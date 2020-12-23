from abc import ABC, abstractmethod
from datetime import datetime
from multiprocessing import Lock
from multiprocessing.context import Process
from queue import SimpleQueue
from time import perf_counter
from typing import Generic, Iterable, Type, TypeVar, Counter
from hashed_model_counting_framework.runner import FormulaParams, RunnerBase
from hashed_model_counting_framework.integrator import IntegratorBase, IntermediateResult, Result
from hashed_model_counting_framework.scheduler import SchedulerBase
from hashed_model_counting_framework.types import Params, HBmcTask

SerializedFormulaParams = TypeVar("SerializedFormulaParams")


class MultiProcessingIntegratorBase(
    ABC,
    Generic[IntermediateResult, Result, FormulaParams, SerializedFormulaParams],
    IntegratorBase[IntermediateResult, Result]
):
    """
    Class that implements instantiating runners in processes thus enabling parallel
    execution of scheduler tasks.

    Class is abstract since the runner that is used must be specified and how the formula params
    are serialized to enable them being transferred using the python multiprocessing process arguments.
    """

    PRINT_DEBUG: bool = True

    @classmethod
    def _print_debug(cls, *messages: Iterable[str]):
        """ Timestamped version of print that only prints if PRINT_DEBUG is True """
        if cls.PRINT_DEBUG:
            for message in messages:
                print(f"[{datetime.now().strftime('%H:%M:%S:%f')}] {message}")

    @classmethod
    @abstractmethod
    def get_runner_class(cls) -> Type[RunnerBase[FormulaParams]]:
        """
        Returns class used for the runner in worker processes.
        """
        raise NotImplementedError()

    @classmethod
    @abstractmethod
    def serialize_formula_params(cls, formula_params: FormulaParams) -> SerializedFormulaParams:
        """
        Returns a serialized version of the formula params that can be transferred
        via multiprocessing process arguments.
        """
        raise NotImplementedError()

    @classmethod
    @abstractmethod
    def deserialize_formula_params(cls, serialized_formula_params: SerializedFormulaParams) -> FormulaParams:
        """
        Returns formula params from the serialized formula params.
        """
        raise NotImplementedError()

    @classmethod
    def _run_worker(
        cls,
        worker_idx: int,
        worker_count: int,
        stdio_lock: Lock,
        task_queue: SimpleQueue,
        result_queue: SimpleQueue,
        params: Params,
        serialized_formula_params: FormulaParams,
    ):
        worker_number = worker_idx + 1

        def debug_print(*messages: Iterable[str]):
            if cls.PRINT_DEBUG and stdio_lock is not None:
                with stdio_lock:
                    cls._print_debug(
                        *[f"Worker[{worker_number}/{worker_count}]: {message}" for message in messages],
                    )

        runner = cls.get_runner_class()(
            params=params,
            formula_params=cls.deserialize_formula_params(serialized_formula_params),
        )

        debug_print("Initialized")

        task = task_queue.get()

        while task is not None:
            s = perf_counter()
            result = runner.hbmc(task)
            result_queue.put((task, result))
            debug_print(f"Ran estimate for {task} which took {perf_counter() - s:.3f} seconds")

            task = task_queue.get()

    def __init__(self, formula_params: FormulaParams, worker_count: int):
        super().__init__(formula_params)
        self.worker_count = worker_count

    def run(self, scheduler: SchedulerBase):
        def print_debug(*messages: Iterable[str]):
            self._print_debug(
                *[f"Integrator: {message}" for message in messages]
            )

        print_debug("Starting integrator run")

        s0 = perf_counter()

        task_queue = SimpleQueue()
        result_queue = SimpleQueue()
        stdio_lock = Lock()

        processes = [
            Process(
                target=self._run_worker,
                kwargs={
                    "worker_idx": worker_idx,
                    "worker_count": self.worker_count,
                    "stdio_lock": stdio_lock,
                    "task_queue": task_queue,
                    "result_queue": result_queue,
                    "params": self.scheduler.manager.execution.estimate_base_params,
                    "serialized_formula_params": self.serialize_formula_params(self.formula_params),
                },
                daemon=True,
            ) for worker_idx in range(self.worker_count)
        ]

        for process in processes:
            process.start()

        d0 = perf_counter() - s0
        print_debug(f"Initializing processes took {d0:.2f} seconds")

        s1 = perf_counter()

        try:
            tasks_in_progress: Counter[HBmcTask] = Counter[HBmcTask]()

            algorithm_generator = scheduler.run()
            prev_intermediate_result = None

            try:
                # execute tasks until the algorithm stops the iteration thus indicating the final result
                while True:
                    # execute an algorithm step
                    algorithm_yield = next(algorithm_generator)

                    # if the intermediate result has changed, it should be published via a yield
                    if algorithm_yield.intermediate_result != prev_intermediate_result:
                        prev_intermediate_result = algorithm_yield.intermediate_result

                        print_debug(f"Intermediate Result: {prev_intermediate_result}")

                        yield prev_intermediate_result

                    # determine how many tasks should be queued, by first considering what tasks
                    # are not yet in progress and how many idle workers exist
                    required_tasks = algorithm_yield.required_tasks - tasks_in_progress
                    idle_workers = sum(tasks_in_progress.values()) - self.worker_count
                    tasks_to_queue = min(sum(required_tasks.values()), idle_workers)

                    # queue as many tasks as are available and can be directly forwarded to an idle worker
                    if tasks_to_queue > 0:
                        for _ in range(tasks_to_queue):
                            task = [task for task, count in required_tasks if count > 0]

                            required_tasks -= [task]
                            tasks_in_progress += [task]
                            task_queue.put(task)

                    # if tasks are in progress we wait until a result is available, since either all workers are
                    # processing or no more tasks are available until existing tasks have been finished
                    if sum(tasks_in_progress.values()) > 0:
                        # waits for at least one result and if multiple are available, retrieves all
                        task_results = []
                        task_result = result_queue.get()
                        while task_result is not None:
                            task_results.append(task_result)
                            task_result = result_queue.get_nowait()

                        # add all results to the store
                        # TODO: handle adding the results blocking the integrator from scheduling more tasks
                        scheduler.store.add_hbmc_results(task_results)
            except StopIteration as err:
                d1 = s1 - perf_counter()
                print_debug(f"Running schedulers tasks until result was available took {d1:.2f} seconds")
                print_debug(f"Result: {err.value}")

                return err.value
        finally:
            for process in processes:
                process.terminate()
