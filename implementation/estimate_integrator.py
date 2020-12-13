from implementation.estimate_manager import EstimateBaseParams
from implementation.estimate_scheduler import BaseEstimateScheduler
from implementation.estimate_runner import EstimateTask, BaseEstimateRunner, PP
from datetime import datetime
from time import perf_counter
from abc import ABC, abstractmethod
from multiprocessing import Process, SimpleQueue, Lock
from typing import Dict, Iterable, Generic, TypeVar, Type


# Estimate integrator construct the estimate runners and forward
# the work orders of the scheduler to them. Where the runners actually
# perform their actions is not specified.

class BaseEstimateIntegrator(ABC, Generic[PP]):
    PRINT_DEBUG: bool = True
    """ Whether the print debug should print its output to the console """

    def __init__(
        self,
        scheduler: BaseEstimateScheduler,
        problem_params: PP,
    ):
        self.scheduler: BaseEstimateScheduler = scheduler
        self.problem_params: PP = problem_params

    @classmethod
    def _print_debug(cls, *messages: Iterable[str]):
        """ Timestamped version of print that only prints if PRINT_DEBUG is True """
        if cls.PRINT_DEBUG:
            for message in messages:
                print(f"[{datetime.now().strftime('%H:%M:%S:%f')}] {message}")

    @abstractmethod
    def run(self):
        """
        Works available and predicted tasks of scheduler until no
        more tasks are available, after which the scheduler is expected
        to be able to return its data.
        """
        raise NotImplementedError


class BaseDirectEstimateIntegrator(Generic[PP], BaseEstimateIntegrator[PP], ABC):
    @classmethod
    @abstractmethod
    def get_runner_class(cls) -> Type[BaseEstimateRunner[PP]]:
        raise NotImplementedError

    def run(self):
        self._print_debug("Starting integrator run")

        runner = self.get_runner_class()(
            base_params=self.scheduler.manager.execution.estimate_base_params,
            problem_params=self.problem_params,
        )

        tasks = self.scheduler.available_estimate_tasks()

        while len(tasks) > 0:
            task = tasks[0]

            s = perf_counter()
            self.scheduler.manager.add_estimate_result_and_sync(task, runner.estimate(task))
            self._print_debug(f"Ran estimate for {task} which took {perf_counter() - s:.3f} seconds")

            tasks = self.scheduler.available_estimate_tasks()


SPP = TypeVar("SPP")


class BaseMultiProcessingEstimateIntegrator(Generic[PP, SPP], BaseEstimateIntegrator[PP], ABC):
    @classmethod
    @abstractmethod
    def get_runner_class(cls) -> Type[BaseEstimateRunner[PP]]:
        raise NotImplementedError

    @classmethod
    @abstractmethod
    def serialize_problem_params(cls, problem_params: PP) -> SPP:
        raise NotImplementedError

    @classmethod
    @abstractmethod
    def deserialize_problem_params(cls, serialized_problem_params: SPP) -> PP:
        raise NotImplementedError

    @classmethod
    def _run_worker(
        cls,
        worker_idx: int,
        worker_count: int,
        stdio_lock: Lock,
        task_queue: SimpleQueue,
        result_queue: SimpleQueue,
        base_params: EstimateBaseParams,
        serialized_problem_params: SPP,
    ):
        worker_number = worker_idx + 1

        def debug_print(*messages: Iterable[str]):
            if cls.PRINT_DEBUG:
                with stdio_lock:
                    cls._print_debug(
                        *[f"Worker[{worker_number}/{worker_count}]: {message}" for message in messages],
                    )

        runner = cls.get_runner_class()(
            base_params=base_params,
            problem_params=cls.deserialize_problem_params(serialized_problem_params),
        )

        debug_print("Initialized")

        task = task_queue.get()

        while task is not None:
            s = perf_counter()
            result = runner.estimate(task)
            result_queue.put((task, result))
            debug_print(f"Ran estimate for {task} which took {perf_counter() - s:.3f} seconds")

            task = task_queue.get()

    def __init__(self, scheduler: BaseEstimateScheduler, problem_params: PP, worker_count: int):
        super().__init__(scheduler, problem_params)
        self.worker_count = worker_count

    def run(self):
        """
        Works on the available tasks from the scheduler until none remain.
        """

        def print_debug(*messages: Iterable[str]):
            self._print_debug(
                *[f"Integrator: {message}" for message in messages]
            )

        print_debug("Starting integrator run")

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
                    "base_params": self.scheduler.manager.execution.estimate_base_params,
                    "serialized_problem_params": self.serialize_problem_params(self.problem_params),
                },
                daemon=True,
            ) for worker_idx in range(self.worker_count)
        ]

        for process in processes:
            process.start()

        try:
            s = perf_counter()

            completed_task_count = 0
            tasks_in_progress: Dict[EstimateTask, int] = {}
            tasks = self.scheduler.available_estimate_tasks()[:self.worker_count]

            for task in tasks:
                tasks_in_progress[task] = tasks_in_progress.get(task, 0) + 1
                task_queue.put(task)

            while any(map(lambda x: x > 0, tasks_in_progress.values())):
                task, result = result_queue.get()

                completed_task_count += 1

                self.scheduler.manager.add_estimate_result_and_sync(task, result)

                tasks_in_progress[task] = tasks_in_progress.get(task, 0) - 1

                tasks = self.scheduler.available_estimate_tasks(
                    tasks_in_progress,
                )[:self.worker_count - sum(tasks_in_progress.values())]

                for task in tasks:
                    tasks_in_progress[task] = tasks_in_progress.get(task, 0) + 1
                    task_queue.put(task)

            print_debug(f"Completed {completed_task_count} tasks in {perf_counter() - s:.3f} seconds")
        finally:
            for process in processes:
                process.terminate()
