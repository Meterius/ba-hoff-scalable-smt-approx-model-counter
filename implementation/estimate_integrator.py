from estimate_manager import EstimateBaseParams
from estimate_scheduler import BaseEstimateScheduler
from estimate_runner import EstimateTask, OptimizedEstimateRunner, EstimateRunner, EstimateProblemParams, \
    SerializedEstimateProblemParams, deserialize_estimate_problem_params, serialize_estimate_problem_params
from datetime import datetime
from time import perf_counter
from abc import ABC, abstractmethod
from multiprocessing import Process, SimpleQueue, Lock
from typing import Dict, Iterable, Optional, Type


# Estimate integrator construct the estimate runners and forward
# the work orders of the scheduler to them. Where the runners actually
# perform their actions is not specified.

class BaseEstimateIntegrator(ABC):
    PRINT_DEBUG: bool = True
    """ Whether the print debug should print its output to the console """

    RUNNER_CLASS: Type[EstimateRunner] = OptimizedEstimateRunner
    """ An estimate runner class used for executing estimate tasks """

    def __init__(self, problem_params: EstimateProblemParams, scheduler: BaseEstimateScheduler):
        self.problem_params: EstimateProblemParams = problem_params
        self.scheduler: BaseEstimateScheduler = scheduler

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


class DirectProcessingEstimateIntegrator(BaseEstimateIntegrator):
    def run(self):
        self._print_debug("Starting integrator run")

        runner = self.RUNNER_CLASS(
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


class MultiProcessingEstimateIntegrator(BaseEstimateIntegrator):
    RUNNER_CLASS = EstimateRunner

    @classmethod
    def _run_worker(
        cls,
        worker_idx: int,
        worker_count: int,
        stdio_lock: Lock,
        task_queue: SimpleQueue,
        result_queue: SimpleQueue,
        base_params: EstimateBaseParams,
        serialized_problem_params: SerializedEstimateProblemParams,
    ):
        worker_number = worker_idx + 1

        def debug_print(*messages: Iterable[str]):
            if cls.PRINT_DEBUG:
                with stdio_lock:
                    cls._print_debug(
                        *[f"Worker[{worker_number}/{worker_count}]: {message}" for message in messages],
                    )

        runner = cls.RUNNER_CLASS(
            base_params=base_params,
            problem_params=deserialize_estimate_problem_params(serialized_problem_params),
        )

        debug_print("Initialized")

        task = task_queue.get()

        while task is not None:
            s = perf_counter()
            result = runner.estimate(task)
            result_queue.put((task, result))
            debug_print(f"Ran estimate for {task} which took {perf_counter()-s:.3f} seconds")

            task = task_queue.get()

    def __init__(self, problem_params: EstimateProblemParams, scheduler: BaseEstimateScheduler, worker_count: int):
        super().__init__(problem_params, scheduler)

        self.task_queue = SimpleQueue()
        self.result_queue = SimpleQueue()
        self.stdio_lock = Lock()

        self.worker_count = worker_count

        self.processes = [
            Process(
                target=MultiProcessingEstimateIntegrator._run_worker,
                kwargs={
                    "worker_idx": worker_idx,
                    "worker_count": worker_count,
                    "stdio_lock": self.stdio_lock,
                    "task_queue": self.task_queue,
                    "result_queue": self.result_queue,
                    "base_params": scheduler.manager.execution.estimate_base_params,
                    "serialized_problem_params": serialize_estimate_problem_params(problem_params),
                },
                daemon=True,
            ) for worker_idx in range(worker_count)
        ]

        for process in self.processes:
            process.start()

    def run(self):
        """
        Works on the available tasks from the scheduler until none remain.
        """

        def print_debug(*messages: Iterable[str]):
            MultiProcessingEstimateIntegrator._print_debug(
                *[f"Integrator: {message}" for message in messages]
            )

        print_debug("Starting integrator run")

        s = perf_counter()

        completed_task_count = 0
        tasks_in_progress: Dict[EstimateTask, int] = {}
        tasks = self.scheduler.available_estimate_tasks()[:self.worker_count]

        for task in tasks:
            tasks_in_progress[task] = tasks_in_progress.get(task, 0) + 1
            self.task_queue.put(task)

        while any(map(lambda x: x > 0, tasks_in_progress.values())):
            task, result = self.result_queue.get()

            completed_task_count += 1

            self.scheduler.manager.add_estimate_result_and_sync(task, result)

            tasks_in_progress[task] = tasks_in_progress.get(task, 0) - 1

            tasks = self.scheduler.available_estimate_tasks(
                tasks_in_progress,
            )[:self.worker_count-sum(tasks_in_progress.values())]

            for task in tasks:
                tasks_in_progress[task] = tasks_in_progress.get(task, 0) + 1
                self.task_queue.put(task)

        print(f"Completed {completed_task_count} tasks in {perf_counter()-s:.3f} seconds")

