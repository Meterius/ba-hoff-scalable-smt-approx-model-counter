from estimate_manager import EstimateBaseParams
from estimate_scheduler import BaseEstimateScheduler
from estimate_runner import EstimateRunner, EstimateProblemParams, \
    SerializedEstimateProblemParams, deserialize_estimate_problem_params, serialize_estimate_problem_params
from datetime import datetime
from time import perf_counter
from multiprocessing import Process, SimpleQueue, Lock
from typing import Dict, Iterable, Optional


# Estimate integrator construct the estimate runners and forward
# the work orders of the scheduler to them. Where the runners actually
# perform their actions is not specified.


class DirectProcessingEstimateIntegrator:
    PRINT_DEBUG = True

    @staticmethod
    def _print_debug(*messages: Iterable[str]):
        if DirectProcessingEstimateIntegrator.PRINT_DEBUG:
            for message in messages:
                print(f"[{datetime.now().strftime('%H:%M:%S:%f')}] {message}")

    def __init__(self, problem_params: EstimateProblemParams, scheduler: BaseEstimateScheduler):
        self.problem_params = problem_params
        self.scheduler = scheduler

    def run(self):
        """
        Works on the available tasks from the scheduler until none remain.
        """

        self._print_debug("Starting integrator run")

        runner = EstimateRunner(
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


class MultiProcessingEstimateIntegrator:
    PRINT_DEBUG = True

    @staticmethod
    def _print_debug(lock: Optional[Lock], title: str, *messages: Iterable[str]):
        if MultiProcessingEstimateIntegrator.PRINT_DEBUG:
            with lock:
                for message in messages:
                    print(f"[{datetime.now().strftime('%H:%M:%S:%f')}] ({title}): {message}")

    @staticmethod
    def _run_worker(
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
            MultiProcessingEstimateIntegrator._print_debug(
                stdio_lock,
                f"Worker[{worker_number}/{worker_count}]",
                *messages,
            )

        runner = EstimateRunner(
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
        self.scheduler = scheduler
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
                }
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
                self.stdio_lock,
                "Integrator",
                *messages,
            )

        print_debug("Starting integrator run")

        tasks_in_progress: Dict[int, int] = {}
        tasks = self.scheduler.available_estimate_tasks()[:self.worker_count]

        for task in tasks:
            tasks_in_progress[task] = tasks_in_progress.get(task, 0) + 1
            self.task_queue.put(task)

        while any(map(lambda x: x > 0, tasks_in_progress.values())):
            task, result = self.result_queue.get()

            self.scheduler.manager.add_estimate_result_and_sync(task, result)

            tasks_in_progress[task] = tasks_in_progress.get(task, 0) - 1

            tasks = self.scheduler.available_estimate_tasks(
                tasks_in_progress,
            )[:self.worker_count-sum(tasks_in_progress.values())]

            for task in tasks:
                tasks_in_progress[task] = tasks_in_progress.get(task, 0) + 1
                self.task_queue.put(task)

    def terminate(self):
        for process in self.processes:
            process.terminate()
