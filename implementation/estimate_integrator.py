from estimate_scheduler import BaseEstimateScheduler
from estimate_runner import SerializedApproxPayloadParams, serialize_approx_payload_params, \
    ApproxPayloadParams, EstimateRunner, ApproxParams, deserialize_approx_payload_params
from datetime import datetime
from time import perf_counter
from multiprocessing import Process, SimpleQueue, Lock
from typing import Dict, Iterable, Optional


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
        approx_params: ApproxParams,
        serialized_approx_payload: SerializedApproxPayloadParams,
    ):
        worker_number = worker_idx + 1

        def debug_print(*messages: Iterable[str]):
            MultiProcessingEstimateIntegrator._print_debug(
                stdio_lock,
                f"Worker[{worker_number}/{worker_count}]",
                *messages,
            )

        runner = EstimateRunner(
            approx_params=approx_params,
        )

        runner.initialize(deserialize_approx_payload_params(serialized_approx_payload))

        debug_print("Initialized")

        task = task_queue.get()

        while task is not None:
            s = perf_counter()
            result = runner.estimate(task)
            result_queue.put((task, result))
            debug_print(f"Ran estimate for m={task} which took {perf_counter()-s:.3f} seconds")

            task = task_queue.get()

    def __init__(self, approx_payload_params: ApproxPayloadParams, scheduler: BaseEstimateScheduler, worker_count: int):
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
                    "approx_params": scheduler.manager.params.approx_params,
                    "serialized_approx_payload": serialize_approx_payload_params(approx_payload_params),
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
