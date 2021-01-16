from abc import abstractmethod
from datetime import datetime
from time import perf_counter
from collections import Counter
from typing import Generic, Iterable, Type, Any, Tuple, List, Optional
from rfb_mc.runner import FormulaParams, RunnerBase
from rfb_mc.integrator import IntegratorBase, IntermediateResult, Result
from rfb_mc.scheduler import SchedulerBase
from threading import Thread, Lock
from queue import SimpleQueue, Empty

from rfb_mc.types import RfBmcTask, RfBmcResult


class DirectIntegratorBase(
    Generic[IntermediateResult, Result, FormulaParams],
    IntegratorBase[IntermediateResult, Result]
):
    """
    Class that implements instantiating runners directly.

    Class is abstract since the runner that is used must be specified.
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
    def get_runner_class(cls) -> Type[RunnerBase[FormulaParams, Any, Any]]:
        """
        Returns class used for the runner in worker processes.
        """
        raise NotImplementedError()

    def __init__(self, formula_params: FormulaParams):
        super().__init__(formula_params)

    def run(self, scheduler: SchedulerBase):
        runner = self.get_runner_class()(
            params=scheduler.store.data.params,
            formula_params=self.formula_params,
        )

        algorithm_generator = scheduler.run()
        prev_intermediate_result = None

        s1 = perf_counter()

        syncing_task_results_lock = Lock()
        syncing_task_results: Counter[RfBmcTask] = Counter()
        syncable_task_results: SimpleQueue[Optional[Tuple[RfBmcTask, RfBmcResult]]] = SimpleQueue()

        def run_result_sync_thread():
            nonlocal syncing_task_results

            while True:
                task_results: List[Optional[Tuple[RfBmcTask, RfBmcResult]]] = [syncable_task_results.get()]

                while True:
                    try:
                        task_results.append(syncable_task_results.get_nowait())
                    except Empty:
                        break

                filtered_task_results = [task_result for task_result in task_results if task_result is not None]

                if len(filtered_task_results) > 0:
                    scheduler.store.add_rf_bmc_results(filtered_task_results)

                with syncing_task_results_lock:
                    syncing_task_results -= Counter([
                        task for task, _ in filtered_task_results
                    ])

                # terminate if None is found in Queue
                if None in task_results:
                    break

        result_sync_thread = Thread(target=run_result_sync_thread, daemon=True)
        result_sync_thread.start()

        try:
            # execute tasks until the algorithm stops the iteration thus indicating the final result
            while True:
                # execute an algorithm step
                algorithm_yield = next(algorithm_generator)

                # if the intermediate result has changed, it should be published via a yield
                if algorithm_yield.intermediate_result != prev_intermediate_result:
                    prev_intermediate_result = algorithm_yield.intermediate_result
                    yield prev_intermediate_result

                with syncing_task_results_lock:
                    required_tasks = algorithm_yield.required_tasks - syncing_task_results

                if sum(required_tasks.values()) > 0:
                    task = next(required_tasks.elements())

                    s = perf_counter()
                    result = runner.rf_bmc(task)
                    self._print_debug(f"Ran {task} returning {result} which took {perf_counter() - s:.3f} seconds")

                    with syncing_task_results_lock:
                        syncing_task_results += Counter([(task, result)])

                    syncable_task_results.put((task, result))
        except StopIteration as err:
            d1 = perf_counter() - s1
            self._print_debug(f"Running schedulers tasks until result was available took {d1:.2f} seconds")
            self._print_debug(f"Result: {err.value}")

            # terminates the syncing thread
            syncable_task_results.put(None)
            result_sync_thread.join()

            return err.value
