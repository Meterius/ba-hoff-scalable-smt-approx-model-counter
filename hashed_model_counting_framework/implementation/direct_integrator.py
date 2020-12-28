from abc import ABC, abstractmethod
from datetime import datetime
from time import perf_counter
from typing import Generic, Iterable, Type
from hashed_model_counting_framework.runner import FormulaParams, RunnerBase
from hashed_model_counting_framework.integrator import IntegratorBase, IntermediateResult, Result
from hashed_model_counting_framework.scheduler import SchedulerBase


class DirectIntegratorBase(
    ABC,
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
    def get_runner_class(cls) -> Type[RunnerBase[FormulaParams]]:
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

        try:
            # execute tasks until the algorithm stops the iteration thus indicating the final result
            while True:
                # execute an algorithm step
                algorithm_yield = next(algorithm_generator)

                # if the intermediate result has changed, it should be published via a yield
                if algorithm_yield.intermediate_result != prev_intermediate_result:
                    prev_intermediate_result = algorithm_yield.intermediate_result
                    yield prev_intermediate_result

                if sum(algorithm_yield.required_tasks.values()) > 0:
                    # get a runnable task and run it
                    task = [task for task, count in algorithm_yield.required_tasks.keys() if count > 0][0]

                    s = perf_counter()
                    result = runner.hbmc(task)
                    self.debug_print(f"Ran {task} returning {result} which took {perf_counter() - s:.3f} seconds")

                    # add all result to the store
                    # TODO: handle adding the result blocking the integrator from running more tasks
                    scheduler.store.add_hbmc_results([(task, result)])
        except StopIteration as err:
            d1 = s1 - perf_counter()
            self.print_debug(f"Running schedulers tasks until result was available took {d1:.2f} seconds")
            self.print_debug(f"Result: {err.value}")

            return err.value
