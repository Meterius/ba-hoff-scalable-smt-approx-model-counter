from abc import ABC, abstractmethod
from typing import TypeVar, Generic
from hashed_model_counting_framework.types import Params, HBmcTask, HBmcResult

FormulaParams = TypeVar("FormulaParams")


class RunnerBase(ABC, Generic[FormulaParams]):
    def __init__(self, params: Params, formula_params: FormulaParams):
        self.check_params_and_formula_params_compatibility(params, formula_params)

        self.params: Params = params
        self.formula_params: FormulaParams = formula_params

    @classmethod
    @abstractmethod
    def check_params_and_formula_params_compatibility(cls, params: Params, formula_params: FormulaParams):
        """
        Raises an error if the params and formula_params are not compatible.
        """

        raise NotImplementedError()

    @abstractmethod
    def hbmc(self, task: HBmcTask) -> HBmcResult:
        """
        Performs bounded model counting on the formula resulting from
        first replicating the original formula q-times and
        then introducing a hash equation condition.
        """

        raise NotImplementedError()
