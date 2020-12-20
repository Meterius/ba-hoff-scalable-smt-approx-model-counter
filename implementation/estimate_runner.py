from abc import abstractmethod, ABC
from implementation.estimate_manager import EstimateDerivedBaseParams, EstimateBaseParams,\
    EstimateTaskResult, EstimateTask
from typing import Optional, TypeVar, Generic


PP = TypeVar("PP")


class BaseEstimateRunner(ABC, Generic[PP]):
    def __init__(
        self,
        base_params: EstimateBaseParams,
        problem_params: PP,
    ):
        self.params: EstimateDerivedBaseParams = EstimateDerivedBaseParams(base_params)
        self.problem_params = problem_params

    @classmethod
    def assert_base_params_and_problem_params_compatible(cls, base_params: EstimateBaseParams, problem_params: PP):
        raise NotImplementedError

    @abstractmethod
    def exact_model_count_if_less_or_equal_t(self, a: int) -> Optional[int]:
        """
        If the formula has <= t models this will return the exact model count,
        otherwise it returns None.
        """

        raise NotImplementedError

    @abstractmethod
    def estimate(self, task: EstimateTask) -> EstimateTaskResult:
        """
        Performs estimate from smt paper for the parameter m.
        Note: requires runner to be initialized
        :param task:
        """

        raise NotImplementedError
