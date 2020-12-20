from abc import ABC, abstractmethod
from math import ceil, sqrt, log2, floor, prod, log
from itertools import chain
from typing import NamedTuple, Dict, Optional, Tuple, Set, Callable, List
from dataclasses import dataclass

from implementation.primes import get_smallest_prime_above_or_equal_power_of_two, get_highest_power_two_key_in_dict

EstimateTask = NamedTuple("EstimateTask", [("c", Tuple[int, ...]), ("a", int)])
""" Parameters for a single estimate call """

EstimateTaskResult = NamedTuple("EstimateTaskResult", [("lmc", Optional[int])])
""" Result of a single estimate call """


EstimateBaseParams = NamedTuple(
    "EstimateBaseParams",
    [
        # clones made of the formula (1 <= q)
        ("q", int),
        # map from bit count to amount of variables that have that bit count
        ("km", Dict[int, int]),
        # if known an upper bound on the model count, if not specified is set to 2**bc,
        # this can be used if the formula is known to have an upper bound on the model count,
        # which will be used to reduce unnecessary operations
        ("max_mc", Optional[int]),
    ],
)
""" Params that are constant across the approx execution """


def assert_estimate_base_params_is_valid(base_params: EstimateBaseParams):
    assert base_params.q >= 1, "Base parameter q >= 1"
    assert all([k >= 1 for k in base_params.km.keys()]) >= 1, "Every key of base parameter km is >= 1 " \
                                                              "(i.e. no bit count is < 1)"
    assert sum(base_params.km.values()) >= 1, "Summed values of base parameter km is >= 1 (i.e. at least " \
                                              "one variable is counted)"
    theoretical_max_mc = prod([(2**k)**kc for k, kc in base_params.km.items()])
    assert base_params.max_mc is None or theoretical_max_mc >= base_params.max_mc >= 0, \
        "Base parameter max_mc if specified is in inclusive interval [0, theoretical maximal model count]"


class EstimateDerivedBaseParams:
    """ Calculates other necessary parameters for estimate that are derived from the base params """

    def __init__(self, base_params: EstimateBaseParams):
        assert_estimate_base_params_is_valid(base_params)

        self.q: int = base_params.q

        self.km: Dict[int, int] = base_params.km
        self.kn: int = sum([k * kc for k, kc in self.km.items()])
        self.n: int = sum(self.km.values())

        theoretical_max_mc = prod([(2**k)**kc for k, kc in base_params.km.items()])
        self.max_mc: int = base_params.max_mc if base_params.max_mc is not None else theoretical_max_mc

        self.cn: int = int(ceil(log2(log2(self.max_mc ** self.q))))

        self.g: Callable[[int], float] = lambda a: (sqrt(a + 1) - 1) ** 2
        self.G: Callable[[int], float] = lambda a: (sqrt(a + 1) + 1) ** 2

        # model count needs to be greater than t,
        # otherwise estimate would always correctly return No
        # (note in the paper CDM-2017 this parameter is called p)
        self.t: Callable[[int], int] = lambda a: int(ceil((sqrt(a + 1) - 1) ** (2 / self.q)))

        self.p: Tuple[int, ...] = tuple([
            get_smallest_prime_above_or_equal_power_of_two(int(ceil(self.kn / (2 ** j)))) for j in range(self.cn + 1)
        ])

    def get_estimate_result_model_count_strict_upper_bound_on_negative_vote(self, task: EstimateTask) -> float:
        """
        Returns the upper bound for the formula model count if an estimate call were
        to return a negative vote and is correct.
        """

        return (self.get_num_cells_of_c(task.c) * self.G(task.a)) ** (1 / self.q)

    def get_estimate_result_model_count_strict_lower_bound_on_positive_vote(self, task: EstimateTask) -> float:
        """
        Returns the lower bound for the formula model count if an estimate call were
        to return a positive vote and is correct.
        """

        return (self.get_num_cells_of_c(task.c) * self.g(task.a)) ** (1 / self.q)

    def get_estimate_result_implication(self, task: EstimateTask, result: EstimateTaskResult) -> Tuple[bool, float]:
        """
        Returns what the result means if the estimate was correct.
        The format is that the model count of the formula is (> if result[0] else <) (result[1]).
        """

        return result.lmc is None, self.get_estimate_result_model_count_strict_lower_bound_on_positive_vote(task) \
            if result.lmc is None else self.get_estimate_result_model_count_strict_upper_bound_on_negative_vote(task)

    def is_possible_c(self, c: Tuple[int, ...], a: int) -> bool:
        """
        Whether the c parameter can be used as an estimate task c parameter.
        It cant be zero, all its elements must be greater or equal 0, it cant be partial and
        if the number of cells determined by the c cannot be large enough
        to be impossible to achieve a negative vote estimate return.
        """

        # all elements in c must be greater or equal zero,
        # and at least one must be greater 0
        if not all([cj >= 0 for cj in c]) or len(c) != self.cn + 1:
            return False

        num_cells = self.get_num_cells_of_c(c)

        return num_cells * self.G(a) < self.max_mc ** self.q

    def assert_is_possible_c(self, c: Tuple[int, ...], a: int):
        """
                Whether the c parameter can be used as an estimate task c parameter.
                It cant be zero, all its elements must be greater or equal 0, it cant be partial and
                if the number of cells determined by the c cannot be large enough
                to be impossible to achieve a negative vote estimate return.
                """

        assert len(c) == self.cn + 1, "c has length of cn + 1"
        assert all([cj >= 0 for cj in c]), "all elements in c are >= 0"
        assert any([cj > 0 for cj in c]), "some element in c is > 0"

        num_cells = self.get_num_cells_of_c(c)
        assert num_cells * self.G(a) < (self.max_mc ** self.q), "number of cells of c * G < (max_mc ** q), as otherwise " \
                                                             "estimate would need to always return a negative vote"

    def get_num_cells_of_c(self, partial_c: Tuple[int, ...]) -> int:
        """
        Returns the number of outputs i.e. the cardinality of the range of a hash chosen from the
        hash family with this c parameter.
        """

        return prod([self.p[j] ** partial_c[j] for j in range(len(partial_c))])

    def get_max_cj_of_possible_c(self, partial_c: Tuple[int, ...], a: int, j: int) -> int:
        """
        Returns the maximum value c[j] could have if it were replaced or set in the partial_c.
        """

        num_cells = self.get_num_cells_of_c(tuple([
            partial_c[i] if i != j else 0 for i in range(len(partial_c))
        ]))
        return max(0, int(floor(log((self.max_mc ** self.q) / (num_cells * self.G(a)), self.p[j]))))

    def get_possible_c(self, a: int):
        """
        Returns all possible c parameters i.e. all c that would return True for is_possible_c(c).
        """

        def get_possible_c_ref(partial_c: Tuple[int, ...]) -> Set[Tuple[int, ...]]:
            if len(partial_c) == self.cn + 1:
                # ensure the c is not zero
                return {partial_c} if any([cj > 0 for cj in partial_c]) else set()

            j = len(partial_c)
            cj_max = self.get_max_cj_of_possible_c(partial_c, a, j)

            return set(chain.from_iterable([
                get_possible_c_ref(partial_c + (cj,)) for cj in range(cj_max + 1)
            ]))

        return get_possible_c_ref(tuple())

    def as_base_params(self) -> EstimateBaseParams:
        return EstimateBaseParams(
            q=self.q,
            km=self.km,
            max_mc=self.max_mc,
        )


ApproxExecution = NamedTuple("ApproxExecution", [
    ("estimate_base_params", EstimateBaseParams),
    ("estimate_tasks_results", Dict[EstimateTask, List[EstimateTaskResult]]),
])
"""
An approx execution is the result data of estimate calls to a specific problem with base params i.e.
across the approx execution the base params and the problem params stay constant that are supplied to the
estimate runners. It can be discarded after the approx information has been retrieved or stored for further reference
and iteratively improving the approx information     
"""


class ApproxExecutionAnalyser:
    def __init__(self, execution: ApproxExecution):
        self.execution: ApproxExecution = execution


class BaseApproxExecutionManager(ABC):
    """
    An execution manager stores the approx execution data in memory and expects that implementations of the
    class implement their own proper execution data location which can be in memory, as a file or in a database, etc.
    With the manager scheduler and integrators can communicate with multiple instances on multiple computing nodes
    to work together towards the common schedulers goal.
    """

    def __init__(self, base_params: EstimateBaseParams):
        assert_estimate_base_params_is_valid(base_params)

        self.execution: ApproxExecution = ApproxExecution(
            estimate_base_params=base_params,
            estimate_tasks_results={},
        )

        self.analyser = ApproxExecutionAnalyser(self.execution)

    @abstractmethod
    def sync(self):
        pass

    @abstractmethod
    def add_estimate_result_and_sync(self, task: EstimateTask, result: EstimateTaskResult):
        pass


class InMemoryApproxExecutionManager(BaseApproxExecutionManager):
    """
    Stores the execution only in the class itself i.e. in memory.
    """

    def sync(self):
        pass

    def add_estimate_result_and_sync(self, task: EstimateTask, result: EstimateTaskResult):
        if task not in self.execution.estimate_tasks_results:
            self.execution.estimate_tasks_results[task] = []

        self.execution.estimate_tasks_results[task].append(result)
