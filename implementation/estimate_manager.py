from abc import ABC, abstractmethod
from math import ceil, sqrt, log2, floor, prod, log
from itertools import chain
from typing import NamedTuple, Dict, Optional, Tuple, Set
from dataclasses import dataclass

from implementation.primes import get_smallest_prime_above_or_equal_power_of_two

EstimateTask = NamedTuple("EstimateTask", [("c", Tuple[int, ...])])
""" Parameters for a single estimate call """

EstimateTaskResult = NamedTuple("EstimateTaskResult", [("positive_vote", bool)])
""" Result of a single estimate call """


@dataclass
class EstimateTaskCombinedResults:
    """ Combined results from multiple estimate calls with the same task """
    positive_voters: int
    negative_voters: int


EstimateBaseParams = NamedTuple(
    "EstimateBaseParams",
    [
        # queries made to smt solver in each estimate call (1 <= a)
        ("a", int),
        # clones made of the formula (1 <= q)
        ("q", int),
        # amount of bits per variable
        ("k", int),
        # amount of variables that are counted with
        ("n", int),
        # if known an upper bound on the model count, if not specified is set to 2**bc,
        # this can be used if the formula is known to have an upper bound on the model count,
        # which will be used to reduce unnecessary operations
        ("max_mc", Optional[int]),
    ],
)
""" Params that are constant across the approx execution """


def assert_estimate_base_params_is_valid(base_params: EstimateBaseParams):
    assert base_params.a >= 1, "Base parameter a >= 1"
    assert base_params.q >= 1, "Base parameter q >= 1"
    assert base_params.k >= 1, "Base parameter k >= 1"
    assert base_params.n >= 1, "Base parameter n >= 1"
    assert base_params.max_mc is None or 2**(base_params.n * base_params.k) >= base_params.max_mc >= 0, \
        "Base parameter max_mc if specified is <= 2**(n*k) and >= 0"

    # note that constraint can be lifted once the implementation properly supports it
    assert log2(base_params.k).is_integer(), "Base parameter k is power of 2"


class EstimateDerivedBaseParams:
    """ Calculates other necessary parameters for estimate that are derived from the base params """

    def __init__(self, base_params: EstimateBaseParams):
        assert_estimate_base_params_is_valid(base_params)

        self.a: int = base_params.a
        self.q: int = base_params.q

        self.n: int = base_params.n
        self.k: int = base_params.k

        self.cn: int = int(floor(log2(self.k)))

        self.g: float = (sqrt(self.a + 1) - 1) ** 2
        self.G: float = (sqrt(self.a + 1) + 1) ** 2

        self.max_mc: int = base_params.max_mc if base_params.max_mc is not None else 2**(self.k * self.n)

        # model count needs to be greater than t,
        # otherwise estimate would always correctly return No
        # (note in the paper CDM-2017 this parameter is called p)
        self.t: int = int(ceil((sqrt(self.a + 1) - 1) ** (2 / self.q)))

        self.p: Tuple[int, ...] = tuple([
            get_smallest_prime_above_or_equal_power_of_two(self.k/(2**j)) for j in range(self.cn + 1)
        ])

    def get_estimate_result_implication(self, task: EstimateTask, result: EstimateTaskResult) -> Tuple[bool, float]:
        """
        Returns what the result means if the estimate was correct.
        The format is that the model count of the formula is (> if result[0] else <) (result[1]).
        """
        return result.positive_vote,\
               (self.get_num_cells_of_c(task.c) * (self.g if result.positive_vote else self.G)) ** (1 / self.q)

    def is_possible_c(self, c: Tuple[int, ...]) -> bool:
        """
        Whether the c parameter can be used as an estimate task c parameter.
        It cant be zero, all its elements must be greater or equal 0, it cant be partial and
        if the number of cells determined by the c cannot be large enough
        to be impossible to achieve a negative vote estimate return.
        """

        # all elements in c must be greater or equal zero,
        # and at least one must be greater 0
        if not all([cj >= 0 for cj in c]) or all([cj == 0 for cj in c]) or len(c) != self.cn + 1:
            return False

        num_cells = self.get_num_cells_of_c(c)

        return num_cells * self.G < self.max_mc

    def get_num_cells_of_c(self, partial_c: Tuple[int, ...]) -> int:
        """
        Returns the number of outputs i.e. the cardinality of the range of a hash chosen from the
        hash family with this c parameter.
        """

        return prod([self.p[j] ** partial_c[j] for j in range(len(partial_c))])

    def get_max_cj_of_possible_c(self, partial_c: Tuple[int, ...], j: int) -> int:
        """
        Returns the maximum value c[j] could have if it were replaced or set in the partial_c.
        """

        num_cells = self.get_num_cells_of_c(tuple([
            partial_c[i] if i != j else 0 for i in range(len(partial_c))
        ]))
        return int(floor(log(self.max_mc / (num_cells * self.G), self.p[j])))

    def get_possible_c(self):
        """
        Returns all possible c parameters i.e. all c that would return True for is_possible_c(c).
        """

        def get_possible_c_ref(partial_c: Tuple[int, ...]) -> Set[Tuple[int, ...]]:
            if len(partial_c) == self.cn + 1:
                # ensure the c is not zero
                return {partial_c} if any([cj > 0 for cj in partial_c]) else set()

            j = len(partial_c)
            cj_max = self.get_max_cj_of_possible_c(partial_c, j)

            return set(chain.from_iterable([
                get_possible_c_ref(partial_c + (cj,)) for cj in range(cj_max + 1)
            ]))

        return get_possible_c_ref(tuple())

    def as_base_params(self) -> EstimateBaseParams:
        return EstimateBaseParams(
            q=self.q,
            a=self.a,
            k=self.k,
            n=self.n,
            max_mc=self.max_mc,
        )


ApproxExecution = NamedTuple("ApproxExecution", [
    ("estimate_base_params", EstimateBaseParams),
    ("estimate_tasks_combined_results", Dict[EstimateTask, EstimateTaskCombinedResults]),
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
        # assert_estimate_base_params_is_valid(base_params) is not needed as it is performed in the derived params init
        derived_params = EstimateDerivedBaseParams(base_params)

        self.execution: ApproxExecution = ApproxExecution(
            estimate_base_params=base_params,
            estimate_tasks_combined_results={
                EstimateTask(c=c): EstimateTaskCombinedResults(
                    positive_voters=0,
                    negative_voters=0,
                ) for c in derived_params.get_possible_c()
            },
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
        if result.positive_vote:
            self.execution.estimate_tasks_combined_results[task].positive_voters += 1
        else:
            self.execution.estimate_tasks_combined_results[task].negative_voters += 1
