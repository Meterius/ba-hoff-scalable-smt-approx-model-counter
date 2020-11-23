from abc import ABC, abstractmethod
from math import ceil, sqrt, log2, floor
from typing import NamedTuple, Dict, Optional
from dataclasses import dataclass

EstimateTask = NamedTuple("EstimateTask", [("m", int)])
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
        # amount of bits used to encode the formulas variables (1 <= bc)
        ("bc", int),
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
    assert base_params.bc >= 1, "Base parameter bc >= 1"
    assert base_params.max_mc is None or 2**base_params.bc >= base_params.max_mc >= 0, \
        "Base parameter max_mc if specified is <= 2**bc and >= 0"


class EstimateDerivedBaseParams:
    """ Calculates other necessary parameters for estimate that are derived from the base params """

    def __init__(self, base_params: EstimateBaseParams):
        assert_estimate_base_params_is_valid(base_params)

        self.a: int = base_params.a
        self.q: int = base_params.q
        self.bc: int = base_params.bc
        self.n: int = self.bc * self.q

        self.g: float = (sqrt(self.a + 1) - 1) ** 2
        self.G: float = (sqrt(self.a + 1) + 1) ** 2

        self.max_mc: int = base_params.max_mc if base_params.max_mc is not None else 2**self.n

        # self.mp: int = int(floor(self.n - log2(self.G)))
        self.mp: int = int(floor(log2(self.max_mc) - log2(self.G)))

        self.p: int = int(ceil((sqrt(self.a + 1) - 1) ** (2 / self.q)))

    def as_base_params(self) -> EstimateBaseParams:
        return EstimateBaseParams(
            q=self.q,
            a=self.a,
            bc=self.bc,
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
                EstimateTask(m=m): EstimateTaskCombinedResults(
                    positive_voters=0,
                    negative_voters=0,
                ) for m in range(1, derived_params.mp + 1)
            },
        )

    @abstractmethod
    def sync(self):
        pass

    @abstractmethod
    def add_estimate_result_and_sync(self, m: int, positive: bool):
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
