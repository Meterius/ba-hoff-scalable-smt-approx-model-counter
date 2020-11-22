from abc import ABC, abstractmethod
from math import ceil, sqrt, log2, floor
from typing import NamedTuple, Dict
from dataclasses import dataclass

ApproxParams = NamedTuple(
    "ApproxParams",
    [("a", int), ("q", int), ("bit_count", int)],
)


@dataclass
class EstimateData:
    positive_voters: int
    negative_voters: int


ApproxExecutionData = NamedTuple("ApproxExecutionData", [
    ("approx_params", ApproxParams),
    ("estimate_data_map", Dict[int, EstimateData]),
])


class ApproxDerivedParams:
    approx_params: ApproxParams

    def __init__(self, approx_params: ApproxParams):
        self.approx_params = approx_params

        self.a = approx_params.a
        self.q = approx_params.q
        self.n = approx_params.bit_count * approx_params.q

        self.g = (sqrt(self.a + 1) - 1) ** 2
        self.G = (sqrt(self.a + 1) + 1) ** 2

        self.mp = int(floor(self.n - log2(self.G)))

        self.p = int(ceil((sqrt(self.a + 1) - 1) ** (2 / self.q)))


class BaseApproxExecutionManager(ABC):
    params: ApproxDerivedParams

    data: ApproxExecutionData

    def __init__(self, approx_params: ApproxParams):
        self.params = ApproxDerivedParams(approx_params)

        self.data = ApproxExecutionData(
            approx_params=approx_params,
            estimate_data_map={
                m: EstimateData(
                    positive_voters=0,
                    negative_voters=0,
                ) for m in range(1, self.params.mp + 1)
            },
        )

    @abstractmethod
    def sync(self):
        pass

    @abstractmethod
    def add_estimate_result_and_sync(self, m: int, positive: bool):
        pass


class InMemoryApproxExecutionManager(BaseApproxExecutionManager):
    def sync(self):
        pass

    def add_estimate_result_and_sync(self, m: int, positive: bool):
        if positive:
            self.data.estimate_data_map[m].positive_voters += 1
        else:
            self.data.estimate_data_map[m].negative_voters += 1
