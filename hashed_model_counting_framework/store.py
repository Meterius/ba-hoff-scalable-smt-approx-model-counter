from abc import ABC, abstractmethod
from typing import Dict, Counter, Iterable, Tuple
from dataclasses import dataclass, field
from hashed_model_counting_framework.types import Params, HBmcTask, HBmcResult


@dataclass
class StoreData:
    # general and problem specific parameter for the hash based model counting framework
    params: Params
    # results from hashed bounded model counting calls
    hbmc_results_map: Dict[HBmcTask, Counter[HBmcResult]] = field(default_factory=dict)


class StoreBase(ABC):
    def __init__(self, data: StoreData):
        self.data = data

    @abstractmethod
    def sync(self):
        """
        Synchronizes the memory with the storage location
        used by the store implementation.

        (Possibly causes a blocking operation)
        """

        raise NotImplementedError()

    def add_hbmc_results(self, task_results: Iterable[Tuple[HBmcTask, HBmcResult]]):
        """
        Adds a result of a hbmc call to the data.
        Based on the store implementation this operation should also
        synchronize with the storage location.

        (Possibly causes a blocking operation)
        """

        for task, result in task_results:
            if task not in self.data.hbmc_results_map:
                self.data.hbmc_results_map[task] = Counter[HBmcResult]()

            self.data.hbmc_results_map[task][result] += 1
