from abc import abstractmethod, ABC
from common import BaseApproxExecutionManager
from typing import List, Generic, TypeVar, Tuple, Optional, Union, Dict
from math import floor, log2, log, ceil

R = TypeVar("R")


class BaseEstimateScheduler(ABC, Generic[R]):
    def __init__(self, manager: BaseApproxExecutionManager):
        self.manager = manager

    def available_estimate_tasks(self, tasks_in_progress: Optional[Dict[int, int]] = None) -> List[int]:
        """
        Returns a list of estimate m parameters that need to be executed in
        order to achieve the scheduler goal. If a tasks_in_progress map is supplied
        tasks that are already being worked on will not be included.
        """

        tasks = self._available_estimate_tasks()

        if tasks_in_progress:
            for task in tasks_in_progress:
                try:
                    for _ in range(tasks_in_progress[task]):
                        tasks.remove(task)
                except ValueError:
                    pass

        return tasks

    @abstractmethod
    def _available_estimate_tasks(self) -> List[int]:
        """
        Returns a list of estimate m parameters that need to be executed in
        order to achieve the scheduler goal.
        """
        pass

    @abstractmethod
    def predicted_estimate_tasks(self) -> List[int]:
        """
        Returns a list of estimate m parameters that could possibly be needed to be executed
        after the available work has been finished/continued. If additional computational power is available
        this work might be executed before the current work is finished.
        """
        pass

    @abstractmethod
    def result(self) -> Optional[R]:
        """
        Returns the goal that the scheduler was tasked
        to achieve if it has been achieved and otherwise
        returns None. (For example: an interval with sufficient confidence and preciseness)
        """
        pass


class ConfidentEdgeFinderBinarySearchEstimateScheduler(BaseEstimateScheduler[Tuple[int, int]]):
    """
    This estimate scheduler will find via binary search an estimate m parameter for which the predecessor or successor
    is unequal for the value at m with sufficient confidence. This will yield as the result an interval in which
    the model count is contained that is as precise as the execution will allow and is correct with probability given
    as the confidence parameter.
    """

    def __init__(self, manager: BaseApproxExecutionManager, confidence: float):
        super().__init__(manager)

        assert 0 <= confidence < 1

        self.confidence = confidence

    def _apply_binary_search(self) -> Union[Tuple[int, int], List[int]]:
        left = 1
        right = self.manager.params.mp

        alpha = 1 - self.confidence
        r = int(ceil(8 * log((1 / alpha) * floor(self.manager.params.n - log2(self.manager.params.G)))))

        def estimate(m: int) -> Union[bool, int]:
            nonlocal self

            estimate_data = self.manager.data.estimate_data_map[m]

            rr = max(0, r - estimate_data.positive_voters + estimate_data.negative_voters)

            if estimate_data.positive_voters >= estimate_data.negative_voters and \
               estimate_data.positive_voters >= estimate_data.negative_voters + rr:
                return True

            if estimate_data.negative_voters > estimate_data.positive_voters and \
               estimate_data.negative_voters > estimate_data.positive_voters + rr:
                return False

            return rr

        m = 1
        while left <= right:
            m = floor((left + right) / 2)

            estimate_base = estimate(m)
            if type(estimate_base) == int:
                return [m] * estimate_base

            if m == 1 and not estimate_base:
                comparison = 0
            elif m == self.manager.params.mp:
                comparison = 0 if estimate_base else -1
            elif estimate_base:
                comparison = 1
            else:
                estimate_prev = estimate(m - 1)
                if type(estimate_prev) == int:
                    return [m - 1] * estimate_prev

                comparison = 0 if estimate_prev else -1

            if comparison == -1:
                right = m - 1
            elif comparison == 1:
                left = m + 1
            else:
                break

        return [self.manager.params.p + 1, 2 * self.manager.params.G] \
            if m == 1 else [2 ** (m - 1) * self.manager.params.g, 2 ** m * self.manager.params.G]

    def _available_estimate_tasks(self) -> List[int]:
        res = self._apply_binary_search()
        return [] if type(res) == tuple else res

    def predicted_estimate_tasks(self) -> List[int]:
        return []

    def result(self) -> Optional[Tuple[int, int]]:
        res = self._apply_binary_search()
        return res if type(res) == tuple else None
