from abc import abstractmethod, ABC
from implementation.estimate_manager import BaseApproxExecutionManager, EstimateDerivedBaseParams, EstimateTask
from typing import List, Generic, TypeVar, Tuple, Optional, Union, Dict, NamedTuple
from math import floor, log2, log, ceil

R = TypeVar("R")

EstimateTaskCombinedResults = NamedTuple(
    "EstimateTaskCombinedResults", [("positive_voters", int), ("negative_voters", int)]
)


class BaseEstimateScheduler(ABC, Generic[R]):
    """
    The estimate scheduler specifies available estimate tasks and
    predicted estimate tasks that need to be completed before the goal or
    result the estimate scheduler is supposed to achieve are available.
    Ideally when the available_estimate_tasks are finished the result should
    be available.
    """

    def __init__(self, manager: BaseApproxExecutionManager):
        self.manager = manager

    def _get_estimate_task_combined_results(self, task: EstimateTask) -> EstimateTaskCombinedResults:
        return EstimateTaskCombinedResults(
            positive_voters=len([
                result for result in self.manager.execution.estimate_tasks_results.get(task, [])
                if result.lmc is None
            ]),
            negative_voters=len([
                result for result in self.manager.execution.estimate_tasks_results.get(task, [])
                if result.lmc is not None
            ]),
        )

    def available_estimate_tasks(
        self,
        tasks_in_progress: Optional[Dict[EstimateTask, int]] = None,
    ) -> List[EstimateTask]:
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
    def _available_estimate_tasks(self) -> List[EstimateTask]:
        """
        Returns a list of estimate m parameters that need to be executed in
        order to achieve the scheduler goal.
        """
        pass

    @abstractmethod
    def predicted_estimate_tasks(self) -> List[EstimateTask]:
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


class XORConfidentEdgeFinderLinearEstimateScheduler(BaseEstimateScheduler[Tuple[int, int]]):
    """
    This estimate scheduler will find via binary search an estimate m parameter for which the predecessor or successor
    is unequal for the value at m with sufficient confidence. This will yield as the result an interval in which
    the model count is contained that is as precise as the execution will allow and is correct with probability given
    as the confidence parameter.
    """

    def __init__(self, manager: BaseApproxExecutionManager, a: int, confidence: float):
        super().__init__(manager)

        assert 0 <= confidence < 1, "Confidence is < 1 and >= 0"

        self.a: int = a
        self.confidence: float = confidence
        self.params: EstimateDerivedBaseParams = EstimateDerivedBaseParams(manager.execution.estimate_base_params)

    def _apply_binary_search(self) -> Union[Tuple[float, float], List[EstimateTask]]:
        mp = self.params.get_max_cj_of_possible_c(tuple(), self.params.cn, self.a)

        def task(m: int) -> EstimateTask:
            return EstimateTask(c=(0,) * self.params.cn + (m,), a=self.a)

        alpha = 1 - self.confidence

        # modified to account for reduced amount of steps due to binary search
        r = int(ceil(8 * log((1 / alpha) * ceil(log2(mp)))))

        def estimate(task: EstimateTask) -> Union[bool, int]:
            nonlocal self

            estimate_data = self._get_estimate_task_combined_results(task)

            rr = max(0, r - (estimate_data.positive_voters + estimate_data.negative_voters))

            if estimate_data.positive_voters >= estimate_data.negative_voters and \
               estimate_data.positive_voters >= estimate_data.negative_voters + rr:
                return True

            if estimate_data.negative_voters > estimate_data.positive_voters and \
               estimate_data.negative_voters > estimate_data.positive_voters + rr:
                return False

            return rr

        m = 1
        while True:
            estimate_base = estimate(task(m))
            if type(estimate_base) == int:
                return [task(m)] * estimate_base

            if m == mp:
                break
            elif not estimate_base:
                m -= 1
                break
            else:
                m += 1

        if m == 0:
            # TODO: properly handle case of too little model count
            raise ValueError("less than minimally detectable amount of estimate models")

        print(f"Result: {((self.a * (2 ** ((m + 1) - 0.5))) ** (1 / self.params.q)):.2f}")

        lower_bound = self.params.get_estimate_result_model_count_strict_lower_bound_on_positive_vote(
            EstimateTask(
                c=(0,) * self.params.cn + (m,), a=self.a,
            )
        )

        upper_bound = self.params.get_estimate_result_model_count_strict_upper_bound_on_negative_vote(
            EstimateTask(
                c=(0,) * self.params.cn + (m + 1,), a=self.a,
            )
        ) if m != mp else self.params.max_mc

        return lower_bound, upper_bound

    def _available_estimate_tasks(self) -> List[EstimateTask]:
        res = self._apply_binary_search()
        return [] if type(res) == tuple else res

    def predicted_estimate_tasks(self) -> List[EstimateTask]:
        return []

    def result(self) -> Optional[Tuple[int, int]]:
        res = self._apply_binary_search()
        return res if type(res) == tuple else None


class XORConfidentEdgeFinderBinarySearchEstimateScheduler(BaseEstimateScheduler[Tuple[int, int]]):
    """
    This estimate scheduler will find via binary search an estimate m parameter for which the predecessor or successor
    is unequal for the value at m with sufficient confidence. This will yield as the result an interval in which
    the model count is contained that is as precise as the execution will allow and is correct with probability given
    as the confidence parameter.
    """

    def __init__(self, manager: BaseApproxExecutionManager, a: int, confidence: float):
        super().__init__(manager)

        assert a >= 1, "a >= 1"
        assert 0 <= confidence < 1, "Confidence is < 1 and >= 0"

        self.a: int = a
        self.confidence: float = confidence
        self.params: EstimateDerivedBaseParams = EstimateDerivedBaseParams(manager.execution.estimate_base_params)

    def _apply_binary_search(self) -> Union[Tuple[float, float], List[EstimateTask]]:
        mp = self.params.get_max_cj_of_possible_c(tuple(), self.a, self.params.cn)

        left = 1
        right = mp

        def task(m: int) -> EstimateTask:
            return EstimateTask(c=(0,) * self.params.cn + (m,), a=self.a)

        alpha = 1 - self.confidence

        # modified to account for reduced amount of steps due to binary search
        r = int(ceil(8 * log((1 / alpha) * ceil(log2(mp)))))

        def estimate(task: EstimateTask) -> Union[bool, int]:
            nonlocal self

            estimate_data = self._get_estimate_task_combined_results(task)

            rr = max(0, r - (estimate_data.positive_voters + estimate_data.negative_voters))

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

            estimate_base = estimate(task(m))
            if type(estimate_base) == int:
                return [task(m)] * estimate_base

            if m == 1 and not estimate_base:
                comparison = 0
            elif m == mp:
                comparison = 0 if estimate_base else -1
            elif estimate_base:
                comparison = 1
            else:
                estimate_prev = estimate(task(m=m - 1))
                if type(estimate_prev) == int:
                    return [task(m=m - 1)] * estimate_prev

                comparison = 0 if estimate_prev else -1

            if comparison == -1:
                right = m - 1
            elif comparison == 1:
                left = m + 1
            else:
                break

        if m == 1:
            # TODO: properly handle case of too little model count
            raise ValueError("less than minimally detectable amount of estimate models")

        print(f"Result: {((self.a * (2 ** (m - 0.5))) ** (1 / self.params.q)):.2f}")

        lower_bound = self.params.get_estimate_result_model_count_strict_lower_bound_on_positive_vote(
            EstimateTask(
                c=(0,) * self.params.cn + (m,), a=self.a,
            )
        )

        upper_bound = self.params.get_estimate_result_model_count_strict_upper_bound_on_negative_vote(
            EstimateTask(
                c=(0,) * self.params.cn + (m + 1,), a=self.a,
            )
        ) if m != mp else self.params.max_mc

        return lower_bound, upper_bound

    def _available_estimate_tasks(self) -> List[EstimateTask]:
        res = self._apply_binary_search()
        return [] if type(res) == tuple else res

    def predicted_estimate_tasks(self) -> List[EstimateTask]:
        return []

    def result(self) -> Optional[Tuple[int, int]]:
        res = self._apply_binary_search()
        return res if type(res) == tuple else None


class ConfidentEdgeFinderLinearSearchEstimateScheduler(BaseEstimateScheduler[Tuple[int, int]]):
    def __init__(self, manager: BaseApproxExecutionManager, a: int, confidence: float):
        super().__init__(manager)

        assert a >= 1, "a >= 1"
        assert 0 <= confidence < 1, "Confidence is < 1 and >= 0"

        self.a: int = a
        self.confidence: float = confidence
        self.params: EstimateDerivedBaseParams = EstimateDerivedBaseParams(manager.execution.estimate_base_params)

    def _apply_linear_search(self) -> Union[Tuple[float, float], List[EstimateTask]]:
        alpha = 1 - self.confidence
        r = int(ceil(8 * log2((1 / alpha) * ceil(log2(
            self.params.get_max_cj_of_possible_c(tuple(), self.a, self.params.cn)
        )))))

        def estimate(task: EstimateTask) -> Union[bool, int]:
            nonlocal self

            estimate_data = self._get_estimate_task_combined_results(task)

            rr = max(0, r - (estimate_data.positive_voters + estimate_data.negative_voters))

            if estimate_data.positive_voters >= estimate_data.negative_voters and \
               estimate_data.positive_voters >= estimate_data.negative_voters + rr:
                return True

            if estimate_data.negative_voters > estimate_data.positive_voters and \
               estimate_data.negative_voters > estimate_data.positive_voters + rr:
                return False

            return rr

        partial_c = [0, 1]

        def make_c():
            return tuple(partial_c) + (0,) * (self.params.cn + 1 - len(partial_c))

        while True:
            if not self.params.is_possible_c(make_c(), self.a):
                if len(partial_c) == self.params.cn + 1:
                    partial_c[-1] -= 1
                    break
                else:
                    partial_c[-1] -= 1
                    partial_c.append(1)
                    continue

            j = len(partial_c) - 1

            task = EstimateTask(c=make_c(), a=self.a)
            ret = estimate(task)
            if type(ret) == int:
                return [task] * ret

            if ret:
                if j == self.params.cn:
                    partial_c[j] += 1
                else:
                    partial_c.append(1)
            else:
                if j == self.params.cn:
                    partial_c[j] -= 1

                    if sum(partial_c) == 0:
                        # TODO: properly handle case of too little model count
                        raise ValueError("less than minimally detectable amount of estimate models")
                    else:
                        break
                else:
                    partial_c[j] -= 1
                    partial_c.append(1)

        lower_bound = self.params.get_estimate_result_model_count_strict_lower_bound_on_positive_vote(
            EstimateTask(c=make_c(), a=self.a)
        )

        # test if could have been minimally increased, if it could have been the estimate for it was a negative vote,
        # if it was already maximal the maximal model count must have been smaller than the minimal increase
        partial_c[-1] += 1
        if self.params.is_possible_c(make_c(), self.a):
            upper_bound = self.params.get_estimate_result_model_count_strict_upper_bound_on_negative_vote(
                EstimateTask(c=make_c(), a=self.a)
            )
        else:
            upper_bound = self.params.max_mc

        return lower_bound, upper_bound

    def _available_estimate_tasks(self) -> List[EstimateTask]:
        res = self._apply_linear_search()
        return [] if type(res) == tuple else res

    def predicted_estimate_tasks(self) -> List[EstimateTask]:
        return []

    def result(self) -> Optional[Tuple[int, int]]:
        res = self._apply_linear_search()
        return res if type(res) == tuple else None
