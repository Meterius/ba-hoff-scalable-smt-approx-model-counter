from typing import Type
from implementation.estimate_integrator import BaseDirectEstimateIntegrator, BaseMultiProcessingEstimateIntegrator
from implementation.estimate_runner_z3 import EstimateRunnerZ3, EstimateProblemParamsZ3, \
    SerializedEstimateProblemParamsZ3, serialize_estimate_problem_params_z3, deserialize_estimate_problem_params_z3


class DirectEstimateIntegratorZ3(BaseDirectEstimateIntegrator[EstimateProblemParamsZ3]):
    @classmethod
    def get_runner_class(cls) -> Type[EstimateRunnerZ3]:
        return EstimateRunnerZ3


class MultiProcessingEstimateIntegratorZ3(
    BaseMultiProcessingEstimateIntegrator[EstimateProblemParamsZ3, SerializedEstimateProblemParamsZ3]
):
    @classmethod
    def get_runner_class(cls) -> Type[EstimateRunnerZ3]:
        return EstimateRunnerZ3

    @classmethod
    def serialize_problem_params(cls, problem_params: EstimateProblemParamsZ3) -> SerializedEstimateProblemParamsZ3:
        return serialize_estimate_problem_params_z3(problem_params)

    @classmethod
    def deserialize_problem_params(
        cls, serialized_problem_params: SerializedEstimateProblemParamsZ3,
    ) -> EstimateProblemParamsZ3:
        return deserialize_estimate_problem_params_z3(serialized_problem_params)
