from typing import Type
from implementation.estimate_integrator import BaseDirectEstimateIntegrator, BaseMultiProcessingEstimateIntegrator
from implementation.estimate_runner_pysmt import EstimateRunnerPYSMT, EstimateProblemParamsPYSMT, \
    SerializedEstimateProblemParamsPYSMT, serialize_estimate_problem_params_pysmt, \
    deserialize_estimate_problem_params_pysmt


class DirectEstimateIntegratorPYSMT(BaseDirectEstimateIntegrator[EstimateProblemParamsPYSMT]):
    @classmethod
    def get_runner_class(cls) -> Type[EstimateRunnerPYSMT]:
        return EstimateRunnerPYSMT


class MultiProcessingEstimateIntegratorPYSMT(
    BaseMultiProcessingEstimateIntegrator[EstimateProblemParamsPYSMT, SerializedEstimateProblemParamsPYSMT]
):
    @classmethod
    def get_runner_class(cls) -> Type[EstimateRunnerPYSMT]:
        return EstimateRunnerPYSMT

    @classmethod
    def serialize_problem_params(
        cls, problem_params: EstimateProblemParamsPYSMT,
    ) -> SerializedEstimateProblemParamsPYSMT:
        return serialize_estimate_problem_params_pysmt(problem_params)

    @classmethod
    def deserialize_problem_params(
        cls, serialized_problem_params: SerializedEstimateProblemParamsPYSMT,
    ) -> EstimateProblemParamsPYSMT:
        return deserialize_estimate_problem_params_pysmt(serialized_problem_params)
