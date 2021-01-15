from typing import Generic
from rfb_mc.implementation.direct_integrator import DirectIntegratorBase, IntermediateResult,\
    Result
from rfb_mc.implementation.runner_z3 import RunnerZ3, FormulaParamsZ3


class DirectIntegratorZ3(
    Generic[IntermediateResult, Result],
    DirectIntegratorBase[IntermediateResult, Result, FormulaParamsZ3]
):
    @classmethod
    def get_runner_class(cls):
        return RunnerZ3
