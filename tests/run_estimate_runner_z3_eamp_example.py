from collections import Counter
from time import perf_counter
from z3 import *
from rfb_mc.implementation.eamp.eamp_rfm import EampParams, EampTransformMethod, EampRfm
from rfb_mc.implementation.eamp.eamp_rfmi_z3 import EampRfmiZ3
from rfb_mc.implementation.runner_z3 import RunnerZ3, FormulaParamsZ3
from rfb_mc.types import Params, RfBmcTask

RunnerZ3.register_restrictive_formula_module_implementation(EampRfmiZ3)

if __name__ == "__main__":
    a = 35
    q = 2
    k = 6
    x, y, z = BitVecs("x y z", k)
    f = And([
        URem(x, 4) == 0,
        URem(y, 5) == 0,
        ULT(z, x + y),
    ])

    s1 = perf_counter()

    params = Params(
        bit_width_counter=Counter({
            k: 2,
        })
    )

    formula_params = FormulaParamsZ3(
        formula=f,
        variables=[x, y],
    )

    runner = RunnerZ3(
        params=params,
        formula_params=formula_params,
    )

    print(f"Initialize took {perf_counter()-s1:.3f} seconds")

    mp = 40

    for m in range(1, mp + 1):
        s = perf_counter()
        eamp_params = EampParams(
            c=(m,),
            transform_method=EampTransformMethod.SORTED_ROLLING_WINDOW,
        )
        task = RfBmcTask(
            rf_module_uid=EampRfm.get_uid(),
            rf_module_param=eamp_params,
            a=a,
            q=q,
        )
        result = runner.rf_bmc(task)
        print(f"Rf Bmc for m={m} took {perf_counter()-s:.3f} seconds with result {result}")

    print(f"Finished, took {perf_counter()-s1:.3f} seconds")
