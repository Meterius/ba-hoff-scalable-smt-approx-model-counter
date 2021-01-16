from collections import Counter
from fractions import Fraction
from time import perf_counter
import z3
from alternatives.branching_counter import count_models_by_branching
from rfb_mc.implementation.direct_integrator_z3 import DirectIntegratorZ3
from rfb_mc.implementation.eamp.eamp_edge_scheduler import EampEdgeScheduler
from rfb_mc.implementation.eamp.eamp_rfmi_z3 import EampRfmiZ3
from rfb_mc.implementation.runner_z3 import FormulaParamsZ3, RunnerZ3
from rfb_mc.store import InMemoryStore, StoreData
from rfb_mc.types import Params

RunnerZ3.add_restrictive_formula_module_implementation(EampRfmiZ3)

if __name__ == "__main__":
    k = 14
    x, y, z = z3.BitVecs("x y z", k)
    f = z3.And([
        z3.URem(x, 200) == 0,
        z3.URem(y, 200) == 0,
        z3.ULT(z, x + y),
    ])

    a = 100

    store = InMemoryStore(
        data=StoreData(
            params=Params(
                bit_width_counter=Counter({k: 2}),
            ),
        ),
    )

    scheduler = EampEdgeScheduler(
        store=store,
        confidence=Fraction(0.75),
        a=a,
        q=1,
    )

    integrator = DirectIntegratorZ3(
        formula_params=FormulaParamsZ3(
            formula=f,
            variables=[x, y],
        )
    )

    print("Integrator ------------------------")

    s1 = perf_counter()

    run = integrator.run(scheduler)

    try:
        while True:
            print(f"Intermediate Result: {next(run)}")
    except StopIteration as err:
        print(f"Result: {err.value}")

    d1 = perf_counter() - s1

    print(f"Integrator took {d1:.2f} seconds")

    s2 = perf_counter()
    print("Running branching counter")
    result = count_models_by_branching(f, [x, y])
    print(f"Returned {result} in {perf_counter() - s2:.2f} seconds")
