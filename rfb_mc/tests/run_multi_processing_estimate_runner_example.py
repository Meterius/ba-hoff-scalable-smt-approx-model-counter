from collections import Counter
from fractions import Fraction
from time import perf_counter
import z3
from os import cpu_count
from rfb_mc.implementation.eamp.eamp_edge_scheduler import EampEdgeScheduler
from rfb_mc.implementation.eamp.eamp_rfmi_z3 import EampRfmiZ3
from rfb_mc.implementation.multi_processing_integrator_z3 import MultiProcessingIntegratorZ3
from rfb_mc.implementation.runner_z3 import RunnerZ3, FormulaParamsZ3
from rfb_mc.store import InMemoryStore, StoreData
from rfb_mc.types import Params

RunnerZ3.register_restrictive_formula_module_implementation(EampRfmiZ3)

if __name__ == "__main__":
    k = 8
    x, y, z = z3.BitVecs("x y z", k)
    f = z3.And([
        z3.UGE(x, 0),
        z3.UGE(y, 0),
        z3.URem(x, 4) == 0,
        z3.URem(y, 5) == 0,
        z3.ULT(z, x + y),
    ])

    s2 = perf_counter()
    s = perf_counter()

    a = 50

    store = InMemoryStore(
        data=StoreData(
            params=Params(
                bit_width_counter=Counter({k: 2})
            )
        )
    )

    print(f"Initializing InMemoryApproxExecutionManager took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    scheduler = EampEdgeScheduler(
        store=store,
        confidence=Fraction(0.75),
        a=a,
        q=2,
    )

    print(f"Initializing ConfidentEdgeFinderBinarySearchEstimateScheduler took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    integrator = MultiProcessingIntegratorZ3(
        formula_params=FormulaParamsZ3(formula=f, variables=[x, y]),
        worker_count=cpu_count(),
    )

    print(f"Initializing MultiProcessingEstimateIntegrator took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    print(f"Initializing took {perf_counter()-s2:.3f} seconds")

    run = integrator.run(scheduler)

    try:
        while True:
            print(f"Intermediate Result: {next(run)}")
    except StopIteration as err:
        print(f"Result: {err.value}")

    print(f"Binary search with multi processing took {perf_counter()-s2:.3f} seconds")
