from alternatives.branching_counter import count_models_by_branching
from implementation.estimate_manager import InMemoryApproxExecutionManager, EstimateBaseParams
from implementation.estimate_runner_z3 import EstimateProblemParamsZ3
from implementation.estimate_integrator_z3 import MultiProcessingEstimateIntegratorZ3
from implementation.estimate_scheduler import XORConfidentEdgeFinderBinarySearchEstimateScheduler
from time import perf_counter
from z3 import *
from os import cpu_count

if __name__ == "__main__":
    k = 8
    x, y, z = BitVecs("x y z", k)
    f = And([
        UGE(x, 0),
        UGE(y, 0),
        URem(x, 4) == 0,
        URem(y, 5) == 0,
        ULT(z, x + y),
    ])

    s2 = perf_counter()
    s = perf_counter()

    manager = InMemoryApproxExecutionManager(
        base_params=EstimateBaseParams(
            a=50,
            q=2,
            k=k,
            n=2,
            max_mc=None,
        ),
    )

    print(f"Initializing InMemoryApproxExecutionManager took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    scheduler = XORConfidentEdgeFinderBinarySearchEstimateScheduler(
        manager=manager,
        confidence=0.75,
    )

    print(f"Initializing ConfidentEdgeFinderBinarySearchEstimateScheduler took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    integrator = MultiProcessingEstimateIntegratorZ3(
        problem_params=EstimateProblemParamsZ3(
            formula=f,
            variables=[x, y],
        ),
        scheduler=scheduler,
        worker_count=cpu_count(),
    )

    print(f"Initializing MultiProcessingEstimateIntegrator took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    print(f"Initializing took {perf_counter()-s2:.3f} seconds")

    integrator.run()

    print(f"Binary search with multi processing took {perf_counter()-s2:.3f} seconds")

    print(scheduler.result())

    print(f"Exact count: {count_models_by_branching(f, [x, y])}")