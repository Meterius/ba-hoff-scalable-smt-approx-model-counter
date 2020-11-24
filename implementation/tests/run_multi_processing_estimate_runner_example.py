from implementation.estimate_runner import EstimateProblemParams
from implementation.estimate_manager import InMemoryApproxExecutionManager, EstimateBaseParams
from implementation.estimate_integrator import MultiProcessingEstimateIntegrator
from implementation.estimate_scheduler import ConfidentEdgeFinderBinarySearchEstimateScheduler
from time import perf_counter
from z3 import *
from os import cpu_count

if __name__ == "__main__":
    n = 20
    x, y, z = Ints("x y z")
    f = And([
        x >= 0,
        y >= 0,
        x % 4 == 0,
        y % 5 == 0,
        z < x + y,
    ])

    s2 = perf_counter()
    s = perf_counter()

    manager = InMemoryApproxExecutionManager(
        base_params=EstimateBaseParams(
            a=10,
            q=1,
            bc=2 * n,
            max_mc=None,
        ),
    )

    print(f"Initializing InMemoryApproxExecutionManager took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    scheduler = ConfidentEdgeFinderBinarySearchEstimateScheduler(
        manager=manager,
        confidence=0.75,
    )

    print(f"Initializing ConfidentEdgeFinderBinarySearchEstimateScheduler took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    integrator = MultiProcessingEstimateIntegrator(
        problem_params=EstimateProblemParams(
            formula=f,
            variables=[(x, n), (y, n)],
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