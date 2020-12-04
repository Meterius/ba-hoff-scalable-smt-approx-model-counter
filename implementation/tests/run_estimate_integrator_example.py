from implementation.estimate_manager import EstimateBaseParams, InMemoryApproxExecutionManager
from implementation.estimate_runner_z3 import EstimateProblemParamsZ3
from implementation.estimate_scheduler \
    import XORConfidentEdgeFinderBinarySearchEstimateScheduler, ConfidentEdgeFinderLinearSearchEstimateScheduler
from implementation.estimate_integrator_z3 import DirectEstimateIntegratorZ3
from time import perf_counter
from z3 import *

if __name__ == "__main__":
    k = 18
    x, y, z = BitVecs("x y z", k)
    f = And([
        URem(x, 4) == 0,
        URem(y, 2481) == 0,
        ULT(z, x + y),
    ])

    manager = InMemoryApproxExecutionManager(
        base_params=EstimateBaseParams(
            a=100,
            q=1,
            km={k: 2},
            max_mc=None,
        ),
    )

    scheduler1 = ConfidentEdgeFinderLinearSearchEstimateScheduler(
        manager=manager,
        confidence=0.75,
    )

    integrator1 = DirectEstimateIntegratorZ3(
        scheduler=scheduler1,
        problem_params=EstimateProblemParamsZ3(
            formula=f,
            variables=[x, y],
        )
    )

    scheduler2 = XORConfidentEdgeFinderBinarySearchEstimateScheduler(
        manager=manager,
        confidence=0.75,
    )

    integrator2 = DirectEstimateIntegratorZ3(
        scheduler=scheduler2,
        problem_params=EstimateProblemParamsZ3(
            formula=f,
            variables=[x, y],
        )
    )

    print("Integrator1 ------------------------")

    s1 = perf_counter()
    integrator1.run()
    d1 = perf_counter() - s1

    print("Integrator2 ------------------------")

    s2 = perf_counter()
    integrator2.run()
    d2 = perf_counter() - s2

    print("------------------------------------")

    print(f"Integrator1 took {d1:.2f} seconds, with result {scheduler1.result()}")
    print(f"Integrator2 took {d2:.2f} seconds, with result {scheduler2.result()}")