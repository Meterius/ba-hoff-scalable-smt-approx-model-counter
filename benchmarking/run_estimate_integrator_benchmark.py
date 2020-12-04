from time import perf_counter

from implementation.estimate_manager import InMemoryApproxExecutionManager, EstimateBaseParams
from implementation.estimate_scheduler import XORConfidentEdgeFinderBinarySearchEstimateScheduler, ConfidentEdgeFinderLinearSearchEstimateScheduler
from implementation.estimate_integrator_z3 import DirectEstimateIntegratorZ3
from benchmarking.convert_benchmark_z3 import get_benchmark_problem

if __name__ == "__main__":
    problem = get_benchmark_problem("1159708")

    manager = InMemoryApproxExecutionManager(
        base_params=EstimateBaseParams(
            a=100,
            q=1,
            k=max([x.size() for x in problem.variables]),
            n=len(problem.variables),
            max_mc=None,
        )
    )

    scheduler = ConfidentEdgeFinderLinearSearchEstimateScheduler(
        manager=manager,
        confidence=0.8,
    )

    integrator = DirectEstimateIntegratorZ3(
        scheduler=scheduler,
        problem_params=problem,
    )

    print("Starting Integrator Run")
    s = perf_counter()

    integrator.run()

    d = perf_counter() - s

    print(f"Scheduler Result is {scheduler.result()}")
    print(f"Took {d:.2f} seconds")
