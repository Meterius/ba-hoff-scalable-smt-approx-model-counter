from typing import Tuple, List
from collections import Counter
from time import perf_counter
from alternatives.branching_counter import count_models_by_branching
from benchmarking.benchmark import get_benchmark_list
from implementation.estimate_manager import InMemoryApproxExecutionManager, EstimateBaseParams
from implementation.estimate_scheduler import ConfidentEdgeFinderLinearSearchEstimateScheduler
from implementation.estimate_integrator_z3 import MultiProcessingEstimateIntegratorZ3, DirectEstimateIntegratorZ3
from benchmarking.convert_benchmark_z3 import get_benchmark_problem
import os


def run_benchmark(benchmark: str) -> Tuple[float, Tuple[float, float]]:
    problem = get_benchmark_problem(benchmark)

    print(f"Retrieved benchmark problem {benchmark}")

    manager = InMemoryApproxExecutionManager(
        base_params=EstimateBaseParams(
            a=100,
            q=1,
            km=dict(Counter([x.size() for x in problem.variables])),
            max_mc=None,
        )
    )

    print("Setup Manager")

    scheduler = ConfidentEdgeFinderLinearSearchEstimateScheduler(
        manager=manager,
        confidence=0.75,
    )

    print("Setup Scheduler")

    integrator = MultiProcessingEstimateIntegratorZ3(
        worker_count=os.cpu_count(),
        scheduler=scheduler,
        problem_params=problem,
    )

    print("Setup Integrator")

    print("Starting Integrator Run")
    s = perf_counter()

    integrator.run()

    d = perf_counter() - s

    print(f"Scheduler Result is {scheduler.result()}")
    print(f"Took {d:.2f} seconds")

    return d, scheduler.result()


if __name__ == "__main__":
    c = 10

    tested_benchmarks: List[str] = [b for b in get_benchmark_list() if b.startswith("11")]

    code_dir = os.path.dirname(__file__)
    ib_file_name = os.path.join(code_dir, "output", "integrator_benchmark_results.txt")
    bc_file_name = os.path.join(code_dir, "output", "branching_counter_benchmark_results.txt")

    # clear benchmark result files
    with open(ib_file_name, "w") as fib, open(bc_file_name, "w") as fbc:
        pass

    for benchmark in tested_benchmarks:
        print(f"Running Benchmark \"{benchmark}\"")
        for i in range(c):
            duration, result = run_benchmark(benchmark)

            print("Writing results to file...")

            with open(ib_file_name, "a") as fib:
                fib.write(f"{benchmark};{i};{duration};{result}\n")

            # problem = get_benchmark_problem(benchmark)
            # s = perf_counter()
            # mc = count_models_by_branching(problem.formula, problem.variables)
            # mc = 0
            # d = perf_counter() - s
            # print(f"Running exact model count took {d:.2f} seconds and returned {mc}")
            # fbc.write(f"{benchmark};{i};{c};{mc}\n")
