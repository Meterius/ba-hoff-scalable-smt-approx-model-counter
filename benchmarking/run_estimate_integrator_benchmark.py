from typing import Tuple, List
from collections import Counter
from time import perf_counter
from implementation.estimate_manager import InMemoryApproxExecutionManager, EstimateBaseParams
from implementation.estimate_scheduler import ConfidentEdgeFinderLinearSearchEstimateScheduler
from implementation.estimate_integrator_z3 import MultiProcessingEstimateIntegratorZ3
from benchmarking.convert_benchmark_z3 import get_benchmark_problem
import os


def run_benchmark(benchmark: str) -> Tuple[float, Tuple[float, float]]:
    problem = get_benchmark_problem(benchmark)

    print(f"Retrieved benchmark problem {benchmark}")

    a = 100

    manager = InMemoryApproxExecutionManager(
        base_params=EstimateBaseParams(
            q=1,
            km=dict(Counter([x.size() for x in problem.variables])),
            max_mc=None,
        )
    )

    print("Setup Manager")

    scheduler = ConfidentEdgeFinderLinearSearchEstimateScheduler(
        manager=manager,
        confidence=0.75,
        a=a,
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
    c = 1

    tested_benchmarks: List[str] = ['case1', 'case2', 'case26', 'case68']

    code_dir = os.path.dirname(__file__)
    file_name = os.path.join(code_dir, "output", "benchmark_results.txt")

    # clear benchmark result files
    with open(file_name, "w") as fb:
        pass

    for benchmark in tested_benchmarks:
        print(f"Running Benchmark \"{benchmark}\"")
        for i in range(c):
            duration, result = run_benchmark(benchmark)

            # problem = get_benchmark_problem(benchmark)
            # s = perf_counter()
            # result = count_models_by_branching(problem.formula, problem.variables)
            # duration = perf_counter() - s
            # print(f"Running exact model count took {duration:.2f} seconds and returned {result}")

            with open(file_name, "a") as fb:
                fb.write(f"{benchmark};{i};{duration};{result}\n")

            # problem = get_benchmark_problem(benchmark)
            # s = perf_counter()
            # mc = count_models_by_branching(problem.formula, problem.variables)
            # d = perf_counter() - s
            # print(f"Running exact model count took {d:.2f} seconds and returned {mc}")
            #
            # with open(bc_file_name, "a") as fbc:
            #     fbc.write(f"{benchmark};{i};{c};{mc}\n")
