from time import perf_counter
from source_algo_implementation_binary_search_multi_processing_voters.approx import approx
from alternatives.branching_counter import count_models_by_comparison_branching
from problem_generator.generator import generate_random_problem, convert_problem
from os import cpu_count

if __name__ == "__main__":
    s = perf_counter()

    problem = generate_random_problem(10, 3, 0)
    formula, variables = convert_problem(problem)

    count_models_by_comparison_branching(
        formula=formula,
        variables=variables,
        bit_count=2,
    )

    print("Method 1 Took {d} seconds".format(d=perf_counter() - s))

    s = perf_counter()

    approx(
        worker_count=cpu_count(),
        bit_count=2,
        formula=formula,
        variables=variables,
        a=100,
        alpha=0.1,
        epsilon=0.1,
    )

    print("Method 2 Took {d} seconds".format(d=perf_counter() - s))