from time import perf_counter
from source_algo_implementation.approx import approx as ref_approx
from source_algo_implementation_binary_search_multi_processing_voters.approx import approx as bsmpv_approx
from alternatives.branching_counter import count_models_by_comparison_branching
from problem_generator.generator import generate_random_problem, convert_problem
from os import cpu_count

if __name__ == "__main__":
    problem = generate_random_problem(100, 100, 0)
    formula, variables = convert_problem(problem)

    # s = perf_counter()

    # print(count_models_by_comparison_branching(
    #    formula=formula,
    #    variables=variables,
    #    bit_count=2,
    #))

    # print("Method 1 Took {d} seconds".format(d=perf_counter() - s))

    s = perf_counter()

    print(bsmpv_approx(
        worker_count=cpu_count(),
        bit_count=2,
        formula=formula,
        variables=variables,
        a=1,
        alpha=0.25,
        epsilon=9,
    ))

    print("Method 2 Took {d} seconds".format(d=perf_counter() - s))

    s = perf_counter()

    print(ref_approx(
        bit_count=2,
        formula=formula,
        variables=variables,
        a=1,
        alpha=0.25,
        epsilon=9,
    ))

    print("Method 3 Took {d} seconds".format(d=perf_counter() - s))