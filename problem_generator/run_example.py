from time import perf_counter
from problem_generator.example_problem import example_problem_formula, example_problem_formula_variables
from source_algo_implementation_binary_search_multi_processing_voters.approx import approx
from alternatives.branching_counter import count_models_by_comparison_branching
from os import cpu_count

if __name__ == "__main__":
    s = perf_counter()

    """
    count_models_by_comparison_branching(
        formula=example_problem_formula,
        variables=example_problem_formula_variables,
        bit_count=2,
    )
    """

    approx(
        worker_count=cpu_count(),
        bit_count=2,
        formula=example_problem_formula,
        variables=example_problem_formula_variables,
        a=1000,
        alpha=0.1,
        epsilon=0.1,
    )

    print("Took {d} seconds".format(d=perf_counter() - s))