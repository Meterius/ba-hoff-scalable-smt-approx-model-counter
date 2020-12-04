from implementation.estimate_runner_z3 import EstimateProblemParamsZ3
from implementation.helper import deserialize_expression, get_variables
from benchmarking.benchmark import get_benchmark_smt2


def get_benchmark_problem(benchmark: str) -> EstimateProblemParamsZ3:
    smt2 = get_benchmark_smt2(benchmark)
    expr = deserialize_expression(smt2)
    variables = get_variables(expr)

    return EstimateProblemParamsZ3(
        formula=expr,
        variables=variables,
    )
