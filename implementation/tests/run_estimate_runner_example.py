from alternatives.exclusion_counter import count_models_by_exclusion
from implementation.estimate_manager import EstimateBaseParams
from implementation.estimate_runner import EstimateTask
from implementation.estimate_runner_z3 import EstimateRunnerZ3, EstimateProblemParamsZ3
from time import perf_counter
from z3 import *

if __name__ == "__main__":
    k = 6
    x, y, z = BitVecs("x y z", k)
    f = And([
        URem(x, 4) == 0,
        URem(y, 5) == 0,
        ULT(z, x + y),
    ])

    s1 = perf_counter()

    runner = EstimateRunnerZ3(
        base_params=EstimateBaseParams(
            a=35,
            q=3,
            km={k: 2},
            max_mc=None,
        ),
        problem_params=EstimateProblemParamsZ3(
            formula=f,
            variables=[x, y],
        )
    )

    print(f"Initialize took {perf_counter()-s1:.3f} seconds")

    mp = runner.params.get_max_cj_of_possible_c(tuple(), runner.params.cn)

    for m in range(1, mp + 1):
        s = perf_counter()
        task = EstimateTask(c=(0,) * runner.params.cn + (m,))
        result = runner.estimate(task)
        imp = runner.params.get_estimate_result_implication(task, result)
        print(f"{result} which implies mc {'>' if imp[0] else '<'} {imp[1]:.1f}")
        print(f"Estimate for m={m} took {perf_counter()-s:.3f} seconds")

    print(f"Finished, took {perf_counter()-s1:.3f} seconds")

    print(f"Exact model count is {count_models_by_exclusion(f, [x, y])}")
