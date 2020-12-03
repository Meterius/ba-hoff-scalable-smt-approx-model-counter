from pysmt.shortcuts import Symbol, And, BVURem, BVULT, BV, Equals
from pysmt.typing import BVType
from implementation.estimate_manager import EstimateBaseParams
from implementation.estimate_runner import EstimateTask
from implementation.estimate_runner_pysmt import EstimateRunnerPYSMT, EstimateProblemParamsPYSMT
from time import perf_counter

if __name__ == "__main__":
    k = 6
    x, y, z = [Symbol(name, BVType(k)) for name in ("x", "y", "z")]
    f = And([
        Equals(BVURem(x, BV(4, k)), BV(0, k)),
        Equals(BVURem(y, BV(5, k)), BV(0, k)),
        BVULT(z, x + y),
    ])

    s1 = perf_counter()

    runner = EstimateRunnerPYSMT(
        base_params=EstimateBaseParams(
            a=35,
            q=3,
            k=k,
            n=2,
            max_mc=None,
        ),
        problem_params=EstimateProblemParamsPYSMT(
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

