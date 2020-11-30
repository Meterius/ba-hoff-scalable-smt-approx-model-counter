from implementation.estimate_manager import EstimateBaseParams
from implementation.estimate_runner import EstimateRunner, EstimateTask, EstimateProblemParams
from time import perf_counter
from z3 import *

if __name__ == "__main__":
    k = 16
    x, y, z = BitVecs("x y z", k)
    f = And([
        URem(x, 4) == 0,
        URem(y, 5) == 0,
        ULT(z, x + y),
    ])

    s1 = perf_counter()

    runner = EstimateRunner(
        base_params=EstimateBaseParams(
            a=1,
            q=1,
            bc=2*k,
            max_mc=None,
        ),
        problem_params=EstimateProblemParams(
            formula=f,
            variables=[(x, k), (y, k)],
        )
    )

    print(f"Initialize took {perf_counter()-s1:.3f} seconds")

    for m in range(1, 2 * k + 1):
        s = perf_counter()
        result = runner.estimate(EstimateTask(m=m))
        print(result)
        print(f"Estimate for m={m} took {perf_counter()-s:.3f} seconds")

    print(f"Finished, took {perf_counter()-s1:.3f} seconds")
