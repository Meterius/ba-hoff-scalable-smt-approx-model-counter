from implementation.estimate_runner import EstimateRunner, ApproxParams, ApproxPayloadParams
from time import perf_counter
from z3 import *

if __name__ == "__main__":
    n = 20
    x, y, z = Ints("x y z")
    f = And([
        x >= 0,
        y >= 0,
        x % 4 == 0,
        y % 5 == 0,
        z < x + y,
    ])

    runner = EstimateRunner(
        approx_params=ApproxParams(
            a=10,
            q=1,
            bit_count=2*n,
        )
    )

    s = perf_counter()

    runner.initialize(
        ApproxPayloadParams(
            formula=f,
            variables=[(x, n), (y, n)],
        )
    )

    print(f"Initialize took {perf_counter()-s:.3f} seconds")

    for m in range(1, 2 * n + 1):
        s = perf_counter()
        print(runner.estimate(m))
        print(f"Estimate for m={m} took {perf_counter()-s:.3f} seconds")

    print("Finished")
