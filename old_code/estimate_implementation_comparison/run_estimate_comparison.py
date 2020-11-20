from time import perf_counter
from old_code.estimate_implementation_comparison.estimate_implementations import ref_estimate
from old_code.estimate_implementation_comparison.z3_helper import is_binary_encoding
from z3 import *


def run_estimate_benchmark(n: int, estimate):
    print("Starting estimate benchmark for n={n}".format(n=n))

    solver = Solver()
    x = Int("x")
    bits = [Bool("b{i}".format(i=i)) for i in range(n)]

    solver.add(is_binary_encoding(x, bits))
    solver.add(x >= 0)
    solver.add(x + 1 % 4 == 0)

    for m in range(n):
        for a in (1, 100):
            s = perf_counter()

            c = 1
            for i in range(c):
                estimate(
                    solver, [x], bits, m, a
                )

            print(
                "(n={n} m={m}, a={a})".format(n=n, a=a, m=m).ljust(25) +
                "Ran {d:.2f} seconds on average".format(d=(perf_counter() - s)/c)
            )


if __name__ == "__main__":
    run_estimate_benchmark(100, ref_estimate)