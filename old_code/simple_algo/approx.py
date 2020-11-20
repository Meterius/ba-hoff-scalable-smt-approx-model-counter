from z3 import *
from math import *
import random
from itertools import chain
from typing import List, cast
from old_code.source_algo_implementation.z3_helper import limited_model_count, clone_formula, is_binary_encoding


def generate_xor_hash(i: int, n: int, x: ArithRef):
    conditions = []

    vals = [Int("estimate_{i}_val_{j}".format(i=i, j=j)) for j in range(n)]
    rets = [Bool("estimate_{i}_ret_{j}".format(i=i, j=j)) for j in range(n)]

    conditions.append(rets[0] == (random.choice([0, 1]) == vals[0]))
    conditions.append(vals[-1] == x)

    for j in range(n):
        if j != 0:
            conditions.append(
                rets[j] == rets[j - 1] if random.choice([False, True]) else Xor(rets[j - 1], vals[j] >= 2 ** j)
            )

        if j != n - 1:
            conditions.append(
                vals[j] == If(vals[j + 1] >= 2 ** (j + 1), vals[j + 1] - 2 ** (j + 1), vals[j + 1])
            )

    conditions.append(rets[-1])

    return And(conditions)


def estimate(solver: Solver, variable: ArithRef, n: int, m: int, a: int) -> bool:
    solver.push()

    for i in range(m):
        solver.add(generate_xor_hash(i, n, variable))

    has_at_least_a_models = limited_model_count(solver, [variable], a) is None

    solver.pop()

    return has_at_least_a_models


def approx(
    formula: ExprRef,
    variable: ArithRef,
    n: int,
    alpha: float,
) -> float:
    a = 1
    epsilon = 2
    q: int = int(ceil((1 + 4 * log2(sqrt(a + 1) + 1) - 2 * log2(a)) / (2 * log2(1 + epsilon))))
    mp: int = int(floor(n - 2 * log2(sqrt(a + 1) + 1)))
    r: int = int(ceil(8 * log((1 / alpha) * mp)))
    p: int = int(ceil((sqrt(a + 1) - 1) ** (2 / q)))

    if q == 1:
        raise ValueError("q needs to be 1")

    solver = Solver()
    solver.add(formula)

    lmc = limited_model_count(solver, [variable], p + 1)
    if lmc is not None:
        return lmc

    m = 1
    while m <= mp:
        c = 0

        print("Iter ({m}/{mp})".format(m=m, mp=mp))

        for i in range(1, r + 1):
            print("Iter ({m}/{mp}) - {i}".format(m=m, mp=mp, i=i))
            if estimate(solver, variable, n, m, a):
                c += 1

            # early majority vote termination
            if c > r / 2 or c + (r - i) <= r / 2:
                break

        if c <= r / 2:
            break

        m += 1

    return (a * (2 ** (m - 0.5))) ** (1/q)


def run_reference_test():
    x = Int("x")
    f = And([0 <= x, x % 4 == 0])

    print(
        approx(
            f, x, 12, 0.1
        )
    )


if __name__ == "__main__":
    run_reference_test()
