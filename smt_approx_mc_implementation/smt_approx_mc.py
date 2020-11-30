from z3 import Solver, BitVecRef, BitVecVal, BoolRef, And, Or, Sum, \
    Extract, BitVecs, unsat, unknown, ULT, ZeroExt, URem
from typing import List, Optional
from itertools import count
from statistics import median
from math import ceil, log2, exp, floor
from random import randint
from alternatives.exclusion_counter import count_models_by_exclusion


def bit_count(x: int):
    return int(ceil(log2(x)))


def smt_approx_mc(
    formula: BoolRef,
    variables: List[BitVecRef],
    epsilon: float,
    sigma: float,
    k: int,
):
    counter = 0
    M = []
    pivot = 2 * int(ceil(exp(-3 / 2) * (1 + (1 / epsilon)) ** 2))
    t = int(ceil(35 * log2(3 / sigma)))

    solver = Solver()
    solver.add(formula)

    while True:
        m = smt_approx_mc_core(solver, variables, pivot, k)
        counter = counter + 1

        if m is not None:
            M.append(m)

        if counter >= t:
            break

    return median(M)


def smt_approx_mc_core(
    solver: Solver,
    variables: List[BitVecRef],
    pivot: int,
    k: int,
) -> Optional[int]:
    n = len(variables)

    Y = bounded_smt(solver, variables, pivot)

    if Y is not None:
        return Y
    else:
        C = [0, 1]
        i = 1
        numCells = p(k, 1)

        while True:
            alpha = [
                [randint(0, p(k, j) - 1) for _ in range(c)]
                for j, c in enumerate(C)
            ]
            h_equals_alpha = h_equals_alpha_from_H_SMT(variables, k, C, alpha)

            solver.push()
            solver.add(h_equals_alpha)
            Y = bounded_smt(solver, variables, pivot)
            solver.pop()

            if Y is None:
                C[i] += 1
                numCells *= p(k, i)

            if Y == 0:
                if p(k, i) > 2:
                    C[i] -= 1
                    i += 1
                    C.append(1)
                    numCells *= p(k, i + 1) / p(k, i)
                else:
                    break

            if (0 != Y and Y is not None) or (numCells > 2 ** (n * k)):
                break

        if Y is None or Y == 0:
            return None
        else:
            return Y * numCells


def h_equals_alpha_from_H_SMT(
    variables: List[BitVecRef],
    k: int,
    C: List[int],
    alpha: List[List[int]],
):
    return And([
        And([
            h_j(variables, k, j) == alpha[j][i] for i in range(c)
        ]) for j, c in enumerate(C) if c != 0
    ])


def h_j(
    variables: List[BitVecRef],
    k: int,
    j: int,
):
    n = len(variables)
    p_bc = bit_count(p(k, j))

    def x_m(m: int):
        i = int(floor(m / (2 ** j)))
        s = (m % (2 ** j)) * int(k / (2 ** j))
        t = s + int(k / (2 ** j)) - 1

        return ZeroExt(p_bc - (t - s + 1), Extract(t, s, variables[i]))

    return URem(
        Sum([
           BitVecVal(randint(0, p(k, j) - 1), p_bc) * x_m(m) for m in range(n * (2 ** j))
        ]) + BitVecVal(randint(0, p(k, j) - 1), p_bc),
        p(k, j)
    )


def bounded_smt(
    solver: Solver,
    variables: List[BitVecRef],
    pivot: int,
) -> Optional[int]:
    solver.push()

    for i in range(pivot + 1):
        response = solver.check()

        if response == unknown:
            solver.pop()
            raise ValueError("Solver responded with unknown")
        elif response == unsat:
            solver.pop()
            return i

        if i != pivot:
            m = solver.model()
            solver.add(
                Or([
                    x != m[x]
                    for x in variables
                ])
            )

    solver.pop()
    return None


def p(k: int, j: int) -> int:
    for x in count(int(2 ** (k / (2 ** j)))):
        if all(map(lambda y: x % y != 0, range(2, x))):
            return x


if __name__ == "__main__":
    x, y, z = BitVecs("x y z", 8)

    ux = 2 ** (3 + 2)
    uy = 2 ** 6
    uz = 2 ** 7

    f = And([
        (x % 8) == 0,
        ULT(x, ux),
        ULT(y, uy),
        ULT(z, uz),
    ])

    epsilon = 0.2
    mc = (ux / 8) * uy * uz
    print(f"Exact Model Count: {mc}")
    print(f"Expects with epsilon={epsilon} that {mc / (1 + epsilon):.3f} <= response <= {mc * (1 + epsilon):.3f}")


    print(f"SMT Approx MC Count: {smt_approx_mc(f, [x, y, z], epsilon, 0.2, 8)}")
