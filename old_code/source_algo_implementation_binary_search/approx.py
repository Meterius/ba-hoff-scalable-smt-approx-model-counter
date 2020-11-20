from z3 import *
from math import *
from itertools import chain
from time import perf_counter
from typing import Dict, List, cast
from old_code.source_algo_implementation.z3_helper import random_m_xor_hash_equals_zero, \
    limited_model_count, clone_formula, is_binary_encoding


def estimate(solver: Solver, variables: List[ArithRef], bits: List[BoolRef], m: int, a: int) -> bool:
    """
    Given a `solver` that has the formula asserted, the variables and the bits that
    constitute the unsigned binary encodings of the variables, this function implements
    the estimate function from the smt paper.
    :param solver:
    :param variables:
    :param bits:
    :param m:
    :param a:
    :return:
    """

    solver.push()

    solver.add(random_m_xor_hash_equals_zero(m, bits))
    has_at_least_a_models = limited_model_count(solver, variables, a) is None

    solver.pop()

    return has_at_least_a_models


def approx(
    formula: ExprRef,
    variables: List[ArithRef],
    bit_count: int,
    a: int,
    alpha: float,
    epsilon: float,
) -> float:
    q: int = int(ceil((1 + 4 * log2(sqrt(a + 1) + 1) - 2 * log2(a)) / (2 * log2(1 + epsilon))))
    n = bit_count * len(variables) * q
    mp: int = int(floor(n - 2 * log2(sqrt(a + 1) + 1)))
    r: int = int(ceil(8 * log((1 / alpha) * mp)))
    p: int = int(ceil((sqrt(a + 1) - 1) ** (2 / q)))

    # map from variable to its encoding bits
    bits_map = {
        x: [Bool("bit({i})_{x}".format(i=i, x=x)) for i in range(bit_count)] for x in variables
    }

    # formula that represents "formula and each variable is binary encoding of its bits"
    formula_e = And(formula, And([is_binary_encoding(x, bits_map[x]) for x in variables]))

    cloned_formula_e_return = clone_formula(formula_e, q)
    # formula that represents "formula_e but cloned q times"
    formula_q = And(cloned_formula_e_return.clone_formulas)
    # variables in formula_q that represent cloned versions of the formula variables
    q_variables = [cast(ArithRef, x_q) for x in variables for x_q in cloned_formula_e_return.clone_vars_map[x]]
    # bits in formula_q that represent cloned versions of the formula_e bits
    q_bits = [
        cast(BoolRef, bit_q)
        for bit in chain.from_iterable(bits_map.values())
        for bit_q in cloned_formula_e_return.clone_vars_map[bit]
    ]

    solver = Solver()
    solver.add(formula_q)

    lmc = limited_model_count(solver, variables, p + 1)
    if lmc is not None:
        return lmc

    cached_mj_estimate_cache: Dict[int, bool] = {}

    def cached_mj_estimate(m: int) -> bool:
        if m not in cached_mj_estimate_cache:
            c = 0

            for i in range(1, r + 1):
                if estimate(solver, q_variables, q_bits, m, a):
                    c += 1

                # early majority vote termination
                if c > r / 2 or c + (r - i) <= r / 2:
                    break

            cached_mj_estimate_cache[m] = c > r / 2

        print("Estimate majority for m={m} is {0}".format(cached_mj_estimate_cache[m], m=m))

        return cached_mj_estimate_cache[m]

    def compare_edge_to(m: int) -> int:
        estimate_base = cached_mj_estimate(m)

        if m == 1 and not estimate_base:
            return 0
        elif m == mp:
            return 0 if estimate_base else -1
        elif estimate_base:
            return 1

        estimate_prev = cached_mj_estimate(m - 1)

        return 0 if estimate_prev else -1

    left = 1
    right = mp

    m = 1
    while left <= right:
        m = floor((left + right) / 2)
        print("Looking at m={m}".format(m=m))

        comparison = compare_edge_to(m)

        if comparison == -1:
            print("Edge is smaller then m={m}".format(m=m))
            right = m - 1
        elif comparison == 1:
            print("Edge is greater then m={m}".format(m=m))
            left = m + 1
        else:
            print("Edge found at m={m}".format(m=m))
            break

    if left > right:
        print(
            "Edge is not present, i.e. a estimate majority vote must have returned an incorrect result, assuming m={m}"
            .format(m=m)
        )

    return (a * (2 ** (m - 0.5))) ** (1 / q)


def run_reference_test():
    x = Int("x")
    f = And([0 <= x, x < 42])

    s = perf_counter()

    print(
        approx(
            f, [x], 7, 100, 0.1, 0.2,
        )
    )

    print("Took {d} seconds".format(d=perf_counter() -s ))


if __name__ == "__main__":
   run_reference_test()
