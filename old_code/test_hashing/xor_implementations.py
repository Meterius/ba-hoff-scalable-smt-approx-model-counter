from z3 import *
from hash_generation_finder.utility import convert_hash_set_to_tuple_representation
from old_code.source_algo_implementation.z3_helper import is_binary_encoding
from alternatives.exclusion_counter import iterate_models_by_exclusion
from alternatives.branching_counter import iterate_models_by_boolean_branching
from itertools import product
from typing import List, Callable


def ref_xor_hash_on_word_level(bits: List[BoolRef], a: List[bool]):
    conditions = []

    n = len(bits)
    x = Int("x")
    conditions.append(is_binary_encoding(x, bits))

    vals = [Int("val_{j}".format(j=j)) for j in range(n)]
    rets = [Bool("ret_{j}".format(j=j)) for j in range(n)]

    conditions.append(rets[0] == (int(a[0]) == vals[0]))
    conditions.append(vals[-1] == x)

    for j in range(n):
        if j != 0:
            conditions.append(
                rets[j] == rets[j - 1] if a[j+1] else Xor(rets[j - 1], vals[j] >= 2 ** j)
            )

        if j != n - 1:
            conditions.append(
                vals[j] == If(vals[j + 1] >= 2 ** (j + 1), vals[j + 1] - 2 ** (j + 1), vals[j + 1])
            )

    conditions.append(rets[-1])

    return And(conditions)


def ref_xor_hash(bits: List[BoolRef], a: List[bool]):
    def xor_sum(bs: List[BoolRef]) -> BoolRef:
        if len(bs) == 0:
            return BoolVal(False)
        elif len(bs) == 1:
            return bs[0]
        else:
            return Xor(bs[0], xor_sum(bs[1:]))

    return Xor(
        a[0],
        xor_sum([And(a[i+1], bit) for i, bit in enumerate(bits)])
    )


def assert_is_xor_hash_set_generator(n: int, other_generator: Callable[[List[BoolRef], List[bool]], BoolRef]):
    bits = [Bool("b_{i}".format(i=i)) for i in range(n)]

    def evaluate_hash_set(generator: Callable[[List[BoolRef], List[bool]], BoolRef]):
        H = set()

        for a in map(list, product([False, True], repeat=n+1)):
            h = [0] * (2**len(bits))

            formula = generator(bits, a)

            for m in iterate_models_by_boolean_branching(formula, bits):
                h[sum([2**i if m[bit] else 0 for i, bit in enumerate(bits)])] = 1

            H.add(tuple(h))

        return tuple(H)

    H1 = convert_hash_set_to_tuple_representation(evaluate_hash_set(ref_xor_hash))
    H2 = convert_hash_set_to_tuple_representation(evaluate_hash_set(other_generator))

    print("---")
    for h in H1:
        print(h)
    print("---")
    for h in H2:
        print(h)
    print("---")

    if H1 != H2:
        raise ValueError("Other generator does not generate xor hash set")


if __name__ == "__main__":
    assert_is_xor_hash_set_generator(3, ref_xor_hash_on_word_level)
