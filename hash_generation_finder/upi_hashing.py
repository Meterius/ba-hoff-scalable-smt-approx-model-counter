from alternatives.branching_counter import iterate_models_by_boolean_branching
from alternatives.exclusion_counter import iterate_models_by_exclusion
from hash_generation_finder.utility import convert_hash_set_to_tuple_representation, \
    convert_hash_set_to_numpy_representation
from z3 import *
import numpy as np
from itertools import combinations, permutations, product
from typing import Iterable, Any, Callable, Optional, List, Iterable, Tuple
from math import *


# Hash Functions are represented as a numpy array.
# Hash Sets are represented as a two dimensional numpy array where each column corresponds to a hash function.

# Tuple representation represents hash functions as a tuple
# Tuple representation represents hash sets as a tuple of tuple representation of
# hash functions which are sorted


def get_paper_xor_hash(a: int, y: List[int]) -> Tuple[int, ...]:
    return tuple([
        a if Sum([x[i] * y[i] for i in range(len(y))]) % 2 == 1 else 1-a for x in product([0, 1], repeat=len(y))
    ])


def get_paper_xor_hash_set(n: int):
    return convert_hash_set_to_numpy_representation(convert_hash_set_to_tuple_representation(np.array([
        get_paper_xor_hash(a, y) for a in [0, 1] for y in product([0, 1], repeat=n)
    ]).transpose()))


def generate_upi_hash_sets(n: int, k: int) -> Iterable[Any]:
    """
    Generates UPI hash functions with domain 2**n and cardinality 2**k,
    note this function acts like a generator but performs printing.
    """

    print("Generating UPI sets for n={n} and k={k}".format(n=n, k=k))

    possible_rows = np.array([
        [1 if i in c else 0 for i in range(2**k)] for c in
        map(set, combinations(range(2**k), 2**(k-1)))
    ], dtype=int)

    total = factorial(len(possible_rows)) / factorial(len(possible_rows) - 2**n)

    F = set()

    value_pairs = tuple(combinations(range(2**n), 2))

    for i, ixs in enumerate(permutations(range(len(possible_rows)), 2**n)):
        H = possible_rows[np.array(ixs, dtype=int)]

        pairwise_independent = True

        if i % 1000000 == 0:
            print(
                "{p:.2f}% (found {found_amount}) (inspected {i} out of {total})"
                .format(p=100 * i / total, total=total, i=i, found_amount=len(F))
            )

        for a, b in value_pairs:
            coll = np.sum(H[a] * H[b])

            if coll * 4 != 2**k:
                pairwise_independent = False
                break

        if pairwise_independent:
            HC = convert_hash_set_to_tuple_representation(H)

            if HC not in F:
                F.add(HC)
                yield H

    print("Finished UPI generator for n={n} and k={k}".format(n=n, k=k))


def generate_upi_hash_sets_via_solver(
    n: int,
    k: int,
    make_additional_condition: Optional[Callable[[List[List[BoolRef]]], BoolRef]] = None,
    use_exclusion_iterator: bool = True,
) -> Iterable[Any]:
    """
    :param n:
    :param k:
    :param make_additional_condition: Gets with a 2d list called hash_is_zero s.t.
                                      hash_is_zero[i][j] means hash i is zero at value j,
                                      the return value will be added to the model conditions i.e.
                                      the generated hash sets will all satisfy the additional condition
    """

    print("Generating UPI sets for n={n} and k={k}".format(n=n, k=k))

    bits = [[Bool("hash({i})_at_({j})_is_zero".format(i=i, j=j)) for j in range(2**n)] for i in range(2**k)]

    hash_is_zero = [
        [bits[i][j] for j in range(2**n)] for i in range(2**k)
    ]

    def cond_prob_of_zero_is_one_half(j: int) -> BoolRef:
        return PbEq([(hash_is_zero[i][j], 1) for i in range(2**k)], 2**(k-1))

    # ensures the event h(a) = 0 has probability 1 / 2
    val_eq_1_conditions = And([
        cond_prob_of_zero_is_one_half(j) for j in range(2**n)
    ])

    def cond_prob_of_two_zeros_is_one_quarter(j1: int, j2: int) -> BoolRef:
        return PbEq([(And([hash_is_zero[i][j1], hash_is_zero[i][j2]]), 1) for i in range(2**k)], 2**(k-2))

    # ensures the event h(a) = 0 and h(b) = 0 is independent for all a != b
    val_comb_eq_0_conditions = And([
        cond_prob_of_two_zeros_is_one_quarter(a, b) for a, b in combinations(range(2**n), 2)
    ])

    def hash_is_lexicographically_smaller_than(i1: int, i2: int):
        return Sum([If(hash_is_zero[i1][j], 0, 2 ** (n - j - 1)) for j in range(2 ** n)]) \
               < Sum([If(hash_is_zero[i2][j], 0, 2 ** (n - j - 1)) for j in range(2 ** n)])

    # ensures that no two models encode the same hash function
    # and the hash bit rows are ordered with ascending binary number
    # value interpreting the leading bit as the highest valued
    hash_set_distinct = And([
        hash_is_lexicographically_smaller_than(i, i + 1) for i in range(2 ** k - 1)
    ])

    formula = simplify(And([val_eq_1_conditions, val_comb_eq_0_conditions, hash_set_distinct]))

    if make_additional_condition:
        formula = simplify(And(formula, make_additional_condition(hash_is_zero)))

    models = (iterate_models_by_exclusion if use_exclusion_iterator else iterate_models_by_boolean_branching)(
        formula=formula,
        variables=[bit for bit_row in bits for bit in bit_row],
    )

    found = 0
    for m in models:
        found += 1
        H = np.array([[0 if m[bits[i][j]] else 1 for i in range(2 ** k)] for j in range(2 ** n)])

        if found % 100 == 99:
            print("Found {found} models so far...".format(found=found))

        yield H

    print("Finished UPI generator for n={n} and k={k}".format(n=n, k=k))