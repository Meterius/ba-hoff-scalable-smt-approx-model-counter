from alternatives.branching_counter import iterate_models_by_boolean_branching
from hash_generation_finder.utility import convert_hash_set_to_tuple_representation
from z3 import *
import numpy as np
from itertools import combinations, permutations
from typing import Iterable, Any
from math import *


# Hash Functions are represented as a numpy array.
# Hash Sets are represented as a two dimensional numpy array where each column corresponds to a hash function.

# Tuple representation represents hash functions as a tuple
# Tuple representation represents hash sets as a tuple of tuple representation of
# hash functions which are sorted


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


def generate_upi_hash_sets_via_solver(n: int, k: int) -> Iterable[Any]:
    print("Generating UPI sets for n={n} and k={k}".format(n=n, k=k))

    bits = [[Bool("hash({i})_value({j})".format(i=i, j=j)) for j in range(2**n)] for i in range(2**k)]

    hash_is_zero = [
        [Not(bits[i][j]) for j in range(2**n)] for i in range(2**k)
    ]

    def cond_prob_of_zero_is_one_half(j: int) -> BoolRef:
        return PbEq([(hash_is_zero[i][j], 1) for i in range(2**k)], 2**(k-1))

    val_eq_1_conditions = And([
        cond_prob_of_zero_is_one_half(j) for j in range(2**n)
    ])

    def cond_prob_of_two_zeros_is_one_quarter(j1: int, j2: int) -> BoolRef:
        return PbEq([(And([hash_is_zero[i][j1], hash_is_zero[i][j2]]), 1) for i in range(2**k)], 2**(k-2))

    val_comb_eq_0_conditions = And([
        cond_prob_of_two_zeros_is_one_quarter(a, b) for a, b in combinations(range(2**n), 2)
    ])

    def hash_is_lexicographically_smaller_than(i1: int, i2: int) -> BoolRef:
        return Sum([If(bits[i1][j], 2**j, 0) for j in range(2**n)]) < Sum([If(bits[i2][j], 2**j, 0) for j in range(2**n)])

    hash_set_distinct = And([
        hash_is_lexicographically_smaller_than(i, i+1) for i in range(2**k - 1)
    ])

    models = iterate_models_by_boolean_branching(
        formula=And([val_eq_1_conditions, val_comb_eq_0_conditions, hash_set_distinct]),
        variables=[bit for bit_row in bits for bit in bit_row],
    )

    found = 0
    for m in models:
        found += 1
        H = np.array([[1 if m[bits[i][j]] else 0 for i in range(2 ** k)] for j in range(2 ** n)])

        if found % 1 == 0:
            print("Found {found} models so far...".format(found=found))

        yield H

    print("Finished UPI generator for n={n} and k={k}".format(n=n, k=k))