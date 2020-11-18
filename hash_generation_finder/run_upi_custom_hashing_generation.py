from z3 import *
from typing import List
from hash_generation_finder.upi_hashing import generate_upi_hash_sets_via_solver, convert_hash_set_to_tuple_representation
from itertools import combinations

# runs some pi hash generation

if __name__ == "__main__":
    # Generates upi hash function
    n = 3
    k = n + 1

    # makes the iteration stop after at least stop_after hash sets have been found,
    # if negative or zero will only stop once all have been found
    stop_after = 1

    def make_additional_condition(hash_is_zero: List[List[BoolRef]]) -> BoolRef:
        def compare_hash_range(
            i1: int,
            i1m1: int,
            i2: int,
            i2m1: int,
            ml: int,
            inverse_equality: bool = False,
        ) -> BoolRef:
            """
            Compares the hash i1 at the values i1m1 to i1m1 + ml - 1
            to hash i2 at the values i2m1 to i2m1 + ml - 1, s.t.
            if inverse_equality is False it returns whether the hash
            range is equal and otherwise whether the hash ranges are inversely equal
            """

            modifier = (lambda x: Not(x)) if inverse_equality else (lambda x: x)
            return And([hash_is_zero[i1][i1m1 + l] == modifier(hash_is_zero[i2][i2m1 + l]) for l in range(ml)])

        def is_hash_prefix_equal(m2: int, i1: int, i2: int):
            """
            Returns whether the hash range from 0 to m2 - 1 at the hashes i1 and i2
            is equal
            """
            return compare_hash_range(i1, 0, i2, 0, m2, False)

        conditions = []

        self_inverse = And([
            And([
                hash_is_zero[2*i][j] == Not(hash_is_zero[2*i+1][j]) for j in range(2**n)
            ]) for i in range(2**(k-1))
        ])

        dual_extension = And([
            And([
                is_hash_prefix_equal(2 ** (n - 1), 2 * i, 2 * i + 1),
                And([Not(is_hash_prefix_equal(2 ** (n - 1), 2 * i, 2 * i2)) for i2 in range(2 ** (k - 1)) if i2 != i])
            ]) for i in range(2 ** (k - 1))
        ])

        paired_inverse_dual_extension = And([
            dual_extension,
            And([
                compare_hash_range(2 * i, 2 ** (n - 1), 2 * i + 1, 2 ** (n - 1), 2 ** (n - 1), True)
                for i in range(2 ** (k - 1))
            ])
        ])

        self_paired_inverse_dual_extension = And([
            paired_inverse_dual_extension,
            And([
                Or([
                    compare_hash_range(2 * i, 0, 2 * i, 2 ** (n - 1), 2 ** (n - 1)),
                    compare_hash_range(2 * i + 1, 0, 2 * i + 1, 2 ** (n - 1), 2 ** (n - 1)),
                ])
                for i in range(2 ** (k - 1))
            ])
        ])

        # asserts that the hash set must be a self inverse hash set
        # conditions.append(self_inverse)

        # only one of following the modifiers should active at once

        # asserts that the hash set must be a dual extension
        # conditions.append(dual_extension)

        # asserts that the hash set must be a paired inverse dual extension
        # conditions.append(paired_inverse_dual_extension)

        # asserts that the hash set must be a paired inverse dual extension
        # that was applied using the same hash set twice
        # conditions.append(self_paired_inverse_dual_extension)

        return And(conditions)

    HS = set()

    for H in generate_upi_hash_sets_via_solver(n, k, make_additional_condition, True):
        HC = convert_hash_set_to_tuple_representation(H)

        print("----------------------------------")
        for h in HC:
            print(h)
        print("----------------------------------")

        HS.add(HC)

        if len(HS) >= stop_after and stop_after > 0:
            print("Found >={stop_after} hash sets that comply with the conditions".format(stop_after=stop_after))
            break

    """
    # Generates pi hash function
    n = 3
    k = n+1

    hash_is_zero = [
        [Bool("h[{i}]({j})=0".format(i=i, j=j)) for j in range(2**n)] for i in range(2**k)
    ]

    sym = And([hash_is_zero[i][j] == hash_is_zero[i][2**n-1-j] for j in range(2**(n-1)) for i in range(2**k)])

    hash_prob = [Int("h[{i}].prob".format(i=i)) for i in range(2**k)]

    hp = And([0 < hash_prob[i] for i in range(2**k)])

    total = Int("h_prob_total")
    ht = total == Sum(hash_prob)

    h0pc = And([
        2 * Sum([If(hash_is_zero[i][j], hash_prob[i], 0) for i in range(2**k)]) == total for j in range(2**n)
    ])

    hh0pc = And([
        4 * Sum([
            If(And([hash_is_zero[i][j1], hash_is_zero[i][j2]]), hash_prob[i], 0)
            for i in range(2**k)
        ]) == total for j1, j2 in combinations(range(2**n), 2)
    ])

    solver = Solver()
    solver.add(hp)
    solver.add(ht)
    solver.add(h0pc)
    solver.add(hh0pc)

    # forces each hash to be symmetric
    solver.add(sym)

    ret = solver.check()
    if ret != sat:
        raise ValueError("Solver responded with " + str(ret))

    m = solver.model()

    m_hash_prob = tuple([m[hash_prob[i]] for i in range(2**k)])
    m_hashes = tuple([
        tuple([0 if m[hash_is_zero[i][j]] else 1 for j in range(2**n)]) for i in range(2**k)
    ])

    print("TOTAL {total}".format(total=m[total]))
    for i in range(2**k):
        print("P {p}".format(p=m_hash_prob[i]))
        print(m_hashes[i])
    """