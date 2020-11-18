from z3 import *
from itertools import combinations

# runs some pi hash generation

if __name__ == "__main__":
    # Generates upi hash function
    n = 3
    k = n + 1

    hash_is_zero = [
        [Bool("h[{i}]({j})=0".format(i=i, j=j)) for j in range(2 ** n)] for i in range(2 ** k)
    ]

    h0pc = And([
        PbEq([(hash_is_zero[i][j], 1) for i in range(2**k)], 2**(k-1)) for j in range(2 ** n)
    ])

    hh0pc = And([
        PbEq([
            (And([hash_is_zero[i][j1], hash_is_zero[i][j2]]), 1) for i in range(2**k)
        ], 2**(k-2)) for j1, j2 in combinations(range(2 ** n), 2)
    ])

    solver = Solver()
    solver.add(h0pc)
    solver.add(hh0pc)

    self_inverse = And([
        And([
            hash_is_zero[2*i][j] == Not(hash_is_zero[2*i+1][j]) for j in range(2**n)
        ]) for i in range(2**(k-1))
    ])
    # solver.add(self_inverse) # asserts that the hash set must be a self inverse hash set

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

    dual_extension = And([
        And([
            is_hash_prefix_equal(2**(n-1), 2*i, 2*i+1),
            And([Not(is_hash_prefix_equal(2**(n-1), 2*i, 2*i2)) for i2 in range(2**(k-1)) if i2 != i])
        ]) for i in range(2**(k-1))
    ])

    paired_inverse_dual_extension = And([
        dual_extension,
        And([
            compare_hash_range(2*i, 2**(n-1), 2*i+1, 2**(n-1), 2**(n-1), True)
            for i in range(2**(k-1))
        ])
    ])

    self_paired_inverse_dual_extension = And([
        paired_inverse_dual_extension,
        And([
            Or([
                compare_hash_range(2 * i, 0, 2 * i, 2 ** (n - 1), 2 ** (n - 1)),
                compare_hash_range(2 * i + 1, 0, 2 * i + 1, 2 ** (n - 1), 2 ** (n - 1)),
            ])
            for i in range(2**(k-1))
        ])
    ])

    # only one of following the modifiers should active at once
    # asserts that the hash set must be a dual extension
    # solver.add(dual_extension)
    # asserts that the hash set must be a paired inverse dual extension
    # solver.add(paired_inverse_dual_extension)
    # asserts that the hash set must be a paired inverse dual extension that was applied using the same hash set twice
    solver.add(self_paired_inverse_dual_extension)

    def hash_is_lexicographically_smaller_than(i1: int, i2: int):
        return Sum([If(hash_is_zero[i1][j], 0, 2**(n-j-1)) for j in range(2**n)])\
               < Sum([If(hash_is_zero[i2][j], 0, 2**(n-j-1)) for j in range(2**n)])

    # ensures that no two models encode the same hash function
    # and the hash bit rows are ordered with ascending binary number
    # value interpreting the leading bit as the highest valued
    hash_set_distinct = And([
        hash_is_lexicographically_smaller_than(i, i+1) for i in range(2**k - 1)
    ])

    solver.add(hash_set_distinct)

    ret = solver.check()
    if ret != sat:
        raise ValueError("Solver responded with " + str(ret))

    m = solver.model()

    m_hashes = tuple([
        tuple([0 if m[hash_is_zero[i][j]] else 1 for j in range(2 ** n)]) for i in range(2 ** k)
    ])

    for i in range(2 ** k):
        print(m_hashes[i])

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