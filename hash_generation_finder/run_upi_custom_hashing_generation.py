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
    solver.add(self_inverse)

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