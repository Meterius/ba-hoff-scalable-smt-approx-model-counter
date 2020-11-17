from hash_generation_finder.uniform_pairwise_independent_hash_sets.D5_exec import uniform_pairwise_independent_hash_sets_D5
from hash_generation_finder.uniform_pairwise_independent_hash_sets.D6_exec import uniform_pairwise_independent_hash_sets_D6
from hash_generation_finder.hashing import is_pairwise_independent_hash_set, complement_hash_set,\
    inverse_hash, reversed_hash, hashes, uniform_pairwise_independent_hash_sets_iterator
from itertools import product, cycle, count, combinations, chain
from typing import Iterable, Tuple
from math import *


def get_number_from_bits(bits: Iterable[int]) -> int:
    return sum([bit * (2 ** i) for i, bit in enumerate(bits)])


def iterate_bit_vectors(bit_count: int) -> Iterable[Tuple[int, ...]]:
    return map(tuple, map(reversed, product([0, 1], repeat=bit_count)))


def xor_sum(bits: Iterable[int]) -> int:
    return sum(bits) % 2


if __name__ == "__main__":
    n = 2

    HS = uniform_pairwise_independent_hash_sets_iterator(2**n, 2**(n+1))

    T = []
    for H in HS:
        T.append(T)

    print(T)

"""
if __name__ == "__main__":
    # generates pairwise independent extension for the given hash set
    # by giving each hash two extensions which will be present in the generated hash set
    # thus maintaining the expected minimal size of pairwise independent hash sets

    n = 2
    HB = {(0, 0, 0, 1), (0, 0, 1, 0), (0, 1, 0, 1), (1, 0, 1, 1), (1, 1, 0, 0), (0, 1, 1, 0), (1, 0, 0, 0), (1, 1, 1, 1)}

    def double_extension_iterator(HB, n):
        # column extensions refer to the added output values along on input value for each hash
        # they are used since they can restrict the possible extensions since they need to
        # have the same amount of zeros as they have ones since otherwise for the input value
        # the extended hash wouldn't have Pr[h(x)=0] = 1/2 for uniform distributions
        col_extensions = [
            [1 if i in c else 0 for i in range(2**(n+1))] for c in
            map(set, combinations(range(2**(n+1)), 2**n))
        ]

        extensions = map(
            lambda rs: [tuple([row[i] for row in rs]) for i in range(2**(n+1))],
            product(col_extensions, repeat=2**n),
        )

        for e1 in extensions:
            for e2 in extensions:
                H = {
                    h + addition for h, addition in chain(zip(HB, e1), zip(HB, e2))
                }

                if len(H) == 2 * len(HB):
                    yield H

    for H in double_extension_iterator(HB, n):
        if is_pairwise_independent_hash_set(2**(n+1), H):
            print(H)
"""

"""
# Test for hashes that are extended one-to-one
if __name__ == "__main__":
    for (i, H5), (j, H6) in product(
        enumerate(uniform_pairwise_independent_hash_sets_D5), enumerate(uniform_pairwise_independent_hash_sets_D6)
    ):
        if all(any(all(h[i] == h2[i] for i in range(5)) for h2 in H6) for h in H5):
            print(i + 1, j + 1)
"""

"""
# Testing for possible arithmetic simplifications of the xor hash
if __name__ == "__main__":
    s = 2

    seq_0 = [0, 1]
    seq_1 = [1, 0]

    bit_vectors = list(iterate_bit_vectors(12))
    grouped_bit_vectors = [[bit_vectors[i * s + j] for j in range(s)] for i in range(int(len(bit_vectors) / s))]

    sequences = [[xor_sum(bit_vector) for bit_vector in group] for group in grouped_bit_vectors]

    for seq in sequences:
        print(1 if seq == seq_0 else 0)
"""

"""
Complement of XOR requires exponentially many bits to characterize thus
is not useable
if __name__ == "__main__":
    n = 30
    D = 2 ** n
    def xor_hs():
        return {
            tuple([
                b if xor_sum([x * y for x, y in zip(bit_vec, a)]) == 1 else 1 - b for bit_vec in iterate_bit_vectors(n)
            ]) for b in [0, 1] for a in iterate_bit_vectors(n)
        }

    a_xor_hs = xor_hs()
    # c_xor_hs = complement_hash_set(a_xor_hs)

    hs = a_xor_hs

    l = set()
    for h in hs:
        if inverse_hash(h) not in l:
            l.add(h)
            print(h)

    print(log2(2 ** D - len(hs)))
"""