from hash_generation_finder.uniform_pairwise_independent_hash_sets import complement_hash_set, inverse_hash, reversed_hash
from itertools import product, cycle, count
from typing import Iterable, Tuple
from math import *


def get_number_from_bits(bits: Iterable[int]) -> int:
    return sum([bit * (2 ** i) for i, bit in enumerate(bits)])


def iterate_bit_vectors(bit_count: int) -> Iterable[Tuple[int, ...]]:
    return map(tuple, map(reversed, product([0, 1], repeat=bit_count)))


def xor_sum(bits: Iterable[int]) -> int:
    return sum(bits) % 2


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