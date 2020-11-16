from itertools import product, cycle
from typing import Iterable, Tuple


def get_number_from_bits(bits: Iterable[int]) -> int:
    return sum([bit * (2 ** i) for i, bit in enumerate(bits)])


def iterate_bit_vectors(bit_count: int) -> Iterable[Tuple[int, ...]]:
    return map(tuple, map(reversed, product([0, 1], repeat=bit_count)))


def xor_sum(bits: Iterable[int]) -> int:
    return sum(bits) % 2


if __name__ == "__main__":
    s = 2

    seq_0 = [0, 1]
    seq_1 = [1, 0]

    bit_vectors = list(iterate_bit_vectors(12))
    grouped_bit_vectors = [[bit_vectors[i * s + j] for j in range(s)] for i in range(int(len(bit_vectors) / s))]

    sequences = [[xor_sum(bit_vector) for bit_vector in group] for group in grouped_bit_vectors]

    for seq in sequences:
        print(1 if seq == seq_0 else 0)
