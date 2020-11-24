from operator import itemgetter
from typing import Tuple
from math import log2, floor
from itertools import product, chain
import numpy as np


def invert_hash(h):
    return tuple(1 - h[j] for j in range(len(h)))


def is_hash_symmetric(h) -> bool:
    return h == reversed(h)


def is_hash_set_symmetric(H) -> bool:
    return all(map(is_hash_symmetric, convert_hash_set_to_tuple_representation(H)))


def is_hash_set_dual_extension(H1, H2) -> bool:
    """
    Returns whether H2 can be generated
    by making each hash in H1 into two
    separate hashes that are extensions
    of the hash

    (in tuple representation)
    ((0, 1, 0, 0), (0, 1, 1, 0), (1, 1, 0, 1), (1, 1, 1, 0)) is a possible dual extension of ((0, 1), (1, 1))
    """
    HC1 = convert_hash_set_to_tuple_representation(H1)
    HC2 = convert_hash_set_to_tuple_representation(H2)

    if len(HC2) != len(HC1) * 2:
        return False

    for h1 in HC1:
        c = 0

        for h2 in HC2:
            if h2[0:len(h1)] == h1:
                c += 1

                if c > 2:
                    return False

        if c != 2:
            return False

    return True


def get_hash_set_dual_extension_via_paired_inverses(H1, H2):
    HC1 = convert_hash_set_to_tuple_representation(H1)
    HC2 = convert_hash_set_to_tuple_representation(H2)

    H = tuple(
        HC1[i] + (invert_hash(HC2[i]) if a else HC2[i]) for a in [False, True] for i in range(len(HC1))
    )

    return convert_hash_set_to_numpy_representation(H)


def convert_hash_set_to_tuple_representation(H) -> Tuple[Tuple[int, ...], ...]:
    # ensures that convert tuple to tuple representation will return it sorted
    if type(H) == tuple:
        H = convert_hash_set_to_numpy_representation(H)

    hash_list = [tuple(map(int, H[:, i])) for i in range(H.shape[1])]

    sorted_hash_list = tuple(map(itemgetter(0), sorted([
        (h, sum([int(h[i]) * (2**(len(h)-i-1)) for i in range(len(h))])) for h in hash_list
    ], key=itemgetter(1))))

    return sorted_hash_list


def convert_hash_set_to_numpy_representation(H):
    D = len(H[0])

    return np.array([
         [h[j] for h in H] for j in range(D)
    ])


def convert_hash_set_to_bit_table(H):
    H = convert_hash_set_to_tuple_representation(H)

    bc = int(log2(len(H[0])))

    if bc != log2(len(H[0])):
        raise ValueError("Hash domain is not power of two")

    header_size = 5

    table = [" " * header_size + "|"]

    for vec in product([0,1], repeat=bc):
        table[0] += " " + "".join(map(str, vec)) + " |"

    for i, h in enumerate(H):
        line = " " + str(i+1).ljust(header_size - 1) + "|"

        for k in range(2**bc):
            line += " " * floor(bc / 2) + str(h[k]) + " " * (bc - floor(bc / 2) + 1) + "|"

        table.append(line)

    return table


def get_hash_set_identifier(H):
    HC = convert_hash_set_to_tuple_representation(H)

    D = len(HC[0])
    C = len(H)
    N = sum(map(lambda x: x[1]*2**x[0], enumerate(chain.from_iterable(HC))))

    return f"D[{D}]C[{C}]N[{N:X}]"
