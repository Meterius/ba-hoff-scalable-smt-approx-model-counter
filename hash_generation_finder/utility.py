from operator import itemgetter
from typing import Tuple
from math import log2, floor
import re
from itertools import product, chain, permutations
import numpy as np


def invert_hash(h):
    return tuple(1 - h[j] for j in range(len(h)))


def invert_hash_set(H):
    return 1 - convert_hash_set_to_numpy_representation(H)


def is_hash_symmetric(h) -> bool:
    return h == reversed(h)


def is_hash_set_symmetric(H) -> bool:
    return all(map(is_hash_symmetric, convert_hash_set_to_tuple_representation(H)))


def get_hash_set_dual_extender(H):
    pref_suff = {}

    HC = convert_hash_set_to_tuple_representation(H)
    for h in HC:
        pref = h[:floor(len(h) / 2)]
        suff = h[floor(len(h) / 2):]
        pref_suff[pref] = pref_suff.get(pref, []) + [suff]

    if all(map(lambda x: len(x) == 2, pref_suff.values())):
        return pref_suff
    else:
        return None


def get_hash_set_dual_paired_inverse_extender_identifier(H):
    pref_suff = get_hash_set_dual_extender(H)

    if pref_suff is None or not is_hash_set_dual_paired_inverse_extension(H):
        return None
    else:
        HE = set()

        for h1, h2 in pref_suff.values():
            if h1 not in HE:
                HE.add(h1)
            else:
                HE.add(h2)

        HE = convert_hash_set_to_tuple_representation(tuple(HE))

        return get_hash_set_identifier(HE)


def get_hash_set_dual_extender_identifier(H):
    pref_suff = get_hash_set_dual_extender(H)

    if pref_suff is None:
        return None
    else:
        return get_hash_set_identifier(
            convert_hash_set_to_tuple_representation(
                tuple(chain.from_iterable(pref_suff.values()))
            )
        )


def is_hash_set_dual_paired_inverse_extension(H) -> bool:
    HC = convert_hash_set_to_tuple_representation(H)
    pref_suff = get_hash_set_dual_extender(HC)

    return all(map(lambda pref: pref_suff[pref][0] == invert_hash(pref_suff[pref][1]), pref_suff.keys())) if pref_suff\
        else False


def is_hash_set_dual_self_paired_inverse_extension(H) -> bool:
    HC = convert_hash_set_to_tuple_representation(H)
    pref_suff = get_hash_set_dual_extender(HC)

    return all(map(
        lambda pref:
        pref_suff[pref][0] == invert_hash(pref_suff[pref][1]) and pref in pref_suff[pref]
        , pref_suff.keys())) if pref_suff \
        else False


def is_hash_set_dual_extension(H1, H2 = None) -> bool:
    """
    Returns whether H2 can be generated
    by making each hash in H1 into two
    separate hashes that are extensions
    of the hash

    (in tuple representation)
    ((0, 1, 0, 0), (0, 1, 1, 0), (1, 1, 0, 1), (1, 1, 1, 0)) is a possible dual extension of ((0, 1), (1, 1))
    """
    if H2:
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
    else:
        return get_hash_set_dual_extender(H1) is not None


def is_hash_set_permutable(H1, H2):
    return get_hash_set_permutation(H1, H2) is not None


def get_hash_set_permutation(H1, H2):
    perms = product(
        permutations(range(H1.shape[1])),
        permutations(range(H1.shape[0])),
    )

    for p in perms:
        if np.array_equal(H1[p[1], :][:, p[0]], H2):
            return p

    return None


def are_hash_sets_equal(H1, H2):
    return convert_hash_set_to_tuple_representation(H1) == convert_hash_set_to_tuple_representation(H2)


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
    if isinstance(H, np.ndarray):
        return H

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


def get_hash_set_from_identifier(ident):
    m = re.search("^D\[(.+)]C\[(.+)]N\[(.+)]$", ident)
    d = int(m.groups()[0], 10)
    c = int(m.groups()[1], 10)
    n = int(m.groups()[2], 16)
    ns = format(n, f"0{d*c}b")

    HC = convert_hash_set_to_tuple_representation(tuple([
        tuple([ns[i*d+(d-1-j)] == "1" for j in range(d)]) for i in range(c)
    ]))

    return convert_hash_set_to_numpy_representation(HC)
