from typing import Tuple


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


def convert_hash_set_to_tuple_representation(H) -> Tuple[Tuple[int, ...], ...]:
    return tuple(sorted([tuple(H[:, i]) for i in range(H.shape[1])]))
