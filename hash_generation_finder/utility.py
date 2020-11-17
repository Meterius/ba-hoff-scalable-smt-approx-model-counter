from typing import Tuple


def convert_hash_set_to_tuple_representation(H) -> Tuple[Tuple[int, ...], ...]:
    return tuple(sorted([tuple(H[:, i]) for i in range(H.shape[1])]))
