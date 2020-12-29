from hashed_model_counting_framework.eamp_hash_family.primes import get_smallest_prime_above_or_equal_power_of_two
from math import prod, log2, ceil, floor
from typing import Tuple, Counter, Callable, List


"""
This module contains code related to the
extended addition modulo prime hash family.
"""


# TODO: improve readability and modularity of eamp hash family
# TODO: refactor eamp module


def get_cn(bit_width_counter: Counter[int]) -> int:
    """
    Returns the amount of entries in c required to allow a range that
    is greater than the maximum possible model count.
    """

    # for the range size to exceed the possible model count
    # we need t >= log2(bc), thus the smallest t = ceil(log2(bc))
    bc = sum(bit_width_counter.values())
    return int(ceil(log2(bc)))


def get_p(cn: int) -> Tuple[int, ...]:
    """
    Returns the primes used for the partial hashes in the hash family
    that has at most cn entries in c.
    """

    return tuple([
        get_smallest_prime_above_or_equal_power_of_two(
            2 ** i
        ) for i in range(cn)
    ])


def get_range_size(c: Tuple[int, ...]) -> int:
    """
    Returns the size of the range of the hash family for
    the given c parameter.
    """

    p = get_p(len(c))
    return prod([p[i] ** c[i] for i in range(len(c))])


def get_variable_domain_size(j: int) -> int:
    """
    Returns the maximal number a variable in the
    j-th partial hash can have.
    """

    return get_p(j + 1)[j] - 1


def get_variable_domain_size_max_bits(j: int) -> int:
    """
    Returns the maximum amount of bits a variable in the j-th
    partial hash can have.
    """

    return int(floor(log2(get_variable_domain_size(j) + 1)))


def generate_partial_hash_parameters(
    generate_random_int: Callable[[int, int], int],
    variable_count: int,
    pj: int,
) -> Tuple[List[int], int]:
    """
    Generates the parameters for a partial hash.
    It returns in the following format ([a[0], ..., a[variable_count]], b) where
    the corresponding partial hash is h(x) = (sum([x[i] * a[i] for i in range(variable_count)]) + b) % pj.
    """

    return (
        [generate_random_int(0, pj - 1) for _ in range(variable_count)],
        generate_random_int(0, pj - 1)
    )