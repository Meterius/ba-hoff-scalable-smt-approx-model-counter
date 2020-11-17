from math import *
from typing import Iterable, Tuple, Set, TypeVar, List, Callable, Collection
from itertools import combinations, product, chain, permutations
import os
import numpy as np


def count_iterations(iterable: Iterable) -> int:
    count = 0
    for _ in iterable:
        count += 1
    return count


def is_pairwise_independent_hash_set(D: int, H: Collection[Tuple[int, ...]]) -> bool:
    for a in range(D):
        if 2 *  sum([1 for h in H if h[a] == 1]) != len(H):
            return False

    for (a, b) in combinations(range(D), 2):
        for (x, y) in product([0, 1], repeat=2):
            a0b0_count = sum([1 for h in H if h[a] == y and h[b] == x])

            if 4 * a0b0_count != len(H):
                return False

    return True


def inverse_hash(h: Tuple[int, ...]) -> Tuple[int, ...]:
    return tuple([1 if y == 0 else 0 for y in h])


def inversed_hash_set(H: Set[Tuple[int, ...]]) -> Set[Tuple[int, ...]]:
    return {
        inverse_hash(h) for h in H
    }


def reversed_hash(h: Tuple[int, ...]) -> Tuple[int, ...]:
    return tuple(reversed(h))


def complement_hash_set(H: Set[Tuple[int, ...]]) -> Set[Tuple[int, ...]]:
    if len(H) == 0:
        raise ValueError("Hash set cannot be empty")

    D = len(next(iter(H)))

    return hashes(D).difference(H)


T = TypeVar("T")


def powerset(iterable: Iterable[T]) -> Iterable[Set[T]]:
    # powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)
    s = list(iterable)
    return map(set, chain.from_iterable(combinations(s, r) for r in range(len(s) + 1)))


def hashes(D: int) -> Set[Tuple[int, ...]]:
    """
    Returns set of all hashes on D
    """

    return set(map(tuple, product([0, 1], repeat=D)))


def hash_sets_iterator(D: int, k: int = 0) -> Iterable[Set[Tuple[int, ...]]]:
    for H in (powerset(hashes(D)) if k == 0 else map(set, combinations(hashes(D), k))):
        if len(H) > 0:
            yield H


def uniform_pairwise_independent_hash_sets_iterator(D, k):
    # generates independent hash functions faster by using numpy arrays and arithmetic
    # and generating only over possible candidates

    possible_column_count = factorial(k) / (factorial(int(k / 2)) * factorial(k - int(k / 2)))
    possible_columns = np.array([
        [1 if i in c else 0 for i in range(k)] for c in
        map(set, combinations(range(k), int(k / 2)))
    ], dtype=int)

    total = factorial(possible_column_count) / factorial(possible_column_count - D)

    print(possible_column_count)
    print("Theoretical candidates {0}".format(total))

    combs = tuple(combinations(range(D), 2))

    F = set()

    for i, ixs in enumerate(permutations(range(int(possible_column_count)), D)):
        H = possible_columns[np.array(ixs, dtype=int)]

        pairwise_independent = True

        if i % 1000000 == 0:
            print("{p:.2f}% ({i} out of {total})".format(p=100*i/total, total=total, i=i))

        for a, b in combs:
            coll = np.sum(H[a] * H[b])

            if coll * 4 != k:
                pairwise_independent = False
                break

        if pairwise_independent:
            CH = tuple(sorted(tuple(H[:, i]) for i in range(k)))
            if CH not in F:
                F.add(CH)
                yield CH


def generate_and_store_uniform_pairwise_independent_hash_sets(n, k):
    D = 2 ** n

    code_dir = os.path.dirname(__file__)
    file_base = os.path.join(code_dir, "output", "n{n}k{k}".format(n=n, k=k))

    file_listed = file_base + "_listed.txt"
    file_exec = file_base + "_exec.py"

    print("Generating uniform pairwise independent hash sets for n={n} k={k}...".format(n=n, k=k))

    with open(file_listed, "w") as fl, open(file_exec, "w") as fe:
        fe.write("uniform_pairwise_independent_hash_sets_D{D}_k{k} = []\n".format(D=D, k=k))

        for H in uniform_pairwise_independent_hash_sets_iterator(n, k):
            fe.write("uniform_pairwise_independent_hash_sets_D{D}_k{k}.append(".format(D=D, k=k))
            fe.write(repr(H))
            fe.write(")\n")

            fl.write(repr(H))
            fl.write("\n")

            k += 1

    print("Wrote executable data in {file_exec}".format(file_exec=file_exec))
    print("Wrote sets listed by line in {file_listed}".format(file_listed=file_listed))
    print("Finished for n={n} k={k}".format(n=n, k=k))


def find_transformed_hash_function_sets(
    HS: List[Set[Tuple[int, ...]]],
    transform: Callable[[Set[Tuple[int, ...]]], Set[Tuple[int, ...]]],
) -> List[Tuple[int, int]]:
    """
    Returns index pairs (starting at 1) of
    hash sets s.t. hash set 2 results from transforming hash set 1
    """

    THS = [transform(H) for H in HS]

    return [(a + 1, b + 1) for (a, b) in product(range(len(HS)), repeat=2) if HS[b] == THS[a]]


if __name__ == "__main__":
    for d in (6, 8, 9, 16, 32):
        generate_and_store_uniform_pairwise_independent_hash_sets(d)

    """
    uniform_pairwise_independent_hash_sets_D5 = []
    for i, H in enumerate(uniform_pairwise_independent_hash_sets_D5):
        if len({h for h in H if inverse_hash(h) in H}) == len(H) and len({h for h in H if inverse_hash(h) == h}) == 0:
            print(i + 1)
    """

    """
    for k in (2**3, 2**4, 2**5):
        print(k)
        for H in hash_sets_iterator(2**6, k):
            if is_pairwise_independent_hash_set(2**6, H):
                print("---")
                print(H)
                print("---")
    """

    """
    Testing of the k Subset Classifications hash
    D = 16
    only
    def hsk(k: int):
        return {
            tuple([a if x in K else 1 - a for x in range(D)]) for a in [0, 1] for K in map(set, combinations(range(D), k))
        }
    HS = hsk(6)
    print(HS)
    print(len(HS))
    print(is_pairwise_independent_hash_set(D, HS))

    for d in range(1, 100):
       generate_and_store_uniform_pairwise_independent_hash_sets(d)
    """

