from typing import Iterable, Tuple, Set, TypeVar, List, Callable
from itertools import combinations, product, chain
import os


def count_iterations(iterable: Iterable) -> int:
    count = 0
    for _ in iterable:
        count += 1
    return count


def is_pairwise_independent_hash_set(D: int, H: Set[Tuple[int, ...]]) -> bool:
    a0_count_map = {a: 0 for a in range(D)}

    for a in range(D):
        a0_count_map[a] = count_iterations(h for h in H if h[a] == 0)

        if 2 * a0_count_map[a] != len(H):
            print(a)
            return False

    for (a, b) in combinations(range(D), 2):
        a0b0_count = count_iterations(h for h in H if h[a] == 0 and h[b] == 0)

        if 4 * a0b0_count != len(H):
            print(a, b, a0b0_count)
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


def hash_sets_iterator(D: int) -> Iterable[Set[Tuple[int, ...]]]:
    for H in powerset(hashes(D)):
        if len(H) > 0:
            yield H


def uniform_pairwise_independent_hash_sets_iterator(D):
    for H in hash_sets_iterator(D):
        if len(H) != 2 ** D and is_pairwise_independent_hash_set(D, H):
            yield H


def generate_and_store_uniform_pairwise_independent_hash_sets(D):
    hash_count = 2 ** D
    hash_set_count = 2 ** hash_count - 1

    k = 0

    code_dir = os.path.dirname(__file__)
    file_base = os.path.join(code_dir, "uniform_pairwise_independent_hash_sets", "D{D}".format(D=D))

    file_listed = file_base + "_listed.txt"
    file_exec = file_base + "_exec.py"

    print("Generating uniform pairwise independent hash sets for D={D}...".format(D=D))

    with open(file_listed, "w") as fl, open(file_exec, "w") as fe:
        fe.write("uniform_pairwise_independent_hash_sets_D{D} = []\n".format(D=D))

        for i, H in enumerate(hash_sets_iterator(D)):
            if i % 1000000 == 0:
                print(
                    "Iterated through {p:.2f}% ({i}/{hash_set_count}), found {k} upi hash sets so far"
                        .format(i=i, p=100 * i / hash_set_count, k=k, hash_set_count=hash_set_count)
                )

            if is_pairwise_independent_hash_set(D, H):
                fe.write("uniform_pairwise_independent_hash_sets_D{D}.append(".format(D=D))
                fe.write(repr(H))
                fe.write(")\n")

                fl.write(repr(H))
                fl.write("\n")

                k += 1

    print("Wrote executable data in {file_exec}".format(file_exec=file_exec))
    print("Wrote sets listed by line in {file_listed}".format(file_listed=file_listed))
    print("Finished for D={D}".format(D=D))


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

