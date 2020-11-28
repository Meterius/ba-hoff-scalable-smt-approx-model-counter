import random
from itertools import product
from math import *


def generate_mp_hash(n, m):
    rs = [random.randint(0, m) for i in range(n)]
    return lambda xs: sum([x * r for x, r in zip(xs, rs)]) % m


if __name__ == "__main__":
    n = 2
    m = 53

    test_set_size = int(m ** n / 2)

    p = sqrt(4 * m / test_set_size)
    test_set_expected_intersection_size = test_set_size / m

    print(p)
    print(p * test_set_expected_intersection_size)

    test_set_generations = 100
    test_set_hash_generations = 100

    test_set_iteration_intersection_sizes = []

    for i in range(test_set_generations):
        print(f"Iter {i}")

        test_set = set(random.sample(tuple(product(range(1, m), repeat=n)), k=test_set_size))

        print(f"Set generated")

        test_set_intersection_sizes = []

        for _ in range(test_set_hash_generations):
            h = generate_mp_hash(n, m)

            test_set_intersection_size = sum(map(lambda xs: 1 if h(xs) == 0 else 0, test_set))
            test_set_intersection_sizes.append(test_set_intersection_size)

        test_set_iteration_intersection_sizes.append(test_set_intersection_sizes)

    test_set_iteration_intersection_size_expectancy_deviations = [
        sum([
            abs(test_set_expected_intersection_size - size)
            for size in intersection_sizes
        ]) / len(intersection_sizes) for intersection_sizes in test_set_iteration_intersection_sizes
    ]

    print("-------")

    for dev in test_set_iteration_intersection_size_expectancy_deviations:
        print(dev)

    print("-------")

    total_dev = sum(test_set_iteration_intersection_size_expectancy_deviations) \
                / len(test_set_iteration_intersection_size_expectancy_deviations)

    print(total_dev)

    flat_sizes = [size for iter_sizes in test_set_iteration_intersection_sizes for size in iter_sizes]

    print(sum([
        1
        if abs(test_set_expected_intersection_size - size) >= p * test_set_expected_intersection_size
        else 0
        for size in flat_sizes
    ]) / len(flat_sizes))
