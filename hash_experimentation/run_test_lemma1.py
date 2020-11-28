import random
from itertools import *
from math import *


def make_prime_mod_is_zero_prob(r, n):
    return 1 / r


def make_prime_mod_domain(r, n):
    return product(range(1, r), repeat=n)


def make_prime_mod_hash(r, n):
    cs = [random.randint(1, r-1) for _ in range(n)]

    return lambda xs: sum([c * x for c, x in zip(cs, xs)]) % r


###


def make_bin_prime_mod_is_zero_prob(r, n):
    return 1/2


make_bin_prime_mod_domain = make_prime_mod_domain


def make_bin_prime_mod_hash(r, n):
    h = make_prime_mod_hash(r, n)
    return lambda xs: h(xs) % 2


##



##


make_domain = make_bin_prime_mod_domain
make_is_zero_prob = make_bin_prime_mod_is_zero_prob
generate_hash = make_bin_prime_mod_hash

if __name__ == "__main__":
    n = 2
    r = 17

    zpr = make_is_zero_prob(r, n)

    domain = list(make_domain(r, n))
    test_set_size = int(len(domain) / 2)

    p = sqrt(4 / (test_set_size * zpr))
    test_set_expected_intersection_size = test_set_size * zpr

    print(f"Zero Prob: {zpr}")
    print(f"Domain Size: {len(domain)}")
    print(f"Set size: {test_set_size}")
    print(f"Expected inter size: {test_set_expected_intersection_size}")
    print(f"Small Dev Size: {p * test_set_expected_intersection_size}")

    test_set_generations = 10000
    test_set_hash_generations = 100

    test_set_iteration_intersection_sizes = []

    for i in range(test_set_generations):
        print(f"Iter {i}")

        test_set = set(random.sample(domain, k=test_set_size))

        test_set_intersection_sizes = []

        for _ in range(test_set_hash_generations):
            h = generate_hash(r, n)

            test_set_intersection_size = sum(map(lambda xs: 1 if h(xs) == 0 else 0, test_set))
            test_set_intersection_sizes.append(test_set_intersection_size)

        test_set_iteration_intersection_sizes.append(test_set_intersection_sizes)

    # for sizes in test_set_iteration_intersection_sizes:
    #     for size in sizes:
    #         print(abs(test_set_expected_intersection_size - size))

    print("---")

    prs = []

    for sizes in test_set_iteration_intersection_sizes:
        pr = sum([
            1
            if abs(test_set_expected_intersection_size - size) >= p * test_set_expected_intersection_size
            else 0
            for size in sizes
        ]) / len(sizes)

        print("Prob of Large Dev for specific set:", pr)
        prs.append(pr)

    print("---")

    print("Max Large Dev Prob:", max([
        sum([
            1
            if abs(test_set_expected_intersection_size - size) >= p * test_set_expected_intersection_size
            else 0
            for size in sizes
        ]) / len(sizes)
        for sizes in test_set_iteration_intersection_sizes
    ]))

    print("---")

    print("Prob of Large Dev on average: ", sum(prs) / len(prs))
