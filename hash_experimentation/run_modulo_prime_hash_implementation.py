from implementation.estimate_manager import EstimateBaseParams
from hash_experimentation.modulo_prime_hash_implementation import EstimateRunner, EstimateTask, EstimateProblemParams
from alternatives.exclusion_counter import count_models_by_exclusion
from time import perf_counter
import random
from math import *
from itertools import *
from z3 import *


def is_prime(x):
    for i in range(2, x):
        if x % i == 0:
            return False

    return True


def generate_primes():
    i = 2

    while True:
        if is_prime(i):
            yield i

        i += 1


def generate_ith_prime(n):
    for i, p in enumerate(generate_primes()):
        if i == n:
            return p


if __name__ == "__main__":
    p = generate_ith_prime(6)
    bc = int(ceil(log2(p)))

    print(f"Using Prime {p} {bc}")

    for xn in count(3):
        print(f"Running for {xn}")

        xs = [
            Int(f"x_{i}") for i in range(xn)
        ]

        bs = [
            BitVec(f"x_{i}", bc) for i in range(xn)
        ]

        f = And([
            And([And(p > x, x >= 1) for x in xs]),
            And([
                x * random.randint(1, p) % random.randint(1, p ** 2) < int(0.5 * p ** 2) for x in xs
            ]),
            And([BV2Int(bv) == x for x, bv in zip(xs, bs)])
        ])
        """
        f = And([
            And([And(UGT(p, x), UGE(x, 1)) for x in xs]),
            And([
                ULT(x * random.randint(1, p) % random.randint(1, p**2), int(0.5 * p ** 2)) for x in xs
            ])
        ])
        """

        # print(count_models_by_exclusion(f, xs))

        s1 = perf_counter()

        runner = EstimateRunner(
            base_params=EstimateBaseParams(
                a=1,
                q=1,
                bc=1,
                max_mc=None,
            ),
            problem_params=EstimateProblemParams(
                formula=f,
                variables=[(x, 1) for x in bs],
            ),
            r=p,
        )

        print(runner.params.g, runner.params.G)

        print(f"Initialize took {perf_counter() - s1:.3f} seconds")

        for m in count(1):
            s = perf_counter()
            task = EstimateTask(m=m)
            result = runner.estimate(task)
            print(f"Estimate for {task} {result} took {perf_counter()-s:.3f} seconds")

            if not result.positive_vote:
                break

        print(f"Finished, took {perf_counter()-s1:.3f} seconds")
