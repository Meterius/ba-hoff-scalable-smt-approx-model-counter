from itertools import count
from primes.generate_power_two_primes import is_probably_prime
import os


if __name__ == "__main__":
    code_dir = os.path.dirname(__file__)
    file_name = os.path.join(code_dir, "output", "suggested_power_two_primes.txt")

    x = 1
    with open(file_name, "w") as f:
        while True:
            p = next(filter(
                is_probably_prime,
                count(2**x),
            ))

            f.write(f"{x} {p}\n")

            print(f"For smallest prime >= 2**{x}, suggested prime: {p}; is {p-2**x} larger")

            x += 1
