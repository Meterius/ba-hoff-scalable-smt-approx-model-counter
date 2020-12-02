from z3 import *
from primes.generate_power_two_primes import is_prime
import os


if __name__ == "__main__":
    code_dir = os.path.dirname(__file__)
    file_in = os.path.join(code_dir, "output", "suggested_power_two_primes.txt")
    file_out = os.path.join(code_dir, "output", "verified_power_two_primes.txt")

    solver = SolverFor("QF_NIA")

    with open(file_in, "r") as fi, open(file_out, "w") as fo:
        for line in fi.readlines():
            xs, ps = line.split(" ")
            x = int(xs, 10)
            p = int(ps, 10)

            response = solver.check(Int("x") > 1, Int("x") < p, (p % Int("x")) == 0)

            if response == unknown:
                raise ValueError("Solver responded with unknown")

            pv = response == unsat

            if pv:
                fo.write(f"{x} {p}\n")
                print(f"For smallest prime >= 2**{x}, verified prime: {p}; is {p - 2 ** x} larger")
            else:
                print(f"DENIED: For smallest prime >= 2**{x}, suggested is not prime")
