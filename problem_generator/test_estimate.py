from time import perf_counter
from source_algo_implementation_binary_search_multi_processing_voters.approx import estimate
from source_algo_implementation_binary_search_multi_processing_voters.z3_helper import is_binary_encoding
from z3 import *

if __name__ == "__main__":
    for n in range(20, 40):
        s = Solver()
        x = Int("x")
        bits = [Bool("b_" + str(i)) for i in range(n)]
        s.add(x >= 0)
        s.add(x % 2 == 0)
        s.add(is_binary_encoding(x, bits))

        start = perf_counter()

        estimate(s, [x], bits, n, 1)

        d = perf_counter() - start
        print(n, d)