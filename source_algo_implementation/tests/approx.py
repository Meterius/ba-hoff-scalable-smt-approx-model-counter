from z3 import *
from math import sqrt
from itertools import chain
import unittest
import random
import source_algo_implementation.z3_helper as z3_helper
import source_algo_implementation.approx as approx


class TestApprox(unittest.TestCase):
    def setUp(self):
        self.solver = Solver()

    def test_estimate(self):
        c = 1000

        for n in (1, 4):
            x, y = Ints("x y")
            bits_x, bits_y = [Bool("bit_x_{i}".format(i=i)) for i in range(n)],\
                             [Bool("bit_y_{i}".format(i=i)) for i in range(n)]
            ux, uy = random.randint(0, 2 ** n), random.randint(0, 2 ** n)

            self.solver.push()
            self.solver.add(
                And([
                    z3_helper.is_binary_encoding(x, bits_x),
                    z3_helper.is_binary_encoding(y, bits_y),
                    x < ux,
                    y < uy,
                ])
            )

            model_count = ux * uy

            for m in range(1, n + 1):
                for a in (1, 10, 100):
                    g = (sqrt(a + 1) - 1) ** 2
                    G = (sqrt(a + 1) + 1) ** 2

                    estimate_wrong_proportion = 0

                    for i in range(c):
                        if approx.estimate(
                            self.solver, [x, y], list(chain(bits_x, bits_y)), m, a,
                        ):
                            estimate_wrong_proportion += 1 if model_count <= (2 ** m) * g else 0
                        else:
                            estimate_wrong_proportion += 1 if model_count >= (2 ** m) * G else 0

                    estimate_wrong_proportion /= c

                    self.assertLessEqual(
                        estimate_wrong_proportion,
                        1/4,
                        "Probability of estimate being wrong is less or equal 1/4",
                    )

            self.solver.pop()
