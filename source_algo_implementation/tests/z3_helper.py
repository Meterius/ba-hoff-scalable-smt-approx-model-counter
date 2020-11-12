from z3 import *
from itertools import product
import unittest
import random
import source_algo_implementation.z3_helper as z3_helper


class TestZ3Helper(unittest.TestCase):
    def setUp(self):
        self.solver = Solver()

    def test_is_binary_encoding(self):
        x = Int("x")

        for bit_count in (2, 10, 20):
            bits = [Bool("bit_{i}".format(i=i)) for i in range(bit_count)]

            for val in [0, random.randint(1, 2 ** bit_count - 2), 2 ** bit_count - 1]:
                cond = And(x == val, z3_helper.is_binary_encoding(x, bits))
                self.assertEqual(self.solver.check(cond), sat, "There exists a binary encoding for valid values")
                m = self.solver.model()
                b_val = sum([(2 ** i if m[bit] else 0) for i, bit in enumerate(bits)])
                self.assertEqual(b_val, val, "Binary encoding should be correct for valid values")

            for val in [-41323, -1, 2 ** bit_count, 2 ** bit_count + 5432]:
                cond = And(x == val, z3_helper.is_binary_encoding(x, bits))
                self.assertEqual(
                    self.solver.check(cond),
                    unsat,
                    "There does not exist a binary encoding for invalid values"
                )

    def test_is_not_model(self):
        x, y, z = Ints("x y z")

        models = [{
            x: val_x,
            y: val_y,
            z: val_z,
        } for val_x in (-5, 0, 1, 100) for val_y in (50, 100) for val_z in (1, 2, 3)]

        formula = Or([And([x == m[x], y == m[y], z == m[z]]) for m in models])

        found_models = []

        self.solver.push()
        self.solver.add(formula)

        while self.solver.check() == sat:
            m = self.solver.model()
            found_models.append(m)
            self.solver.add(z3_helper.is_not_model(m, [x, y]))

        self.solver.pop()

        self.assertListEqual(
            [(m1, m2) for m1, m2 in product(found_models, repeat=2) if m1[x] == m2[x] and m1[y] == m2[y] and m1 != m2],
            [],
            "Excluding models iteratively will not result in models that are non-distinct with respect"
            " to the variables",
        )

        for m1 in models:
            self.assertEqual(
                len([m2 for m2 in found_models if m1[x] == m2[x] and m1[y] == m2[y] and m1 != m2]),
                1,
                "Excluding models iteratively will result in each model having exactly one distinct model"
                " in the found models with respect to the variables"
            )

    def test_xor_sum(self):
        self.assertEqual(
            self.solver.check(z3_helper.xor_sum([])),
            unsat,
            "Empty xor sum should be False"
        )

        for n in (1, 5, 10):
            bits = [Bool("bit_{i}".format(i=i)) for i in range(n)]

            # all bit assignments that should satisfy a xor sum
            models = set([tuple([val == 1 for val in comb]) for comb in product([0, 1], repeat=n) if sum(comb) % 2 == 1])

            self.solver.push()
            self.solver.add(z3_helper.xor_sum(bits))

            found_models = set()
            while self.solver.check() == sat:
                m = self.solver.model()
                found_models.add(tuple([bool(m[bit]) for bit in bits]))
                self.solver.add(z3_helper.is_not_model(m))

            self.solver.pop()

            self.assertEqual(
                found_models,
                models,
                "Models of xor sum should be correct"
            )

    def test_random_xor_hash(self):
        c = 1000

        for n in (2, 5):
            bits = [Bool("bit_{i}".format(i=i)) for i in range(n)]
            assignments = tuple(map(tuple, product((False, True), repeat=n)))

            value_map = {
                a: [] for a in assignments
            }

            for k in range(c):
                self.solver.push()
                self.solver.add(z3_helper.random_xor_hash(bits))

                for a in assignments:
                    value_map[a].append(
                        self.solver.check(
                            And([bit == a[i] for i, bit in enumerate(bits)])
                        ) == sat
                    )

                self.solver.pop()

            average_is_true_proportion = 0
            for a in assignments:
                is_true_proportion = sum(value_map[a]) / c
                average_is_true_proportion += is_true_proportion

                self.assertAlmostEqual(
                    is_true_proportion,
                    1/2,
                    delta=0.1,
                    msg="Probability that hash equals value for given assignment is 1/2",
                )

            average_is_true_proportion /= len(assignments)

            self.assertAlmostEqual(
                average_is_true_proportion,
                1/2,
                delta=0.025,
                msg="Probability that hash equals value for given assignment is 1/2 (when averaged)"
            )

            average_are_equal_proportion = 0

            for i, (a1, a2) in enumerate(product(assignments, repeat=2)):
                if a1 != a2:
                    for ra1, ra2 in product((False, True), repeat=2):
                        are_equal_proportion = sum([
                            1 for i in range(c) if value_map[a1][i] == ra1 and value_map[a2][i] == ra2
                        ]) / c
                        average_are_equal_proportion += are_equal_proportion

                        self.assertAlmostEqual(
                            are_equal_proportion,
                            1/4,
                            delta=0.1,
                            msg="Probability that two assignments equal specific values is (1/2)^2 i.e. 1/4"
                        )

            average_are_equal_proportion /= ((len(assignments) ** 2) - len(assignments)) * 4

            self.assertAlmostEqual(
                average_are_equal_proportion,
                1 / 4,
                delta=0.01,
                msg="Probability that two assignments equal specific values is (1/2)^2 i.e. 1/4 (averaged)"
            )
