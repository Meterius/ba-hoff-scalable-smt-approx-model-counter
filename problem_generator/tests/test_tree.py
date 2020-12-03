from problem_generator.tree import get_tree_model_count_upper_bound, convert_problem, collect_tree
from problem_generator.generator import generate_random_tree, generate_random_flat_tree
from alternatives.branching_counter import count_models_by_branching
import unittest


class TestTree(unittest.TestCase):
    def test_get_tree_model_upper_bound(self):
        for n in (1, 10):
            for i in range(50):
                root = generate_random_tree(n, 5)
                tree = collect_tree(root)
                cond, _, card_map = convert_problem((root, []))

                mc = count_models_by_branching(
                    cond,
                    [card_map[n] for n in tree],
                )

                self.assertLessEqual(
                    mc, get_tree_model_count_upper_bound(root),
                    msg="Upper bound should be upper bound"
                )

        for n in (1, 6):
            for max_nc in (1, 2):
                for min_nc in (0, 1, 2):
                    if min_nc <= max_nc:
                        for i in range(50):
                            root = generate_random_flat_tree(n, min_nc, max_nc)
                            tree = collect_tree(root)
                            cond, _, card_map = convert_problem((root, []))

                            mc = count_models_by_branching(
                                cond,
                                [card_map[n] for n in tree],
                            )

                            self.assertLessEqual(
                                mc, get_tree_model_count_upper_bound(root),
                                msg="Upper bound should be upper bound"
                            )
