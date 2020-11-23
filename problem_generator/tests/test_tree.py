from problem_generator.tree import get_tree_model_count_upper_bound, convert_problem, collect_tree
from problem_generator.generator import generate_random_tree
from alternatives.branching_counter import count_models_by_comparison_branching
import unittest


class TestTree(unittest.TestCase):
    def test_get_tree_model_upper_bound(self):
        for n in (1, 10):
            for i in range(50):
                root = generate_random_tree(n, 5)
                tree = collect_tree(root)
                cond, _, card_map = convert_problem((root, []))

                mc = count_models_by_comparison_branching(
                    cond,
                    [card_map[n] for n in tree],
                    2,
                )

                self.assertLessEqual(
                    mc, get_tree_model_count_upper_bound(root),
                    msg="Upper bound should be upper bound"
                )
