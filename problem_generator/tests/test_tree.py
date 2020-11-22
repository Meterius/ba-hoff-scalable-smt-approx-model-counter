from problem_generator.tree import get_tree_model_count, convert_problem, collect_tree
from problem_generator.generator import generate_random_tree
from alternatives.branching_counter import count_models_by_comparison_branching
import unittest


class TestTree(unittest.TestCase):
    def test_get_tree_model_count(self):
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

                self.assertEqual(
                    mc, get_tree_model_count(root),
                    msg="Model count should be correct"
                )
