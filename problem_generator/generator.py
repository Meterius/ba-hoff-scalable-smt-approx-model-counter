from z3 import *
import random
from typing import NamedTuple, List, Union, Tuple, Dict

TreeNode = NamedTuple("TreeNode", [("children", Tuple["TreeNode", ...]), ('id', str)])


ConstraintImplication = NamedTuple("ConstraintImplication", [("source", TreeNode), ("target", TreeNode)])


Constraint = Union[ConstraintImplication]


def collect_tree(root: TreeNode) -> List[TreeNode]:
    return [root] + [y for x in root.children for y in collect_tree(x)]


def generate_random_tree(n: int, cn: int, id: str = "0") -> TreeNode:
    if n < 1 or cn < 1:
        raise ValueError("n and cn need to be greater or equal 1")

    children_count = random.randint(1, min(cn, n - 1)) if n > 1 else 0

    children_node_count = [1 for i in range(children_count)]

    for i in range(n - 1 - children_count):
        children_node_count[random.randint(0, children_count - 1)] += 1

    children = tuple([generate_random_tree(x, cn, id + "-" + str(i)) for i, x in enumerate(children_node_count)])

    node = TreeNode(
        children=children,
        id=id,
    )

    return node


def generate_random_constraint(tree: List[TreeNode]) -> Constraint:
    return ConstraintImplication(
        source=tree[random.randint(0, len(tree) - 1)],
        target=tree[random.randint(0, len(tree) - 1)],
    )


def generate_random_problem() -> Tuple[List[TreeNode], List[Constraint]]:
    root = generate_random_tree(100, 5)
    tree = collect_tree(root)
    constraints = [generate_random_constraint(tree) for i in range(25)]

    return tree, constraints


def convert_problem(problem: Tuple[List[TreeNode], List[Constraint]]) -> Tuple[BoolRef, List[ArithRef]]:
    tree, constraints = problem

    node_cardinality_map: Dict[TreeNode, ArithRef] = {
        x: Int("cardinality_{x}".format(x=x)) for x in tree
    }

    def collect_tree_conditions(root: TreeNode) -> BoolRef:
        parent_child_conditions = [
            Implies(node_cardinality_map[child] > 0, node_cardinality_map[root] > 0) for child in root.children
        ] + [
            Implies(node_cardinality_map[root] == 0, node_cardinality_map[child] == 0) for child in root.children
        ]

        cardinality_condition = And(0 <= node_cardinality_map[root], node_cardinality_map[root] < 4)

        return And(
            parent_child_conditions
            + [cardinality_condition]
            + [collect_tree_conditions(child) for child in root.children]
        )

    def convert_constraint_condition(constraint: Constraint) -> BoolRef:
        return Implies(node_cardinality_map[constraint.source] > 0, node_cardinality_map[constraint.target] > 0)

    condition = And(collect_tree_conditions(tree[0]), And([convert_constraint_condition(c) for c in constraints]))

    return condition, list(node_cardinality_map.values())
