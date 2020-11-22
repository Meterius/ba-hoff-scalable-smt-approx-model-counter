import random
from problem_generator.tree import TreeNode, Constraint, collect_tree, ConstraintImplication
from typing import List, Tuple


def generate_random_tree(
    n: int,
    cn: int,
    id: str = "0",
) -> TreeNode:
    if n < 1 or cn < 1:
        raise ValueError("n and cn need to be greater or equal 1")

    children_count = random.randint(1, min(cn, n - 1)) if n > 1 else 0

    children_node_count = [1 for i in range(children_count)]

    for i in range(n - 1 - children_count):
        children_node_count[random.randint(0, children_count - 1)] += 1

    children = tuple([generate_random_tree(x, cn, id + "-" + str(i)) for i, x in enumerate(children_node_count)])

    node = TreeNode(
        id=id,
        cardinality_range=(random.randint(0, 1), 2),
        children_selection_range=(random.randint(0, 1), random.randint(1, 2)),
        children=children,
    )

    return node


def generate_random_constraint(tree: List[TreeNode]) -> Constraint:
    return ConstraintImplication(
        source=tree[random.randint(0, len(tree) - 1)],
        target=tree[random.randint(0, len(tree) - 1)],
    )


def generate_random_problem(
    n: int, max_children: int, constraint_count: int,
) -> Tuple[List[TreeNode], List[Constraint]]:
    root = generate_random_tree(n, max_children)
    tree = collect_tree(root)
    constraints = [generate_random_constraint(tree) for i in range(constraint_count)]

    return tree, constraints

