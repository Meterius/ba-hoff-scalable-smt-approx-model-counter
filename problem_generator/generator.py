import random
from problem_generator.tree import TreeNode, Constraint, collect_tree, ConstraintImplication
from typing import List


def generate_random_tree(
    n: int,
    cn: int,
    ident: str = "0",
) -> TreeNode:
    if n < 1 or cn < 1:
        raise ValueError("n and cn need to be greater or equal 1")

    children_count = random.randint(1, min(cn, n - 1)) if n > 1 else 0

    children_node_count = [1 for _ in range(children_count)]

    for i in range(n - 1 - children_count):
        children_node_count[random.randint(0, children_count - 1)] += 1

    children = tuple([generate_random_tree(x, cn, ident + "-" + str(i)) for i, x in enumerate(children_node_count)])

    node = TreeNode(
        id=ident,
        cardinality_range=(0, random.randint(1, 2)),
        children_selection_range=(random.randint(0, 1), random.randint(1, 4)),
        children=children,
    )

    return node


def generate_random_flat_tree(
    root_child_count: int,
    min_child_child_count: int,
    max_child_child_count: int,
) -> TreeNode:
    def gen_child(i: int):
        return TreeNode(
            id=f"0-{i}",
            cardinality_range=(1, 1),
            children_selection_range=(1, 1),
            children=tuple([
                TreeNode(
                    id=f"0-{i}-{j}",
                    cardinality_range=(0, 1),
                    children_selection_range=(0, 0),
                    children=tuple(),
                ) for j in range(random.randint(min_child_child_count, max_child_child_count))
            ])
        )

    return TreeNode(
        id="0",
        cardinality_range=(1, 1),
        children_selection_range=(1, root_child_count),
        children=tuple([gen_child(i) for i in range(root_child_count)]),
    )


def generate_random_constraint(tree: List[TreeNode]) -> Constraint:
    return ConstraintImplication(
        source=tree[random.randint(0, len(tree) - 1)],
        target=tree[random.randint(0, len(tree) - 1)],
    )


def generate_random_constraints(root: TreeNode, count: int) -> List[Constraint]:
    tree = collect_tree(root)
    return [
        generate_random_constraint(tree) for _ in range(count)
    ]
