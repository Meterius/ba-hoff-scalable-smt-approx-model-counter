from z3 import *
from math import comb
from itertools import combinations
from typing import NamedTuple, List, Union, Tuple, Dict


TreeNode = NamedTuple("TreeNode", [
    ("id", str),
    ("cardinality_range", Tuple[int, int]),
    ("children_selection_range", Tuple[int, int]),
    ("children", Tuple["TreeNode", ...]),
])


ConstraintImplication = NamedTuple("ConstraintImplication", [("source", TreeNode), ("target", TreeNode)])


Constraint = Union[ConstraintImplication]


def collect_tree(root: TreeNode) -> List[TreeNode]:
    return [root] + [y for x in root.children for y in collect_tree(x)]


def convert_problem(
    problem: Tuple[TreeNode, List[Constraint]],
) -> Tuple[BoolRef, List[ArithRef], Dict[TreeNode, ArithRef]]:
    root, constraints = problem
    tree = collect_tree(root)

    node_cardinality_map: Dict[TreeNode, ArithRef] = {
        x: Int("cardinality_{id}".format(id=x.id)) for x in tree
    }

    node_used_map: Dict[TreeNode, BoolRef] = {
        x: Bool("used_{id}".format(id=x.id)) for x in tree
    }

    def collect_tree_conditions(root: TreeNode) -> BoolRef:
        parent_child_conditions = [
            node_used_map[root] == (node_cardinality_map[root] > 0),
            node_cardinality_map[root] >= 0,
        ] + [
            Implies(node_used_map[child], node_used_map[root]) for child in root.children
        ] + [
            Implies(
                node_used_map[root],
                And([
                    child.cardinality_range[0] <= node_cardinality_map[child],
                    node_cardinality_map[child] <= child.cardinality_range[1],
                ])
            ) for child in root.children
        ] + ([
            Implies(
                node_used_map[root],
                And([
                    PbGe([(node_used_map[child], 1) for child in root.children], root.children_selection_range[0]),
                    PbLe([(node_used_map[child], 1) for child in root.children], root.children_selection_range[1]),
                ]),
            ),
        ] if len(root.children) > 0 else [])

        return And(
            parent_child_conditions
            + [collect_tree_conditions(child) for child in root.children]
        )

    def convert_constraint_condition(constraint: Constraint) -> BoolRef:
        return Implies(node_cardinality_map[constraint.source] > 0, node_cardinality_map[constraint.target] > 0)

    condition = And([
        And([
            root.cardinality_range[0] <= node_cardinality_map[root],
            node_cardinality_map[root] <= root.cardinality_range[1],
        ]),
        collect_tree_conditions(tree[0]),
        And([convert_constraint_condition(c) for c in constraints]),
    ])

    return simplify(condition), list(node_cardinality_map.values()), node_cardinality_map


def get_tree_model_count_upper_bound_with_required_root(root: TreeNode) -> int:
    if len(root.children) == 0:
        return root.cardinality_range[1]

    required = {child for child in root.children if child.cardinality_range[0] > 0}
    not_required = set(root.children).difference(required)

    t_required = tuple(required)
    t_not_required = tuple(not_required)

    child_upper_bounds = {
        child: get_tree_model_count_upper_bound_with_required_root(child) for child in root.children
    }

    max_child_upper_bound = max(child_upper_bounds.values())

    upper_bound = 0

    max_comb = 3

    for r in range(root.children_selection_range[0], root.children_selection_range[1] + 1):
        if r >= len(t_required):
            if r - len(t_required) <= max_comb or len(t_not_required) - (r - len(t_required)) <= max_comb:
                for combination in combinations(
                    t_not_required,
                    r - len(t_required)
                ):
                    selected_children = t_required + combination

                    selected_children_upper_bound = 1

                    for child in selected_children:
                        selected_children_upper_bound *= child_upper_bounds[child]

                    upper_bound += selected_children_upper_bound
            else:
                upper_bound += (max_child_upper_bound ** r) * comb(len(t_not_required), r - len(t_required))

    return upper_bound * root.cardinality_range[1]


def get_tree_model_count_upper_bound(root: TreeNode) -> int:
    return get_tree_model_count_upper_bound_with_required_root(root) + (1 if root.cardinality_range[0] == 0 else 0)


