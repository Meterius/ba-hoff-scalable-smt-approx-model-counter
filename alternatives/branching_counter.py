from z3 import *
from typing import List, Iterable


def is_binary_encoding(x: ArithRef, bits: List[BoolRef]) -> BoolRef:
    return Sum([If(bits[i], 2 ** i, 0) for i in range(len(bits))]) == x


def count_models_by_boolean_branching(formula: BoolRef, variables: List[BoolRef]) -> int:
    # counts models by exploring the tree that is formed by partial assignments
    # which can cut off large subspaces that are unsatisfiable and imposes only
    # a small complexity increase on the formula which is making this method
    # way faster than counting by naive model exclusion

    mc = 0

    solver = Solver()
    solver.add(formula)

    def explore_branch(partial_assignment: List[bool]):
        nonlocal mc

        solver.push()
        solver.add(partial_assignment[-1] == variables[len(partial_assignment) - 1])

        if solver.check() == sat:
            if len(partial_assignment) == len(variables):
                mc += 1
            else:
                explore_branch(partial_assignment + [False])
                explore_branch(partial_assignment + [True])

        solver.pop()

    explore_branch([False])
    explore_branch([True])

    return mc


def iterate_models_by_boolean_branching(formula: BoolRef, variables: List[BoolRef]) -> Iterable[ModelRef]:
    # counts models by exploring the tree that is formed by partial assignments
    # which can cut off large subspaces that are unsatisfiable and imposes only
    # a small complexity increase on the formula which is making this method
    # way faster than counting by naive model exclusion

    mc = 0

    solver = Solver()
    solver.add(formula)

    queue = [[False], [True]]

    while len(queue) > 0:
        partial_assignment = queue.pop(0)

        if solver.check(And([variables[i] == partial_assignment[i] for i in range(len(partial_assignment))])) == sat:
            if len(partial_assignment) == len(variables):
                yield solver.model()
            else:
                queue.insert(0, partial_assignment + [False])
                queue.insert(0, partial_assignment + [True])

    return mc


def count_models_by_branching(formula: BoolRef, variables: List[BitVecRef]) -> int:
    bits = [Extract(i, i, x) == 1 for x in variables for i in range(x.size())]
    return count_models_by_boolean_branching(formula, bits)
