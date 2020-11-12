from z3 import *
from typing import List


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


def count_models_by_branching(formula: BoolRef, variables: List[ArithRef], bit_count: int) -> int:
    # convert the formula into a boolean formula that can be branched via boolean branching
    bits_map = {
        x: [Bool("bit_{x}_{i}".format(x=x, i=i)) for i in range(bit_count)] for x in variables
    }
    formula_e = And(formula, And([is_binary_encoding(x, bits_map[x]) for x in variables]))

    # reverse bit ordering to allow for easier simplifications internally for the solver
    bits = [bit for x in variables for bit in bits_map[x]]
    bits.reverse()

    return count_models_by_boolean_branching(formula_e, bits)


def count_models_by_comparison_branching(formula: BoolRef, variables: List[ArithRef], bit_count: int) -> int:
    # like count_models_by_branching but instead of transforming the formula into a boolean formula
    # implementing the equivalent behaviour but directly via ordering branching which
    # is minimally faster

    mc = 0

    solver = Solver()
    solver.add(formula)

    def explore_branch(partial_assignment: List[List[bool]]):
        nonlocal mc

        partial_var_assignment = partial_assignment[-1]
        partial_var_assignment_val = sum([
            2 ** (bit_count - i - 1)
            if bit or i == len(partial_var_assignment) - 1 else
            0 for i, bit in enumerate(partial_var_assignment)
        ])

        solver.push()
        solver.add(
            variables[len(partial_assignment) - 1] >= partial_var_assignment_val
            if partial_var_assignment[-1] else
            variables[len(partial_assignment) - 1] < partial_var_assignment_val
        )

        if solver.check() == sat:
            if len(partial_assignment) == len(variables) and len(partial_var_assignment) == bit_count:
                mc += 1
            else:
                explore_branch(
                    partial_assignment + [[True]]
                    if len(partial_var_assignment) == bit_count else
                    partial_assignment[:-1] + [partial_var_assignment + [True]]
                )
                explore_branch(
                    partial_assignment + [[False]]
                    if len(partial_var_assignment) == bit_count else
                    partial_assignment[:-1] + [partial_var_assignment + [False]]
                )

        solver.pop()

    explore_branch([[False]])
    explore_branch([[True]])

    return mc
