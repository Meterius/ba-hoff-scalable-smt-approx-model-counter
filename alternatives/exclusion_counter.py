from z3 import *
from typing import List


def is_not_model(model: ModelRef, variables: List[ExprRef]) -> BoolRef:
    return Or([model[x] != x for x in variables])


def count_models_by_exclusion(formula: BoolRef, variables: List[ArithRef]) -> int:
    solver = Solver()
    solver.add(formula)

    mc = 0
    while solver.check() == sat:
        solver.add(is_not_model(solver.model(), variables))
        mc += 1

    return mc
