from z3 import *
from typing import NamedTuple, List, Dict, Optional, Union
from random import choice


# Returns all variables contained in the expression
def get_variables(expression: z3.ExprRef) -> List[z3.ExprRef]:
    class AstRefKey:
        def __init__(self, n):
            self.n = n

        def __hash__(self):
            return self.n.hash()

        def __eq__(self, other):
            return self.n.eq(other.n)

        def __repr__(self):
            return str(self.n)

    def askey(n):
        assert isinstance(n, z3.AstRef)
        return AstRefKey(n)

    r = set()

    def collect(f):
        if z3.is_const(f):
            if f.decl().kind() == z3.Z3_OP_UNINTERPRETED and not askey(f) in r:
                r.add(askey(f))
        else:
            for c in f.children():
                collect(c)

    collect(expression)
    return [elem.n for elem in r]


def is_binary_encoding(x: ArithRef, bits: List[BoolRef]) -> BoolRef:
    """
    Returns boolean expression of whether the `bits` are
    an unsigned binary encoding of `x`, where `bits[i]` is
    numerically representing 2 ** i

    :param x:
    :param bits:
    """

    return Sum([If(bits[i], 2 ** i, 0) for i in range(len(bits))]) == x


def is_not_model(model: ModelRef, variables: Optional[List[ExprRef]] = None) -> BoolRef:
    """
    Returns boolean expression of whether the `variables` are not equal to
    their values in the `model` i.e. whether at least one variable is unequal to
    its `model` value.

    :param model: Model
    :param variables: Variables, defaults to all variables contained in the model
    """

    variables = variables or [x_decl() for x_decl in model]
    return Or([model[x] != x for x in variables])


def xor_sum(bs: List[BoolRef]) -> BoolRef:
    """
    Returns xor sum i.e. sum via addition modulo 2 over `bs`

    :param bs: Boolean expressions that are summed
    """

    if len(bs) == 0:
        return BoolVal(False)
    elif len(bs) == 1:
        return bs[0]
    else:
        return Xor(bs[0], xor_sum(bs[1:]))


def random_bool_val() -> BoolRef:
    """
    Returns boolean value of True or False uniformly randomly
    """
    return choice((BoolVal(False), BoolVal(True)))


class CloneFormulaReturn(NamedTuple):
    # clones of formula with distinct variables to each other and the formula
    clone_formulas: List[BoolRef]
    # map from variable in formula to substitution variables in clone formulas
    clone_vars_map: Dict[ExprRef, List[ExprRef]]


def clone_formula(formula: BoolRef, q: int) -> CloneFormulaReturn:
    """
    Returns dict containing q clones of the formula
    for which each clone has distinct substitution variables
    corresponding to the variables in the formula

    :param formula:
    :param q:
    """

    variables = get_variables(formula)

    clone_vars_map: Dict[ExprRef, List[ExprRef]] = {
        # distinct substitutions for each variable in the formulas
        x: [
            # distinct substitution for x in j-th clone
            Const("clone({j})_{x}".format(x=x, j=j), x.sort()) for j in range(q)
        ] for i, x in enumerate(variables)
    }

    clone_formulas: List[BoolRef] = [
        # clone formula by substituting the variables by their clone substitutions
        substitute(formula, [(x, clone_vars_map[x][j]) for x in variables]) for j in range(q)
    ]

    return CloneFormulaReturn(clone_formulas=clone_formulas, clone_vars_map=clone_vars_map)


def limited_model_count(solver: Solver, variables: List[ExprRef], a: int) -> Union[int, None]:
    """
    If the assertions of the solver have less than `a` models,
    it returns the exact model count.

    If the assertions of the solver have `a` or more models,
    it returns None.

    Note the models are counted only regarding the given `variables`
    i.e. a model is only distinct if one of the given `variables` are distinct
    in it.

    :param solver: Solver that has already the formula asserted
    :param variables: Variables for which models are counted
    :param a:
    :return:
    """

    solver.push()

    for i in range(a):
        if solver.check() != sat:
            solver.pop()
            return i

        m = solver.model()
        solver.add(is_not_model(m, variables))

    solver.pop()
    return None
