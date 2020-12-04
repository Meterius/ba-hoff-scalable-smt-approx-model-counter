import z3
from typing import Optional, List


def serialize_expression(expression: z3.ExprRef) -> str:
    s = z3.Solver()
    s.add(expression)
    return s.sexpr()


def deserialize_expression(serialized_expression: str, ctx: Optional[z3.Context] = None) -> z3.ExprRef:
    return z3.parse_smt2_string(serialized_expression, ctx=ctx)[0]


def get_variables(expression: z3.ExprRef) -> List[z3.ExprRef]:
    """
    Returns all variables that are contained in the expression.
    :param expression: Expression from which variables are extracted
    """

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

    variables = set()

    def collect(f):
        if z3.is_const(f):
            if f.decl().kind() == z3.Z3_OP_UNINTERPRETED and not askey(f) in variables:
                variables.add(askey(f))
        else:
            for c in f.children():
                collect(c)

    collect(expression)
    return [elem.n for elem in variables]
