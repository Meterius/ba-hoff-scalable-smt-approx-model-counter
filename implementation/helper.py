import z3
from typing import Optional


def serialize_expression(expression: z3.ExprRef) -> str:
    s = z3.Solver()
    s.add(expression)
    return s.sexpr()


def deserialize_expression(serialized_expression: str, ctx: Optional[z3.Context] = None) -> z3.ExprRef:
    return z3.parse_smt2_string(serialized_expression, ctx=ctx)[0]
