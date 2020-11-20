from z3 import *
from random import choice
from typing import List, Union


def ref_estimate(solver: Solver, variables: List[ArithRef], bits: List[BoolRef], m: int, a: int) -> bool:
    def is_not_model(model: ModelRef) -> BoolRef:
        return Or([model[x] != x for x in variables])

    def limited_model_count() -> Union[int, None]:
        solver.push()

        for i in range(a):
            if solver.check() != sat:
                solver.pop()
                return i

            m = solver.model()
            solver.add(is_not_model(m))

        solver.pop()
        return None

    def xor_sum(bs: List[BoolRef]) -> BoolRef:
        if len(bs) == 0:
            return BoolVal(False)
        elif len(bs) == 1:
            return bs[0]
        else:
            return Xor(bs[0], xor_sum(bs[1:]))

    def random_bool_val() -> BoolRef:
        return choice((BoolVal(False), BoolVal(True)))

    def random_xor_hash() -> BoolRef:
        return Xor(
            random_bool_val(),
            xor_sum([And(random_bool_val(), bit) for bit in bits])
        )

    def random_xor_hash_equals_zero() -> BoolRef:
        return Not(random_xor_hash())

    def random_m_xor_hash_equals_zero() -> BoolRef:
        return And([random_xor_hash_equals_zero() for i in range(m)])

    solver.push()

    solver.add(random_m_xor_hash_equals_zero())
    has_at_least_a_models = limited_model_count() is None

    solver.pop()

    return has_at_least_a_models
