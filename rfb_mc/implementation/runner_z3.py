import z3
from collections import Counter
from typing import NamedTuple, Optional, List, Tuple, Dict, cast
from math import ceil, log2
from hashed_model_counting_framework.eamp_hash_family import get_variable_domain_size_max_bits, \
    generate_partial_hash_parameters
from hashed_model_counting_framework.implementation.helper.z3_helper import clone_expression, deserialize_expression, \
    serialize_expression
from hashed_model_counting_framework.runner import RunnerBase
from hashed_model_counting_framework.types import Params, HBmcTask, HBmcResult

FormulaParamsZ3 = NamedTuple("FormulaParamsZ3", [("formula", z3.BoolRef), ("variables", List[z3.BitVecRef])])


class RunnerZ3(RunnerBase[FormulaParamsZ3]):
    def __init__(
        self,
        params: Params,
        formula_params: FormulaParamsZ3,
    ):
        super().__init__(params, formula_params)

        # maps q to a solver that has a q-times conjunction asserted
        self._solver_map: Dict[int, Tuple[z3.Solver, List[z3.BitVecRef]]] = {}

    def _get_solver(self, q: int) -> (z3.Solver, List[z3.BitVecRef]):
        """
        Returns the solver and cloned variables, of which the solver
        has the q-times conjunction of the formula asserted.
        """

        if q not in self._solver_map:
            formula_clone = clone_expression(self.formula_params.formula, q)

            variables = [
                cast(z3.BitVecRef, q_bv)
                for bv in self.formula_params.variables
                for q_bv in formula_clone.var_map[bv]
            ]

            # TODO: investigate performance of different configurations
            #  and allow for custom solver configurations
            solver = z3.Solver()
            solver.add(z3.And(formula_clone.clones))

            self._solver_map[q] = (solver, variables)

        return self._solver_map[q]

    @classmethod
    def assert_params_and_problem_params_compatible(
        cls,
        params: Params,
        formula_params: FormulaParamsZ3,
    ):
        formula_variable_counter = Counter([x.size() for x in formula_params.variables])
        assert formula_variable_counter == params.bit_width_counter, \
               "bit widths of the formula params must match bit widths of the params"

    def _z3_get_XJM_slices(self, xs: List[z3.BitVecRef], j: int) -> List[z3.BitVecRef]:
        slices = []
        slice_size = get_variable_domain_size_max_bits(j)

        queue = xs.copy()

        while len(queue) > 0:
            x = queue.pop(0)

            if x.size() >= slice_size:
                for i in range(x.size() // slice_size):
                    slices.append(
                        z3.Extract(i * slice_size + slice_size - 1, i * slice_size, x)
                    )

                if (x.size() // slice_size) * slice_size != x.size():
                    rem_slice_size = x.size() % slice_size
                    slices.append(
                        z3.ZeroExt(
                            slice_size - rem_slice_size,
                            z3.Extract(x.size() - 1, x.size() - rem_slice_size, x)
                        )
                    )
            else:
                slice_item = [x]

                while len(queue) > 0 and sum([y.size() for y in slice_item]) + queue[0].size() <= slice_size:
                    slice_item.append(queue.pop(0))

                slices.append(z3.Concat(slice_item) if len(slice_item) > 1 else slice_item[0])

        return slices

    def _z3_make_hash_from_HJ(self, xs: List[z3.BitVecRef], j: int) -> z3.BitVecRef:
        pj = self.p[j]

        # bit count for the operations that ensures each variable can be stored and
        # accommodate the value pj
        vbc = max(int(ceil(log2(pj + 1))), get_variable_domain_size_max_bits(j))

        # slices the variable s.t. each can is allowed for the domain specified by the partial hash
        slices = self._z3_get_XJM_slices(xs, j)
        # generates the random coefficients used for the hash
        a, b = generate_partial_hash_parameters(self.get_random_int, len(slices), pj)

        return z3.URem(
            z3.Sum([
                z3.ZeroExt(vbc - s.size(), s) * z3.BitVecVal(a[i], vbc) for i, s in enumerate(slices)
            ]) + z3.BitVecVal(b, vbc),
            pj
        )

    def _z3_make_hash_from_H(self, xs: List[z3.BitVecRef], c: Tuple[int, ...]) -> List[List[z3.BitVecRef]]:
        return [
            # repeat each j-th partial hash c[j] times, as the eamp hash family instructs
            [self._z3_make_hash_from_HJ(xs, j) for _ in range(c[j])]
            for j in range(len(c))
        ]

    def _z3_make_hash_equality_from_H(self, xs: List[z3.BitVecRef], c: Tuple[int, ...]) -> z3.BoolRef:
        h = self._z3_make_hash_from_H(xs, c)

        return z3.And([
            z3.And([h[j][i] == 0 for i in range(c[j])])
            for j in range(len(c))
        ])

    @staticmethod
    def _z3_bounded_model_count(solver: z3.Solver, variables: List[z3.ExprRef], u: int) -> Optional[int]:
        """
        If the solver assertions have less than u models that are distinct for the given variables it
        returns the exact model count, otherwise it returns None.
        :param solver:
        :param variables:
        :param u:
        """

        if u == 1:
            response = solver.check()

            if response == z3.unknown:
                raise RuntimeError("Solver responded with unknown")
            else:
                return None if response == z3.sat else 0

        solver.push()

        for i in range(u):
            response = solver.check()

            if response == z3.unknown:
                solver.pop()
                raise RuntimeError("Solver responded with unknown")
            elif response == z3.unsat:
                solver.pop()
                return i

            if i != u-1:
                m = solver.model()
                solver.add(z3.Or([x != m[x] for x in variables]))

        solver.pop()

        return None

    def hmbc(self, task: HBmcTask) -> HBmcResult:
        solver, variables = self._get_solver(task.q)

        # TODO: ensure solver stack is maintained correctly even on error

        solver.push()
        solver.add(
            self._z3_make_hash_equality_from_H(
                variables, task.c,
            )
        )

        # is None if solver has at least a models for q_bits
        bmc = self._z3_bounded_model_count(solver, variables, task.a)

        solver.pop()

        return HBmcResult(bmc=bmc)


SerializedFormulaParamsZ3 = NamedTuple(
    "SerializedFormulaParamsZ3",
    [("serialized_formula", str), ("serialized_variables", List[Tuple[str, int]])],
)


def serialize_formula_params_z3(formula_params: FormulaParamsZ3) -> SerializedFormulaParamsZ3:
    return SerializedFormulaParamsZ3(
        serialized_formula=serialize_expression(formula_params.formula),
        serialized_variables=[(str(x), x.size()) for x in formula_params.variables],
    )


def deserialize_formula_params_z3(
    serialized_formula_params: SerializedFormulaParamsZ3,
) -> FormulaParamsZ3:
    return FormulaParamsZ3(
        formula=cast(z3.BoolRef, deserialize_expression(serialized_formula_params.serialized_formula)),
        variables=[z3.BitVec(name, k) for name, k in serialized_formula_params.serialized_variables],
    )
