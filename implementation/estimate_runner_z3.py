from collections import Counter

import z3
import random
from implementation.estimate_manager import EstimateBaseParams,\
    EstimateTaskResult, EstimateTask
from implementation.estimate_runner import BaseEstimateRunner
from implementation.helper import deserialize_expression, serialize_expression
from typing import NamedTuple, Optional, List, Tuple, Dict, cast
from math import ceil, log2

EstimateProblemParamsZ3 = NamedTuple(
    "EstimateProblemParamsZ3",
    [("formula", z3.BoolRef), ("variables", List[z3.BitVecRef])]
)


Z3CloneExpressionOutput = NamedTuple("Z3CloneExpressionOutput", [
    ("clones", List[z3.BoolRef]), ("var_map", Dict[z3.ExprRef, List[z3.ExprRef]])
])


class EstimateRunnerZ3(BaseEstimateRunner[EstimateProblemParamsZ3]):
    """
    Implements estimate function.
    """

    def __init__(
        self,
        base_params: EstimateBaseParams,
        problem_params: EstimateProblemParamsZ3,
    ):
        super().__init__(base_params, problem_params)

        # Problem and base params compatibility check

        self.assert_base_params_and_problem_params_compatible(base_params, problem_params)

        # Solver and formula initialization

        solver: z3.Solver = z3.Solver()

        formula = problem_params.formula
        variables = problem_params.variables

        formula_clone_data = self._z3_clone_expression(formula, self.params.q)

        q_bvs = [
            cast(z3.BitVecRef, q_bv)
            for bv in variables
            for q_bv in formula_clone_data.var_map[bv]
        ]

        # q times conjunction of clones of formula
        formula_q = z3.And(formula_clone_data.clones)

        solver.add(formula_q)

        self._solver: z3.Solver = solver
        self._q_bvs: List[z3.BitVecRef] = q_bvs

    @classmethod
    def assert_base_params_and_problem_params_compatible(
        cls,
        base_params: EstimateBaseParams,
        problem_params: EstimateProblemParamsZ3,
    ):
        assert dict(Counter([x.size() for x in problem_params.variables])) == base_params.km, \
               "Variables match base parameter km"

    @staticmethod
    def _get_random_int(a: int, b: int) -> int:
        """
        Returns a random integer from the inclusive interval [a, b]
        """

        return random.randint(a, b)

    @staticmethod
    def _z3_get_variables(expression: z3.ExprRef) -> List[z3.ExprRef]:
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

    @staticmethod
    def _z3_recreate_variable(key: str, variable: z3.ExprRef) -> z3.ExprRef:
        """
        Recreates the variable but renames it with a key that is used
        to make it distinct.
        :param key:
        :param variable:
        """

        return z3.Const(f"{key}_{variable}", variable.sort())

    @classmethod
    def _z3_clone_expression(cls, expression: z3.ExprRef, q: int) -> Z3CloneExpressionOutput:
        """
        Clones expression by generating q instances of the expression where each
        variable is substituted by a unique newly generated variable for each variable in each clone.
        The output will list each clone and a dictionary where each entry corresponds to
        a mapping from variable in the original formula to the substituted cloned variables for each clone
        listed in the same order as the clone list.
        :param expression: Expression to be cloned
        :param q: Amount of clones created
        """

        variables = cls._z3_get_variables(expression)

        var_map = {
            x: [cls._z3_recreate_variable(f"clone{{{i}}}", x) for i in range(q)] for x in variables
        }

        clones = [z3.substitute(expression, [(x, var_map[x][i]) for x in variables]) for i in range(q)]

        return Z3CloneExpressionOutput(
            clones=clones,
            var_map=var_map,
        )

    def _z3_get_XJM_slices(self, xs: List[z3.BitVecRef], j: int) -> List[z3.BitVecRef]:
        slices = []
        slice_size = int(ceil(self.params.kn / (2 ** j)))

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
                slice = [x]

                while len(queue) > 0 and sum([y.size() for y in slice]) + queue[0].size() <= slice_size:
                    slice.append(queue.pop(0))

                slices.append(z3.Concat(slice) if len(slice) > 1 else slice[0])

        return slices

    def _z3_make_hash_from_HJ(self, xs: List[z3.BitVecRef], j: int) -> z3.BitVecRef:
        p = self.params.p[j]
        pbc = int(ceil(log2(p)))

        def get_random_coefficient():
            return z3.BitVecVal(self._get_random_int(0, p - 1), pbc)

        slices = self._z3_get_XJM_slices(xs, j)

        return z3.URem(
            z3.Sum([
                z3.ZeroExt(pbc - s.size(), s) * get_random_coefficient() for s in slices
            ]) + get_random_coefficient(),
            self.params.p[j]
        )

    def _z3_make_hash_from_H(self, xs: List[z3.BitVecRef], c: Tuple[int, ...]) -> List[List[z3.BitVecRef]]:
        return [
            [self._z3_make_hash_from_HJ(xs, j) for _ in range(c[j])]
            for j in range(self.params.cn + 1)
        ]

    def _z3_make_hash_equality_from_H(self, xs: List[z3.BitVecRef], c: Tuple[int, ...]) -> z3.BoolRef:
        alpha = [
            [self._get_random_int(0, self.params.p[j] - 1) for _ in range(c[j])]
            for j in range(self.params.cn + 1)
        ]

        h = self._z3_make_hash_from_H(xs, c)

        return z3.And([
            z3.And([h[j][i] == alpha[j][i] for i in range(c[j])])
            for j in range(self.params.cn + 1)
        ])

    @staticmethod
    def _z3_limited_model_count(solver: z3.Solver, variables: List[z3.ExprRef], u: int) -> Optional[int]:
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

    def exact_model_count_if_less_or_equal_t(self, a: int) -> Optional[int]:
        """
        If the formula has <= t models this will return the exact model count,
        otherwise it returns None.
        """

        return self._z3_limited_model_count(self._solver, self._q_bvs, self.params.t(a) + 1)

    def estimate(self, task: EstimateTask) -> EstimateTaskResult:
        """
        Performs estimate from smt paper for the parameter m.
        Note: requires runner to be initialized
        :param task:
        """

        self.params.assert_is_possible_c(task.c, task.a)

        self._solver.push()
        self._solver.add(
            self._z3_make_hash_equality_from_H(
                self._q_bvs, task.c,
            )
        )

        # is None if solver has at least a models for q_bits
        lmc = self._z3_limited_model_count(self._solver, self._q_bvs, task.a)

        self._solver.pop()

        return EstimateTaskResult(lmc=lmc)


SerializedEstimateProblemParamsZ3 = NamedTuple(
    "SerializedEstimateProblemParamsZ3",
    [("serialized_formula", str), ("serialized_variables", List[Tuple[str, int]])],
)


def serialize_estimate_problem_params_z3(problem_params: EstimateProblemParamsZ3) -> SerializedEstimateProblemParamsZ3:
    return SerializedEstimateProblemParamsZ3(
        serialized_formula=serialize_expression(problem_params.formula),
        serialized_variables=[(str(x), x.size()) for x in problem_params.variables],
    )


def deserialize_estimate_problem_params_z3(
    serialized_estimate_problem_params: SerializedEstimateProblemParamsZ3,
) -> EstimateProblemParamsZ3:
    return EstimateProblemParamsZ3(
        formula=cast(z3.BoolRef, deserialize_expression(serialized_estimate_problem_params.serialized_formula)),
        variables=[z3.BitVec(name, k) for name, k in serialized_estimate_problem_params.serialized_variables],
    )
