import z3
import random
from implementation.estimate_manager import EstimateDerivedBaseParams, EstimateBaseParams,\
    assert_estimate_base_params_is_valid, EstimateTaskResult, EstimateTask
from implementation.helper import deserialize_expression, serialize_expression
from typing import NamedTuple, Optional, List, Tuple, Dict, cast
from math import ceil, log2, floor

EstimateProblemParams = NamedTuple(
    "EstimateProblemParams",
    [("formula", z3.BoolRef), ("variables", List[z3.BitVecRef])]
)
"""
The estimate problem specifies the data that is missing from the base params,
and is separated as it may be stored separately to the base params due to its
not directly serializable nature.

Specifically it specifies the formula and variables with their associated bit counts,
note that the sum of used bits for the variables needs to equal the bc param in the base params.

This data characterizes the model count and is expected to stay equivalent across an approx execution.
"""


def assert_estimate_problem_params_is_valid(problem_params: EstimateProblemParams):
    pass


def assert_estimate_problem_and_base_params_are_valid(
    problem_params: EstimateProblemParams,
    base_params: EstimateBaseParams,
):
    assert_estimate_base_params_is_valid(base_params)
    assert_estimate_problem_params_is_valid(problem_params)

    assert len(problem_params.variables) == base_params.n, "Amount of variables equals base params n"
    assert all([x.size() == base_params.k for x in problem_params.variables]), "Variables must have bit size of k"


Z3CloneExpressionOutput = NamedTuple("Z3CloneExpressionOutput", [
    ("clones", List[z3.BoolRef]), ("var_map", Dict[z3.ExprRef, List[z3.ExprRef]])
])


class EstimateRunner:
    """
    Implements estimate function.
    """

    def __init__(
        self,
        base_params: EstimateBaseParams,
        problem_params: EstimateProblemParams,
    ):
        self.params: EstimateDerivedBaseParams = EstimateDerivedBaseParams(base_params)
        self.problem_params: EstimateProblemParams = problem_params

        # Problem and base params compatibility check

        assert_estimate_problem_and_base_params_are_valid(problem_params, base_params)

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

    @staticmethod
    def _get_random_int(a: int, b: int) -> int:
        """
        Returns a random integer from the inclusive interval [a, b]
        """

        return random.randint(a, b)

    @staticmethod
    def _z3_get_hamming_weight(x: z3.BitVecRef) -> z3.ArithRef:
        return z3.Sum([
            z3.ZeroExt(
                int(ceil(log2(x.size()))),
                z3.Extract(i, i, x)
            )
            for i in range(x.size())
        ])

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

    def _z3_get_XJ(self, xs: List[z3.BitVecRef], j: int, m: int) -> z3.BitVecRef:
        i = int(floor(m / (2 ** j)))
        s = (m % (2 ** j)) * int(self.params.k / (2 ** j))
        t = s + int(self.params.k / (2 ** j)) - 1

        return z3.Extract(t, s, xs[i])

    def _z3_make_hash_from_HJ(self, xs: List[z3.BitVecRef], j: int) -> z3.BitVecRef:
        p = self.params.p[j]
        pbc = int(ceil(log2(p)))

        def get_random_coefficient():
            return z3.BitVecVal(self._get_random_int(0, p - 1), pbc)

        return z3.URem(
            z3.Sum([
                self._z3_get_XJ(xs, j, m) * get_random_coefficient() for m in range(self.params.n * (2 ** j))
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

    def exact_model_count_if_less_or_equal_t(self) -> Optional[int]:
        """
        If the formula has <= t models this will return the exact model count,
        otherwise it returns None.
        """

        return self._z3_limited_model_count(self._solver, self._q_bvs, self.params.t + 1)

    def estimate(self, task: EstimateTask) -> EstimateTaskResult:
        """
        Performs estimate from smt paper for the parameter m.
        Note: requires runner to be initialized
        :param task:
        """

        assert self.params.is_possible_c(task.c), "Estimate Task c must be a possible c"

        self._solver.push()
        self._solver.add(
            self._z3_make_hash_equality_from_H(
                self._q_bvs, task.c,
            )
        )

        # is None if solver has at least a models for q_bits
        lmc = self._z3_limited_model_count(self._solver, self._q_bvs, self.params.a)

        self._solver.pop()

        return EstimateTaskResult(positive_vote=lmc is None)


SerializedEstimateProblemParams = NamedTuple(
    "SerializedEstimateProblemParams",
    [("serialized_formula", str), ("serialized_variables", List[Tuple[str, int]])],
)


def serialize_estimate_problem_params(problem_params: EstimateProblemParams) -> SerializedEstimateProblemParams:
    return SerializedEstimateProblemParams(
        serialized_formula=serialize_expression(problem_params.formula),
        serialized_variables=[(str(x), x.size()) for x in problem_params.variables],
    )


def deserialize_estimate_problem_params(
    serialized_estimate_problem_params: SerializedEstimateProblemParams,
) -> EstimateProblemParams:
    return EstimateProblemParams(
        formula=cast(z3.BoolRef, deserialize_expression(serialized_estimate_problem_params.serialized_formula)),
        variables=[z3.BitVec(name, k) for name, k in serialized_estimate_problem_params.serialized_variables],
    )
