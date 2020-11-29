import z3
import random
from implementation.estimate_manager import EstimateDerivedBaseParams, EstimateBaseParams,\
    assert_estimate_base_params_is_valid, EstimateTaskResult, EstimateTask
from implementation.helper import deserialize_expression, serialize_expression
from typing import NamedTuple, Optional, List, Tuple, Dict, cast
from math import ceil, log2

EstimateProblemParams = NamedTuple(
    "EstimateProblemParams",
    [("formula", z3.BoolRef), ("variables", List[Tuple[z3.ArithRef, int]])]
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
    for x, bc in problem_params.variables:
        assert bc > 0, "Each problem variable has a positive bit count"


def assert_estimate_problem_and_base_params_are_valid(
    problem_params: EstimateProblemParams,
    base_params: EstimateBaseParams,
):
    assert_estimate_base_params_is_valid(base_params)
    assert_estimate_problem_params_is_valid(problem_params)

    assert sum([bc for x, bc in problem_params.variables]) == base_params.bc, \
        "Amount of bits in problem variables equals base params bit count"


Z3CloneExpressionOutput = NamedTuple("Z3CloneExpressionOutput", [
    ("clones", List[z3.BoolRef]), ("var_map", Dict[z3.ExprRef, List[z3.ExprRef]])
])


class ReferenceEstimateRunner:
    """
    Implements estimate function.
    """

    def __init__(
        self,
        base_params: EstimateBaseParams,
        problem_params: EstimateProblemParams,
    ):
        """
        :params approx_params:
        """
        self.params: EstimateDerivedBaseParams = EstimateDerivedBaseParams(base_params)
        self.problem_params: EstimateProblemParams = problem_params

        # Problem and base params compatibility check

        assert_estimate_problem_and_base_params_are_valid(problem_params, base_params)

        # Solver and formula initialization

        ctx: z3.Context = z3.Context()
        solver: z3.Solver = z3.Solver(ctx=ctx)

        formula = problem_params.formula.translate(ctx)
        variables = [(x.translate(ctx), bc) for x, bc in problem_params.variables]

        # map from formula variable to its encoding bits
        bvs = [z3.BitVec(f"bv_{x}", bc, ctx=ctx) for x, bc in variables]

        formula = z3.And([
            formula,
            z3.And([
                x == z3.BV2Int(bv) for x, bv in zip(map(lambda y: y[0], variables), bvs)
            ])
        ])

        formula_clone_data = self._z3_clone_expression(formula, self.params.q)

        q_bvs = [
            cast(z3.BitVecRef, q_bv)
            for bv in bvs
            for q_bv in formula_clone_data.var_map[bv]
        ]

        # q times conjunction of clones of formula
        formula_q = z3.And(formula_clone_data.clones)

        solver.add(formula_q)

        self._solver: z3.Solver = solver
        self._q_bvs: List[z3.BitVecRef] = q_bvs

    @staticmethod
    def _z3_get_hamming_weight(bit_vector: z3.BitVecRef) -> z3.ArithRef:
        return z3.Sum([
            z3.ZeroExt(
                int(ceil(log2(bit_vector.size()))),
                z3.Extract(i, i, bit_vector)
            )
            for i in range(bit_vector.size())
        ])

    def _z3_get_variables(self, expression: z3.ExprRef) -> List[z3.ExprRef]:
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

    def _z3_clone_expression(self, expression: z3.ExprRef, q: int) -> Z3CloneExpressionOutput:
        """
        Clones expression by generating q instances of the expression where each
        variable is substituted by a unique newly generated variable for each variable in each clone.
        The output will list each clone and a dictionary where each entry corresponds to
        a mapping from variable in the original formula to the substituted cloned variables for each clone
        listed in the same order as the clone list.
        :param expression: Expression to be cloned
        :param q: Amount of clones created
        """

        variables = self._z3_get_variables(expression)

        var_map = {
            x: [self._z3_recreate_variable(f"clone{{{i}}}", x) for i in range(q)] for x in variables
        }

        clones = [z3.substitute(expression, [(x, var_map[x][i]) for x in variables]) for i in range(q)]

        return Z3CloneExpressionOutput(
            clones=clones,
            var_map=var_map,
        )

    @classmethod
    def _z3_make_assert_random_pairwise_independent_hash_is_zero(cls, bvs: List[z3.BitVec], m: int) -> z3.BoolRef:
        """
        Returns z3 formula that asserts that the output of a randomly generated hash function
        is zero when given as input the specified bits. The random hash function needs to be
        generated pairwise independently and have probability 1/(2**m) of being zero for any
        input i.e. Pr[h(x)=0] = 1/(2**m) = 2**(-m) for any x. The amount of input bits is len(bits).
        """

        if len(bvs) == 0:
            return z3.BoolVal(True)

        ctx = bvs[0].ctx

        return z3.And([
            z3.Sum([
                cls._z3_get_hamming_weight(
                    bv & z3.BitVecVal(random.randint(0, 2**bv.size()-1), bv.size(), ctx=ctx)
                )
                for bv in bvs
            ]) % 2 == 0 for _ in range(m)
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

    def exact_model_count_if_less_or_equal_p(self) -> Optional[int]:
        """
        If the formula has <= p models this will return the exact model count,
        otherwise it returns None.
        """

        return self._z3_limited_model_count(self._solver, self._q_bvs, self.params.p + 1)

    def estimate(self, task: EstimateTask) -> EstimateTaskResult:
        """
        Performs estimate from smt paper for the parameter m.
        Note: requires runner to be initialized
        :param task:
        """

        self._solver.push()
        self._solver.add(
            self._z3_make_assert_random_pairwise_independent_hash_is_zero(
                self._q_bvs, task.m,
            )
        )

        # is None if solver has at least a models for q_bits
        lmc = self._z3_limited_model_count(self._solver, self._q_bvs, self.params.a)

        self._solver.pop()

        return EstimateTaskResult(positive_vote=lmc is None)


class EstimateRunner(ReferenceEstimateRunner):
    pass


SerializedEstimateProblemParams = NamedTuple(
    "SerializedEstimateProblemParams",
    [("serialized_formula", str), ("serialized_variables", List[Tuple[str, int]])],
)


def serialize_estimate_problem_params(problem_params: EstimateProblemParams) -> SerializedEstimateProblemParams:
    return SerializedEstimateProblemParams(
        serialized_formula=serialize_expression(problem_params.formula),
        serialized_variables=[(str(x), bc) for x, bc in problem_params.variables],
    )


def deserialize_estimate_problem_params(
    serialized_estimate_problem_params: SerializedEstimateProblemParams,
) -> EstimateProblemParams:
    return EstimateProblemParams(
        formula=cast(z3.BoolRef, deserialize_expression(serialized_estimate_problem_params.serialized_formula)),
        variables=[(z3.Int(name), bc) for name, bc in serialized_estimate_problem_params.serialized_variables],
    )
