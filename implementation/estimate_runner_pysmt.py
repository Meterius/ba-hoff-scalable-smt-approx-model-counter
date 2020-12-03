from functools import reduce
import random
from implementation.estimate_manager import EstimateBaseParams, \
    EstimateTaskResult, EstimateTask
from implementation.estimate_runner import BaseEstimateRunner
from typing import NamedTuple, Optional, List, Tuple, Dict, Any
from math import ceil, log2, floor
from pysmt.typing import BVType
from pysmt.solvers.solver import Solver
from pysmt.shortcuts import substitute, Solver, Symbol, get_free_variables, BVExtract, BVZExt, BV, BVURem, BVAdd, \
    BVMul, And, Or, Not, EqualsOrIff, Equals, simplify
from pysmt.parsing import parse

EstimateProblemParamsPYSMT = NamedTuple(
    "EstimateProblemParamsPYSMT",
    [("formula", Any), ("variables", List[Any])]
)

CloneExpressionOutputPYSMT = NamedTuple("CloneExpressionOutputPYSMT", [
    ("clones", List[Any]), ("var_map", Dict[Any, List[Any]])
])


def get_bit_width_of_sum(operator_bit_width: int, operator_count: int) -> int:
    return int(floor(log2(operator_count * ((2 ** operator_bit_width) - 1))) + 1)


def BVSum(xs: List[Any]) -> Any:
    ops_bit_width = xs[0].bv_width()
    sum_bit_width = get_bit_width_of_sum(ops_bit_width, len(xs))
    return reduce(
        lambda x, y: BVAdd(x, y),
        [BVZExt(x, sum_bit_width - x.bv_width()) for x in xs]
    )


class EstimateRunnerPYSMT(BaseEstimateRunner[EstimateProblemParamsPYSMT]):
    """
    Implements estimate function.
    """

    def __init__(
        self,
        base_params: EstimateBaseParams,
        problem_params: EstimateProblemParamsPYSMT,
    ):
        super().__init__(base_params, problem_params)

        # Problem and base params compatibility check

        self.assert_base_params_and_problem_params_compatible(base_params, problem_params)

        # Solver and formula initialization

        solver: Solver = Solver(name="msat")

        formula = problem_params.formula
        variables = problem_params.variables

        formula_clone_data = self._pysmt_clone_expression(formula, self.params.q)

        q_bvs = [
            q_bv
            for bv in variables
            for q_bv in formula_clone_data.var_map[bv]
        ]

        # q times conjunction of clones of formula
        formula_q = And(formula_clone_data.clones)

        solver.add_assertion(formula_q)

        self._solver: Solver = solver
        self._q_bvs: List[Any] = q_bvs

    @classmethod
    def assert_base_params_and_problem_params_compatible(
        cls,
        base_params: EstimateBaseParams,
        problem_params: EstimateProblemParamsPYSMT,
    ):
        assert len(problem_params.variables) == base_params.n, "Amount of variables equals base params n"
        assert all(
            [x.bv_width() <= base_params.k for x in problem_params.variables]), "Variables must have bit size at most k"

    @staticmethod
    def _get_random_int(a: int, b: int) -> int:
        """
        Returns a random integer from the inclusive interval [a, b]
        """

        return random.randint(a, b)

    @classmethod
    def _pysmt_clone_expression(cls, expression: Symbol, q: int) -> CloneExpressionOutputPYSMT:
        """
        Clones expression by generating q instances of the expression where each
        variable is substituted by a unique newly generated variable for each variable in each clone.
        The output will list each clone and a dictionary where each entry corresponds to
        a mapping from variable in the original formula to the substituted cloned variables for each clone
        listed in the same order as the clone list.
        :param expression: Expression to be cloned
        :param q: Amount of clones created
        """

        variables = get_free_variables(expression)

        var_map = {
            x: [Symbol(f"clone{{{i}}}_{x.symbol_name()}", x.symbol_type()) for i in range(q)] for x in variables
        }

        clones = [substitute(expression, {x: var_map[x][i] for x in variables}) for i in range(q)]

        return CloneExpressionOutputPYSMT(
            clones=clones,
            var_map=var_map,
        )

    def _pysmt_get_XJM_slices(self, xs: List[Any], j: int) -> List[Any]:
        slices = []
        slice_size = int(ceil(self.params.k / (2 ** j)))

        for x in xs:
            for i in range(x.bv_width() // slice_size):
                slices.append(
                    BVExtract(x, i * slice_size, (i + 1) * slice_size - 1)
                )

            if (x.bv_width() // slice_size) * slice_size != x.bv_width():
                rem_slice_size = x.bv_width() % slice_size
                slices.append(
                    BVZExt(
                        BVExtract(x, x.bv_width() - 1 - rem_slice_size, x.bv_width() - 1),
                        slice_size - rem_slice_size,
                    )
                )

        return slices

    def _pysmt_make_hash_from_HJ(self, xs: List[Any], j: int) -> Any:
        p = self.params.p[j]
        pbc = int(ceil(log2(p+1)))

        def get_random_coefficient():
            return BV(self._get_random_int(0, p - 1), 2 * pbc)

        slices = self._pysmt_get_XJM_slices(xs, j)
        slice_size = int(ceil(self.params.k / (2 ** j)))

        return BVURem(
            BVSum([
                BVMul(BVZExt(s, 2 * pbc - slice_size), get_random_coefficient()) for s in slices
            ] + [get_random_coefficient()]),
            BV(self.params.p[j], get_bit_width_of_sum(2 * pbc, len(slices) + 1))
        )

    def _pysmt_make_hash_from_H(self, xs: List[Any], c: Tuple[int, ...]) -> List[List[Any]]:
        return [
            [self._pysmt_make_hash_from_HJ(xs, j) for _ in range(c[j])]
            for j in range(self.params.cn + 1)
        ]

    def _pysmt_make_hash_equality_from_H(self, xs: List[Any], c: Tuple[int, ...]) -> Any:
        alpha = [
            [self._get_random_int(0, self.params.p[j] - 1) for _ in range(c[j])]
            for j in range(self.params.cn + 1)
        ]

        h = self._pysmt_make_hash_from_H(xs, c)

        return And([
            And([Equals(h[j][i], BV(alpha[j][i], h[j][i].bv_width())) for i in range(c[j])])
            for j in range(self.params.cn + 1)
        ])

    @staticmethod
    def _pysmt_limited_model_count(solver: Solver, xs: List[Any], u: int) -> Optional[int]:
        """
        If the solver assertions have less than u models that are distinct for the given variables it
        returns the exact model count, otherwise it returns None.
        :param solver:
        :param xs:
        :param u:
        """

        if u == 1:
            return None if solver.solve() else 0

        solver.push()

        for i in range(u):
            if not solver.solve():
                solver.pop()
                return i

            if i != u - 1:
                m = solver.get_model()
                solver.add_assertion(Or([Not(EqualsOrIff(m.get_value(x), x)) for x in xs]))

        solver.pop()

        return None

    def exact_model_count_if_less_or_equal_t(self) -> Optional[int]:
        """
        If the formula has <= t models this will return the exact model count,
        otherwise it returns None.
        """

        return self._pysmt_limited_model_count(self._solver, self._q_bvs, self.params.t + 1)

    def estimate(self, task: EstimateTask) -> EstimateTaskResult:
        """
        Performs estimate from smt paper for the parameter m.
        Note: requires runner to be initialized
        :param task:
        """

        self.params.assert_is_possible_c(task.c)

        self._solver.push()
        self._solver.add_assertion(
            self._pysmt_make_hash_equality_from_H(
                self._q_bvs, task.c,
            )
        )

        # print(self._solver.z3.assertions())

        # is None if solver has at least a models for q_bits
        lmc = self._pysmt_limited_model_count(self._solver, self._q_bvs, self.params.a)

        self._solver.pop()

        return EstimateTaskResult(positive_vote=lmc is None)


SerializedEstimateProblemParamsPYSMT = NamedTuple(
    "SerializedEstimateProblemParamsPYSMT",
    [("serialized_formula", str), ("serialized_variables", List[Tuple[str, int]])],
)


def serialize_estimate_problem_params_pysmt(
    problem_params: EstimateProblemParamsPYSMT,
) -> SerializedEstimateProblemParamsPYSMT:
    return SerializedEstimateProblemParamsPYSMT(
        serialized_formula=problem_params.formula.serialize(),
        serialized_variables=[(x.symbol_name(), x.bv_width()) for x in problem_params.variables],
    )


def deserialize_estimate_problem_params_pysmt(
    serialized_estimate_problem_params: SerializedEstimateProblemParamsPYSMT,
) -> EstimateProblemParamsPYSMT:
    return EstimateProblemParamsPYSMT(
        formula=parse(serialized_estimate_problem_params.serialized_formula),
        variables=[Symbol(name, BVType(k)) for name, k in serialized_estimate_problem_params.serialized_variables],
    )
