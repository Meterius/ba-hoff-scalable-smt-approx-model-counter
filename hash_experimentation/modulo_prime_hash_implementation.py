from implementation.estimate_manager import EstimateBaseParams, EstimateDerivedBaseParams, EstimateTask, \
    EstimateTaskResult
from implementation.estimate_runner import EstimateProblemParams, \
    Z3CloneExpressionOutput
import z3
from typing import *
import random
from math import *


class EstimateRunner:
    """
    Implements estimate function.
    """

    def __init__(
        self,
        base_params: EstimateBaseParams,
        problem_params: EstimateProblemParams,
        r: int,
    ):
        """
        :params approx_params:
        """
        self.params: EstimateDerivedBaseParams = EstimateDerivedBaseParams(base_params)
        self.problem_params: EstimateProblemParams = problem_params

        self.params.mp = max(1, int(floor(log(self.params.max_mc, r) - log(self.params.G, r))))

        self.r = r

        # Problem and base params compatibility check

        # Solver and formula initialization

        ctx: z3.Context = z3.Context()
        # solver: z3.Solver = z3.Solver(ctx=ctx)
        solver: z3.Solver = z3.SolverFor("QF_FD", ctx=ctx)

        formula = problem_params.formula.translate(ctx)
        variables = [x.translate(ctx) for x, bc in problem_params.variables]

        solver.add(formula)

        self._solver: z3.Solver = solver
        self._q_vars: List[z3.ArithRef] = variables

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

    def _z3_make_assert_random_pairwise_independent_hash_is_zero(self, vars: List[z3.ArithRef], m: int) -> z3.BoolRef:
        if len(vars) == 0:
            return z3.BoolVal(True)

        ctx = vars[0].ctx

        return z3.simplify(z3.And([
            z3.Sum([
                random.randint(0, self.r-1) * x for x in vars
            ]) % self.r == 0
            for _ in range(m)
        ]))

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

        return self._z3_limited_model_count(
            self._solver, self._q_vars, self.params.p + 1,
        )

    def estimate(self, task: EstimateTask) -> EstimateTaskResult:
        """
        Performs estimate from smt paper for the parameter m.
        Note: requires runner to be initialized
        :param task:
        """

        self._solver.push()
        self._solver.add(
            self._z3_make_assert_random_pairwise_independent_hash_is_zero(
                self._q_vars, task.m,
            )
        )

        # is None if solver has at least a models for q_bits
        lmc = self._z3_limited_model_count(
            self._solver, self._q_vars, self.params.a,
        )

        self._solver.pop()

        return EstimateTaskResult(positive_vote=lmc is None)