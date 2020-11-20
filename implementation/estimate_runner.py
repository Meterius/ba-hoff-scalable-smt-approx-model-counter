import z3
import random
from abc import ABC, abstractmethod
from math import sqrt, log2, ceil
from typing import NamedTuple, Optional, Generic, TypeVar, List, Tuple, Dict, cast

ApproxParams = NamedTuple(
    "ApproxParams",
    [("a", int), ("epsilon", float)],
)

ApproxPayloadParams = NamedTuple(
    "ApproxPayloadParams",
    [("formula", z3.BoolRef), ("variables", List[Tuple[z3.ArithRef, int]])]
)


class ApproxDerivedParams:
    def __init__(self, params: ApproxParams):
        self.a = params.a
        self.epsilon = params.epsilon

        self.g = (sqrt(self.a + 1) - 1) ** 2
        self.G = (sqrt(self.a + 1) + 1) ** 2

        self.q = ceil(
            (1 + 4 * log2(sqrt(self.a + 1) + 1) - 2 * log2(self.a)) /
            (2 * log2(1 + self.epsilon))
        )
        self.p = ceil((sqrt(self.a + 1) - 1) ** (2 / self.q))


EstimateRunnerInstanceData = NamedTuple(
    "EstimateRunnerInstanceData",
    [
        ("payload_params", ApproxPayloadParams),
        ("solver", z3.Solver),

        # bits representing unsigned binary encoding of the variables given for the formula
        ("bits", List[z3.BoolRef]),

        # clones of the bits and variables that are used in the clones of the original formula which
        # is actually asserted to the solver
        ("q_bits", List[z3.BoolRef]),
        ("q_variables", List[z3.ArithRef]),
    ]
)

Z3CloneExpressionOutput = NamedTuple("Z3CloneExpressionOutput", [
    ("clones", List[z3.BoolRef]), ("var_map", Dict[z3.ExprRef, List[z3.ExprRef]])
])

EstimateRunnerPayloadType = TypeVar("EstimateRunnerPayloadType")


class EstimateRunner(ABC, Generic[EstimateRunnerPayloadType]):
    params: ApproxDerivedParams

    instance_data: Optional[EstimateRunnerInstanceData] = None

    def __init__(self, approx_params: ApproxParams):
        """
        :params approx_params:
        """
        self.params = ApproxDerivedParams(approx_params)

    @abstractmethod
    def _decode_payload(self, payload: EstimateRunnerPayloadType, ctx: z3.Context) -> ApproxPayloadParams:
        """
        Abstract method that should be implemented by concrete implementation.
        Decodes payload to approx payload params.
        The payload should be transferable via python multiprocessing arguments.
        :params payload: Payload from which approx payload params should be decoded
        :params ctx: Context that the z3 data should be created with,
                     note that this can also be achieved by translating
                     formula and variables after their creation, although
                     that should be avoided as it unnecessarily increases setup
                     and memory costs
        """

        return NotImplemented

    def _require_instance_data(self) -> EstimateRunnerInstanceData:
        """
        Returns instance data that is set after initialize has been called.
        If initialize has not been called this method will raise an exception.
        """

        if self.instance_data is not None:
            return self.instance_data
        else:
            raise RuntimeError("EstimateRunner is not initialized")

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

    def _z3_recreate_variable(self, key: str, variable: z3.ExprRef) -> z3.ExprRef:
        """
        Recreates the variable but renames it with a key that is used
        to make it distinct.
        :param key:
        :param variable:
        """

        return z3.Const("{key}_{name}".format(key=key, name=str(variable)), variable.sort())

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
            x: [self._z3_recreate_variable("clone\{{i}\}".format(i=i), x) for i in range(q)] for x in variables
        }

        clones = [z3.substitute(expression, [(x, var_map[x][i]) for x in variables]) for i in range(q)]

        return Z3CloneExpressionOutput(
            clones=clones,
            var_map=var_map,
        )

    def _z3_make_assert_unsigned_binary_encoding(self, variable: z3.ArithRef, bits: List[z3.BoolRef]) -> z3.BoolRef:
        """
        Returns z3 formula that asserts that the bits are
        an unsigned binary encoding of the variable.
        :param variable:
        :bits bits:
        """

        return z3.Sum([z3.If(bit, 2 ** i, 0) for i, bit in enumerate(bits)]) == variable

    def _z3_make_assert_random_pairwise_independent_hash_is_zero(self, bits: List[z3.BoolRef], m: int) -> z3.BoolRef:
        """
        Returns z3 formula that asserts that the output of a randomly generated hash function
        is zero when given as input the specified bits. The random hash function needs to be
        generated pairwise independently and have probability 1/(2**m) of being zero for any
        input i.e. Pr[h(x)=0] = 1/(2**m) = 2**(-m) for any x. The amount of input bits is len(bits).
        """

        if len(bits) == 0:
            return z3.BoolVal(True)

        ctx = bits[0].ctx
        hash_is_zero_conditions = []

        # creates m times the xor hash function from the smt paper to generate
        # a pairwise independent random hash for the given m
        for i in range(m):
            # generates the xor hash function from the smt paper for the case m=1,
            # it generates the xor sum by applying xor to the first two queue elements and
            # appending the result to the end of the queue, when the queue only has one remaining item
            # that item will be an xor sum of the original queue

            queue = [z3.BoolVal(random.getrandbits(1))] + [bit for bit in bits if random.getrandbits(1)]

            while len(queue) >= 2:
                queue.append(
                    z3.Xor(queue.pop(0), queue.pop(0))
                )

            hash_is_zero_conditions.append(queue[0])

        return z3.And(hash_is_zero_conditions)

    def _z3_limited_model_count(self, solver: z3.Solver, variables: List[z3.ExprRef], max: int) -> Optional[int]:
        """
        If the solver assertions have less than max models that are distinct for the given variables it
        returns the exact model count, otherwise it returns None.
        :param solver:
        :param variables:
        :param max:
        """

        solver.push()

        for i in range(max):
            response = solver.check()

            if response == z3.unknown:
                solver.pop()
                raise RuntimeError("Solver responded with unknown")

            if response == z3.unsat:
                solver.pop()
                return i

            m = solver.model()

            solver.add(z3.Or([x != m[x] for x in variables]))

        solver.pop()

        return None

    def initialize(self, payload: EstimateRunnerPayloadType):
        """
        Initializes the runner.
        Needs to be called before other methods are used.
        :params payload:
        """

        ctx = z3.Context()
        solver = z3.Solver(ctx=ctx)
        payload_params = self._decode_payload(payload, ctx)

        # map from formula variable to its encoding bits
        bit_map = {
            x: [z3.Bool("{x}_bit_{i}".format(x=x, i=i)) for i in range(n)] for x, n in payload_params.variables
        }

        # formula that extends original formula with assertion that the bit_map encodes its corresponding variables
        formula_e = z3.And(
            payload_params.formula,
            z3.And([self._z3_make_assert_unsigned_binary_encoding(x, bit_map[x]) for x in bit_map]),
        )

        formula_e_clone_data = self._z3_clone_expression(formula_e, self.params.q)

        q_bits = [
            cast(z3.BoolRef, q_bit)
            for x in bit_map
            for bit in bit_map[x]
            for q_bit in formula_e_clone_data.var_map[bit]
        ]

        q_variables = [
            cast(z3.ArithRef, q_x)
            for x in bit_map
            for q_x in formula_e_clone_data.var_map[x]
        ]

        # q times conjunction of clones of formula_e
        formula_q = z3.And([formula_e_clone_data.clones])

        solver.add(formula_q)

        self.instance_data = EstimateRunnerInstanceData(
            solver=solver,
            payload_params=payload_params,

            bits=[bit for x in bit_map for bit in bit_map[x]],

            q_bits=q_bits,
            q_variables=q_variables,
        )

    def estimate(self, m: int):
        """
        Performs estimate from smt paper for the parameter m.
        Note: requires runner to be initialized
        :param m:
        """

        instance_data = self._require_instance_data()

        instance_data.solver.push()
        instance_data.solver.add(
            self._z3_make_assert_random_pairwise_independent_hash_is_zero(
                instance_data.q_bits, m,
            )
        )

        # is None if solver has at least a models for q_bits
        lmc = self._z3_limited_model_count(instance_data.solver, instance_data.q_bits, self.params.a)

        instance_data.solver.pop()

        return lmc is None
