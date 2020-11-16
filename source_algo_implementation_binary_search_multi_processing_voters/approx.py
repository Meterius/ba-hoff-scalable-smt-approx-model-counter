from z3 import *
from math import *
from time import perf_counter
from os import cpu_count
from multiprocessing import Process, Barrier, Value, Lock
from datetime import datetime
from itertools import chain
from typing import List, cast, Iterable, Dict
from .z3_helper import random_m_xor_hash_equals_zero, \
    limited_model_count, clone_formula, is_binary_encoding, deserialize_expression, get_variables, serialize_expression


print_debug = True


def estimate(solver: Solver, variables: List[ArithRef], bits: List[BoolRef], m: int, a: int) -> bool:
    """
    Given a `solver` that has the formula asserted, the variables and the bits that
    constitute the unsigned binary encodings of the variables, this function implements
    the estimate function from the smt paper.
    :param solver:
    :param variables:
    :param bits:
    :param m:
    :param a:
    :return:
    """

    solver.push()

    solver.add(random_m_xor_hash_equals_zero(m, bits))
    has_at_least_a_models = limited_model_count(solver, variables, a) is None

    solver.pop()

    return has_at_least_a_models


def approx_worker(
    worker_count: int,
    worker_idx: int,
    worker_stdio_lock: Lock,
    workers_sync_barrier: Barrier,
    voters_unassigned: Value,
    voters_positive: Value,
    voters_negative: Value,
    return_value: Value,
    formula_serialized: str,
    variable_names: List[str],
    bit_count: int,
    a: int,
    alpha: float,
    epsilon: float,
):
    worker_number = worker_idx + 1

    def p_print_debug(*messages: Iterable[str]):
        if print_debug:
            with worker_stdio_lock:
                for message in messages:
                    print(
                        "[{time}] (Worker[{worker_number}:{worker_count}]): {message}".format(
                            time=datetime.now().strftime("%H:%M:%S:%f"),
                            worker_count=worker_count,
                            worker_number=worker_number,
                            message=message,
                        )
                    )

    def main_p_print_debug(*messages: Iterable[str]):
        if worker_number == 1:
            p_print_debug(*messages)

    formula = deserialize_expression(formula_serialized)
    arith_variable_map = {str(x): x for x in get_variables(formula) if type(x) == ArithRef}
    variables = [arith_variable_map[xn] for xn in variable_names]

    q: int = int(ceil((1 + 4 * log2(sqrt(a + 1) + 1) - 2 * log2(a)) / (2 * log2(1 + epsilon))))
    n = bit_count * len(variables) * q
    mp: int = int(floor(n - 2 * log2(sqrt(a + 1) + 1)))
    r: int = int(ceil(8 * log((1 / alpha) * mp)))

    # map from variable to its encoding bits
    bits_map = {
        x: [Bool("bit({i})_{x}".format(i=i, x=x)) for i in range(bit_count)] for x in variables
    }

    # formula that represents "formula and each variable is binary encoding of its bits"
    formula_e = And(formula, And([is_binary_encoding(x, bits_map[x]) for x in variables]))

    cloned_formula_e_return = clone_formula(formula_e, q)
    # formula that represents "formula_e but cloned q times"
    formula_q = And(cloned_formula_e_return.clone_formulas)
    # variables in formula_q that represent cloned versions of the formula variables
    q_variables = [cast(ArithRef, x_q) for x in variables for x_q in cloned_formula_e_return.clone_vars_map[x]]
    # bits in formula_q that represent cloned versions of the formula_e bits
    q_bits = [
        cast(BoolRef, bit_q)
        for bit in chain.from_iterable(bits_map.values())
        for bit_q in cloned_formula_e_return.clone_vars_map[bit]
    ]

    solver = Solver()
    solver.add(formula_q)

    p_print_debug(
        "Setup Complete",
    )

    cached_mj_estimate_cache: Dict[int, bool] = {}

    def cached_mj_estimate(m: int) -> bool:
        if m not in cached_mj_estimate_cache:
            workers_sync_barrier.wait()

            if worker_number == 1:
                voters_positive.value = 0
                voters_negative.value = 0
                voters_unassigned.value = r

            workers_sync_barrier.wait()

            while True:
                with voters_unassigned.get_lock(), voters_positive.get_lock(), voters_negative.get_lock():
                    early_vote_termination = voters_positive.value > r / 2 or voters_positive.value + \
                                             (r - voters_positive.value - voters_negative.value) <= r / 2

                    if voters_unassigned.value != 0 and not early_vote_termination:
                        voters_unassigned.value -= 1
                    else:
                        break

                if estimate(solver, q_variables, q_bits, m, a):
                    p_print_debug("Estimate Majority Iteration ({m}) Positive Vote Added".format(m=m))
                    with voters_positive.get_lock():
                        voters_positive.value += 1
                else:
                    p_print_debug("Estimate Majority Iteration ({m}) Negative Vote Added".format(m=m))
                    with voters_negative.get_lock():
                        voters_negative.value += 1

            workers_sync_barrier.wait()

            cached_mj_estimate_cache[m] = voters_positive.value > r / 2

        if worker_number == 1:
            p_print_debug("Estimate majority for m={m} is {0}".format(cached_mj_estimate_cache[m], m=m))

        return cached_mj_estimate_cache[m]

    def compare_edge_to(m: int) -> int:
        estimate_base = cached_mj_estimate(m)

        if m == 1 and not estimate_base:
            return 0
        elif m == mp:
            return 0 if estimate_base else -1
        elif estimate_base:
            return 1

        estimate_prev = cached_mj_estimate(m - 1)

        return 0 if estimate_prev else -1

    left = 1
    right = mp

    m = 1
    while left <= right:
        m = floor((left + right) / 2)

        main_p_print_debug("Looking at m={m}".format(m=m))

        comparison = compare_edge_to(m)

        if comparison == -1:
            main_p_print_debug("Edge is smaller then m={m}".format(m=m))
            right = m - 1
        elif comparison == 1:
            main_p_print_debug("Edge is greater then m={m}".format(m=m))
            left = m + 1
        else:
            main_p_print_debug("Edge found at m={m}".format(m=m))
            break

    workers_sync_barrier.wait()

    if left > right:
        main_p_print_debug(
            "Edge is not present, i.e. a estimate majority vote must have returned an incorrect result, "
            "assuming m={m} "
                .format(m=m)
        )

    return_value.value = (a * (2 ** (m - 0.5))) ** (1 / q)

    p_print_debug("Finished")


def approx(
    worker_count: int,
    formula: ExprRef,
    variables: List[ArithRef],
    bit_count: int,
    a: int,
    alpha: float,
    epsilon: float,
) -> float:
    q: int = int(ceil((1 + 4 * log2(sqrt(a + 1) + 1) - 2 * log2(a)) / (2 * log2(1 + epsilon))))
    p: int = int(ceil((sqrt(a + 1) - 1) ** (2 / q)))

    solver = Solver()
    solver.add(formula)

    lmc = limited_model_count(solver, variables, p + 1)
    if lmc is not None:
        return lmc
    else:
        del solver

    return_value = Value("f", 0)
    voters_unassigned = Value("i", 0)
    voters_positive = Value("i", 0)
    voters_negative = Value("i", 0)
    worker_stdio_lock = Lock()
    workers_sync_barrier = Barrier(parties=worker_count)

    formula_serialized = serialize_expression(formula)
    variable_names = [str(x) for x in variables]

    workers = [
        Process(
            target=approx_worker,
            kwargs={
                "worker_count": worker_count,
                "worker_idx": worker_idx,
                "worker_stdio_lock": worker_stdio_lock,
                "workers_sync_barrier": workers_sync_barrier,
                "voters_unassigned": voters_unassigned,
                "voters_positive": voters_positive,
                "voters_negative": voters_negative,
                "return_value": return_value,
                "formula_serialized": formula_serialized,
                "variable_names": variable_names,
                "bit_count": bit_count,
                "a": a,
                "alpha": alpha,
                "epsilon": epsilon,
            },
        ) for worker_idx in range(worker_count)
    ]

    for worker in workers:
        worker.start()

    for worker in workers:
        worker.join()
        worker.close()

    return return_value.value


def run_reference_test():
    x = Int("x")
    f = And([0 <= x, x < 42])

    s = perf_counter()

    print(
        "Finished Approx with result: {result}".format(
            result=approx(
                cpu_count(), f, [x], 7, 100, 0.1, 0.2,
            )
        )
    )

    print("Took {d} seconds".format(d=perf_counter() - s))


if __name__ == "__main__":
    run_reference_test()