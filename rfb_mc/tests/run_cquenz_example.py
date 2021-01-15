from collections import Counter

from alternatives.branching_counter import count_models_by_branching
from problem_generator.tree import get_tree_model_count_upper_bound, collect_tree, \
    convert_cquenz_conf_knowledge_to_tree, get_cquenz_conf_knowledge_feature_variables, convert_problem, Fraction
from time import perf_counter
import z3
from os import cpu_count
from math import log2, floor
from rfb_mc.implementation.eamp.eamp_edge_scheduler import EampEdgeScheduler
from rfb_mc.implementation.eamp.eamp_rfmi_z3 import EampRfmiZ3
from rfb_mc.implementation.helper.z3_helper import deserialize_expression
from rfb_mc.implementation.multi_processing_integrator_z3 import MultiProcessingIntegratorZ3
from rfb_mc.implementation.runner_z3 import FormulaParamsZ3, RunnerZ3
from rfb_mc.store import InMemoryStore, StoreData
from rfb_mc.types import Params
from test_data_sets.cquenz.alpha.date_2020_11_25.data import ck_data

RunnerZ3.add_restrictive_formula_module_implementation(EampRfmiZ3)

if __name__ == "__main__":
    root = convert_cquenz_conf_knowledge_to_tree(ck_data["ck"])
    tree = collect_tree(root)
    max_mc = get_tree_model_count_upper_bound(root)

    print(f"Cquenz Model has {len(tree)-1} features and has a model count upper bound of >= 2 ** {floor(log2(max_mc))},"
          f" exactly {max_mc}")

    cqz_variables = get_cquenz_conf_knowledge_feature_variables(ck_data["ck"])
    variables = [z3.BitVec("bv_" + str(x), bc) for x, bc in cqz_variables]

    formula_conv = z3.And([
        z3.BV2Int(x, False) == cqz_x for x, (cqz_x, _) in zip(variables, cqz_variables)
    ])
    formula_fe = deserialize_expression(ck_data["fe_assertions"])
    formula_const = deserialize_expression(ck_data["const_assertions"])
    formula = z3.And([formula_fe, formula_conv, formula_const])

    # formula, cards, _ = convert_problem((root, []))
    # variables = cards

    s2 = perf_counter()
    s = perf_counter()

    a = 200

    store = InMemoryStore(
        data=StoreData(
            params=Params(
                bit_width_counter=Counter([x.size() for x in variables]),
            ),
        ),
    )

    print(f"Initializing InMemoryApproxExecutionManager took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    scheduler = EampEdgeScheduler(
        store=store,
        confidence=Fraction(0.75),
        a=a,
        q=3,
        max_model_count=max_mc,
    )

    print(f"Initializing ConfidentEdgeFinderBinarySearchEstimateScheduler took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    print(formula)

    integrator = MultiProcessingIntegratorZ3(
        worker_count=cpu_count(),
        formula_params=FormulaParamsZ3(
            formula=formula,
            variables=variables,
        ),
    )

    print("Integrator ------------------------")

    s1 = perf_counter()

    run = integrator.run(scheduler)

    try:
        while True:
            print(f"Intermediate Result: {next(run)}")
    except StopIteration as err:
        print(f"Result: {err.value}")

    d1 = perf_counter() - s1

    print(f"Integrator took {d1:.2f} seconds")

    s = perf_counter()

    print(
        count_models_by_branching(
            formula,
            variables,
        )
    )

    print(f"Branching took {perf_counter()-s:.3f} seconds")
