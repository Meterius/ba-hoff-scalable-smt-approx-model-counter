from collections import Counter
from alternatives.branching_counter import count_models_by_branching
from alternatives.exclusion_counter import count_models_by_exclusion
from implementation.estimate_integrator_z3 import MultiProcessingEstimateIntegratorZ3, DirectEstimateIntegratorZ3
from implementation.estimate_runner_z3 import EstimateProblemParamsZ3
from problem_generator.tree import get_tree_model_count_upper_bound, collect_tree, \
    convert_cquenz_conf_knowledge_to_tree, get_cquenz_conf_knowledge_feature_variables, convert_problem
from implementation.estimate_manager import InMemoryApproxExecutionManager, EstimateBaseParams
from implementation.estimate_scheduler import XORConfidentEdgeFinderBinarySearchEstimateScheduler, \
    ConfidentEdgeFinderLinearSearchEstimateScheduler
from implementation.helper import deserialize_expression
from time import perf_counter
from z3 import *
from os import cpu_count
from math import log2, floor

from test_data_sets.cquenz.alpha.date_2020_11_25.data import ck_data

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
    formula = z3.And([formula_fe, formula_conv])

    formula, cards, _ = convert_problem((root, []))
    variables = cards

    s2 = perf_counter()
    s = perf_counter()

    manager = InMemoryApproxExecutionManager(
        base_params=EstimateBaseParams(
            a=50,
            q=1,
            km=dict(Counter([x.size() for x in cards])),
            max_mc=max_mc,
        ),
    )

    print(f"Initializing InMemoryApproxExecutionManager took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    scheduler = ConfidentEdgeFinderLinearSearchEstimateScheduler(
        manager=manager,
        confidence=0.75,
    )

    print(f"Initializing ConfidentEdgeFinderBinarySearchEstimateScheduler took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    integrator = MultiProcessingEstimateIntegratorZ3(
        worker_count=cpu_count(),
        problem_params=EstimateProblemParamsZ3(
            formula=formula,
            variables=variables,
        ),
        scheduler=scheduler,
    )

    print(f"Initializing DirectProcessingEstimateIntegrator took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    print(f"Initializing took {perf_counter()-s2:.3f} seconds")

    integrator.run()

    print(scheduler.result())
    print(f"Binary search with multi processing took {perf_counter()-s2:.3f} seconds")

    """
    s = perf_counter()

    print(
        count_models_by_branching(
            formula,
            variables,
        )
    )

    print(f"Branching took {perf_counter()-s:.3f} seconds")

    s = perf_counter()

    print(
        count_models_by_exclusion(
            formula,
            [x for x, bc in variables],
        ),
    )

    print(f"Model exclusion took {perf_counter() - s:.3f} seconds")
    """
