from implementation.estimate_runner import EstimateProblemParams
from alternatives.branching_counter import count_models_by_comparison_branching, count_models_by_branching
from alternatives.exclusion_counter import count_models_by_exclusion
from problem_generator.tree import get_tree_model_count_upper_bound, collect_tree, \
    convert_cquenz_conf_knowledge_to_tree, get_cquenz_conf_knowledge_feature_variables
from implementation.estimate_manager import InMemoryApproxExecutionManager, EstimateBaseParams
from implementation.estimate_integrator import DirectEstimateIntegrator, MultiProcessingEstimateIntegrator
from implementation.estimate_scheduler import ConfidentEdgeFinderBinarySearchEstimateScheduler
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

    formula_fe = deserialize_expression(ck_data["fe_assertions"])
    formula_const = deserialize_expression(ck_data["const_assertions"])
    formula = formula_fe
    variables = get_cquenz_conf_knowledge_feature_variables(ck_data["ck"])

    s2 = perf_counter()
    s = perf_counter()

    manager = InMemoryApproxExecutionManager(
        base_params=EstimateBaseParams(
            a=35,
            q=1,
            bc=sum([bc for _, bc in variables]),
            max_mc=max_mc,
        ),
    )

    print(f"Initializing InMemoryApproxExecutionManager took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    scheduler = ConfidentEdgeFinderBinarySearchEstimateScheduler(
        manager=manager,
        confidence=0.75,
    )

    print(f"Initializing ConfidentEdgeFinderBinarySearchEstimateScheduler took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    integrator = MultiProcessingEstimateIntegrator(
        worker_count=cpu_count(),
        problem_params=EstimateProblemParams(
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


    s = perf_counter()

    print(
        count_models_by_comparison_branching(
            formula,
            [x for x, bc in variables],
            max([bc for x, bc in variables]),
        )
    )

    print(f"Comparison branching took {perf_counter()-s:.3f} seconds")

    s = perf_counter()

    print(
        count_models_by_branching(
            formula,
            [x for x, bc in variables],
            max([bc for x, bc in variables]),
        )
    )

    print(f"Boolean branching took {perf_counter() - s:.3f} seconds")

    s = perf_counter()

    print(
        count_models_by_exclusion(
            formula,
            [x for x, bc in variables],
        ),
    )

    print(f"Model exclusion took {perf_counter() - s:.3f} seconds")
