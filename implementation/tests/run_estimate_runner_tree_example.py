from implementation.estimate_runner_z3 import EstimateProblemParamsZ3
from problem_generator.generator import generate_random_flat_tree, generate_random_constraints
from problem_generator.tree import convert_problem, get_tree_model_count_upper_bound, collect_tree
from implementation.estimate_manager import InMemoryApproxExecutionManager, EstimateBaseParams
from implementation.estimate_integrator_z3 import DirectEstimateIntegratorZ3
from implementation.estimate_scheduler import ConfidentEdgeFinderBinarySearchEstimateScheduler
from time import perf_counter
from math import log2, floor

if __name__ == "__main__":
    root = generate_random_flat_tree(15, 3, 3)
    tree = collect_tree(root)
    constraints = generate_random_constraints(root, 0)

    max_mc = get_tree_model_count_upper_bound(root)

    print(f"Tree has {len(tree)} nodes and has a model count upper bound of >= 2 ** {floor(log2(max_mc))}")
    print(f"{len(constraints)} constraints have been added")

    formula, cards, _ = convert_problem((root, constraints))

    s2 = perf_counter()
    s = perf_counter()

    manager = InMemoryApproxExecutionManager(
        base_params=EstimateBaseParams(
            a=1,
            q=1,
            n=len(cards),
            k=max([x.size() for x in cards]),
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

    integrator = DirectEstimateIntegratorZ3(
        problem_params=EstimateProblemParamsZ3(
            formula=formula,
            variables=cards,
        ),
        scheduler=scheduler,
    )

    print(f"Initializing DirectProcessingEstimateIntegrator took {perf_counter() - s:.3f} seconds")
    s = perf_counter()

    print(f"Initializing took {perf_counter()-s2:.3f} seconds")

    integrator.run()

    print(f"Binary search with multi processing took {perf_counter()-s2:.3f} seconds")

    print(scheduler.result())
