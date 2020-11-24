from z3 import *
import unittest
import random
from implementation.estimate_manager import EstimateBaseParams, EstimateTask
from implementation.estimate_runner import ReferenceEstimateRunner, EstimateRunner, EstimateProblemParams


class TestReferenceEstimateRunner(unittest.TestCase):
    @staticmethod
    def make_runner(base_params: EstimateBaseParams, problem_params: EstimateProblemParams):
        return ReferenceEstimateRunner(base_params, problem_params)

    def test_estimate(self):
        c = 100

        for n in (1, 4, 8):
            for a in (1, 10):
                for q in (1, 2):
                    x, y = Ints("x y")
                    ux, uy = random.randint(0, 2 ** n), random.randint(1, 2 ** n)
                    formula = And([
                        x < ux,
                        y < uy,
                    ])
                    model_count = ux * uy

                    runner = self.make_runner(
                        EstimateBaseParams(
                            a=a, q=q, max_mc=None, bc=2 * n,
                        ),
                        EstimateProblemParams(
                            formula=formula, variables=[(x, n), (y, n)],
                        )
                    )

                    for m in range(1, 2):
                        g = runner.params.g
                        G = runner.params.G

                        estimate_wrong_proportion = 0

                        for i in range(c):
                            if runner.estimate(EstimateTask(m=m)).positive_vote:
                                estimate_wrong_proportion += 1 if model_count ** q <= (2 ** m) * g else 0
                            else:
                                estimate_wrong_proportion += 1 if model_count ** q >= (2 ** m) * G else 0

                        estimate_wrong_proportion /= c

                        self.assertLessEqual(
                            estimate_wrong_proportion,
                            1/4,
                            f"Probability of estimate being wrong is less or equal 1/4",
                        )


class TestEstimateRunner(TestReferenceEstimateRunner):
    @staticmethod
    def make_runner(base_params: EstimateBaseParams, problem_params: EstimateProblemParams):
        return EstimateRunner(base_params, problem_params)
