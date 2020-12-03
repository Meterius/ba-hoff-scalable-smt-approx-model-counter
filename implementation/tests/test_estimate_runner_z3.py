from z3 import *
import unittest
import random
from implementation.estimate_manager import EstimateBaseParams, EstimateTask
from implementation.estimate_runner_z3 import EstimateProblemParamsZ3, EstimateRunnerZ3


class TestReferenceEstimateRunnerZ3(unittest.TestCase):
    def test_estimate(self):
        c = 300

        for k in (1, 4, 6):
            for a in (1, 5):
                for q in (1, 2):
                    x, y = BitVecs("x y", k)
                    ux, uy = random.randint(0, 2 ** k), random.randint(1, 2 ** k)
                    formula = And([
                        ULT(x, ux),
                        ULT(y, uy),
                    ])
                    model_count = ux * uy

                    runner = EstimateRunnerZ3(
                        EstimateBaseParams(
                            a=a, q=q, max_mc=None, n=2, k=k,
                        ),
                        EstimateProblemParamsZ3(
                            formula=formula, variables=[x, y],
                        )
                    )

                    mp = runner.params.get_max_cj_of_possible_c(tuple(), runner.params.cn)

                    for m in range(1, mp, max(1, mp // 4)):
                        print(k, a, q, m)

                        g = runner.params.g
                        G = runner.params.G

                        estimate_wrong_proportion = 0

                        for i in range(c):
                            if runner.estimate(EstimateTask(c=(0,) * runner.params.cn + (m,))).positive_vote:
                                estimate_wrong_proportion += 1 if model_count ** q <= (2 ** m) * g else 0
                            else:
                                estimate_wrong_proportion += 1 if model_count ** q >= (2 ** m) * G else 0

                        estimate_wrong_proportion /= c

                        self.assertLessEqual(
                            estimate_wrong_proportion,
                            1/4,
                            f"Probability of estimate being wrong is less or equal 1/4",
                        )
