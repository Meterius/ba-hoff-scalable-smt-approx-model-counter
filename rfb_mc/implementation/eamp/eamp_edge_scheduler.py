from fractions import Fraction
from math import sqrt, prod, log2, ceil, log
from typing import NamedTuple, Tuple, Type, Optional, Iterable, List
from collections import Counter
from rfb_mc.implementation.eamp.eamp_rfm import EampRfm, get_cn, EampParams, EampTransformMethod, get_pj
from rfb_mc.scheduler import SchedulerBase
from rfb_mc.store import StoreBase
from rfb_mc.types import RfBmcTask, RfBmcResult

EampEdgeInterval = NamedTuple("EampEdgeInterval", [
    ("interval", Tuple[int, int]),
    ("confidence", Fraction),
])


class EampEdgeScheduler(SchedulerBase[EampEdgeInterval, EampEdgeInterval, EampRfm]):
    def __init__(
        self,
        store: StoreBase,
        confidence: Fraction,
        a: int,
        q: int,
        max_model_count: Optional[int] = None,
    ):
        super().__init__(store, EampRfm)

        assert a >= 1, "a >= 1"
        assert q >= 1, "q >= 1"
        assert 0 <= confidence < 1, "Confidence is < 1 and >= 0"

        self.confidence: Fraction = confidence
        self.a: int = a
        self.q: int = q
        self.max_model_count = max_model_count if max_model_count is not None else prod([
            (2 ** bit_width) ** count for bit_width, count in self.store.data.params.bit_width_counter.items()
        ])

    def _run_algorithm(self):
        g = (sqrt(self.a + 1) - 1) ** 2
        G = (sqrt(self.a + 1) + 1) ** 2

        cn = get_cn(self.max_model_count ** self.q, G)

        beta = 1 - self.confidence

        max_k = max(int(ceil(max([
            log2(get_pj(i) / prod([get_pj(j) for j in range(1, i)]))
            for i in range(1, cn)
        ]))) - 1, 1) if cn > 1 else 1
        max_iter_count = cn - 1 + max_k

        alpha = 3 / 4
        sigma = 1 / (2 * alpha) - 1
        gamma = sigma**2 / (2 + sigma)
        r = int(ceil(log(max_iter_count / beta) / gamma))
        print(f"r={r} max_k={max_k}")

        def make_eamp_params(c: Iterable[int]):
            return EampParams(
                c=tuple(c),
                transform_method=EampTransformMethod.SORTED_ROLLING_WINDOW,
            )

        def make_rf_bmc_task(eamp_params: EampParams):
            return RfBmcTask(
                rf_module_uid=self.rf_module.get_uid(),
                rf_module_param=eamp_params,
                a=self.a,
                q=self.q,
            )

        def can_c_be_set_to_negative(c: List[int]) -> bool:
            props = self.rf_module.get_restrictive_formula_properties(
                self.store.data.params,
                make_eamp_params(c),
            )

            return self.max_model_count ** self.q < props.range_size * G

        # TODO: handle model count being too small

        c_pos: Optional[List[int]] = None

        c_neg: Optional[List[int]] = None

        def get_edge_interval():
            props_pos = self.rf_module.get_restrictive_formula_properties(
                self.store.data.params, make_eamp_params(c_pos),
            ) if c_pos is not None else None

            props_neg = self.rf_module.get_restrictive_formula_properties(
                self.store.data.params, make_eamp_params(c_neg),
            ) if c_neg is not None else None

            # TODO: investigate precision of q-th root
            # TODO: add proper confidence known bound
            return EampEdgeInterval(
                interval=(
                    (props_pos.range_size * g) ** (1 / self.q) if props_pos is not None else 0,
                    min(self.max_model_count, (props_neg.range_size * G) ** (1 / self.q))
                    if props_neg is not None else self.max_model_count
                ),
                confidence=self.confidence,
            )

        def majority_vote_estimate(c: List[int]):
            while True:
                rf_bmc_task = make_rf_bmc_task(make_eamp_params(c))
                rf_bmc_results: Counter[RfBmcResult] = self.store.data.hbmc_results_map.get(rf_bmc_task, Counter())

                positive_voters = sum([
                    count
                    for result, count in rf_bmc_results.items()
                    if result.bmc is None
                ])

                negative_voters = sum([
                    count
                    for result, count in rf_bmc_results.items()
                    if result.bmc is not None
                ])

                rr = max(0, r - (positive_voters + negative_voters))

                if positive_voters >= negative_voters and positive_voters >= negative_voters + rr:
                    return True

                if negative_voters > positive_voters and negative_voters > positive_voters + rr:
                    return False

                yield EampEdgeScheduler.AlgorithmYield(
                    required_tasks=Counter(rr * [rf_bmc_task]),
                    predicted_required_tasks=Counter(),
                    intermediate_result=get_edge_interval(),
                )

        c = [0] * (cn - 1) + [1]
        j = cn - 1

        while True:
            while can_c_be_set_to_negative(c) and j != 0:
                c_neg = c.copy()

                c[j] = 0
                c[j - 1] = 1
                j -= 1

            if can_c_be_set_to_negative(c) and j == 0:
                c_neg = c.copy()
                break

            mv_estimate = yield from majority_vote_estimate(c)

            if mv_estimate:
                c_pos = c.copy()

                if j == 0:
                    c[j] += 1
                else:
                    c[j - 1] = 1
                    j -= 1
            else:
                c_neg = c.copy()

                if j == 0:
                    break
                else:
                    c[j] = 0
                    c[j - 1] = 1
                    j -= 1

        return get_edge_interval()
