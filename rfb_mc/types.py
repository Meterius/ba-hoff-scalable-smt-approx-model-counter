from dataclasses import dataclass
from typing import NamedTuple, Optional, Counter, Any

RfBmcTask = NamedTuple("RfBmcTask", [
    ("rf_module_uid", str), ("rf_module_param", Any), ("a", int), ("q", int)
])
""" Parameters for a single restrictive formula bounded model counting call """

RfBmcResult = NamedTuple("RfBmcResult", [("bmc", Optional[int])])
""" Result of a single restrictive formula bounded model counting call """


@dataclass
class Params:
    # keys represent bit widths and values/counts the amount of variable with the given bit width
    bit_width_counter: Counter[int]

    def __post_init__(self):
        if any([bw <= 0 for bw in self.bit_width_counter.keys()]):
            raise ValueError("bit_width_counter cannot contain bit widths (keys) that are <= 0")

        if any([n < 0 for n in self.bit_width_counter.values()]):
            raise ValueError("bit_width_counter cannot contain negative counts")
