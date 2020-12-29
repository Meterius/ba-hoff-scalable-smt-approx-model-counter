from fractions import Fraction
from abc import ABC, abstractmethod
from typing import Generic, TypeVar, Tuple
from itertools import dropwhile


from rfb_mc.types import Params


class RestrictiveFormulaParamsBase(ABC):
    @abstractmethod
    def get_key(self) -> str:
        """
        Returns a string hash of this object that can differentiate
        every different parameter.
        """

        raise NotImplementedError()

RestrictiveFormulaParams = TypeVar("RestrictiveFormulaParams", bound=RestrictiveFormulaParamsBase)
# parameter that determines all formula generation related values

RestrictiveFormulaProperties = TypeVar("RestrictiveFormulaProperties")
# properties of the restrictive formula that are determined by the parameters

RestrictiveFormulaInstanceParams = TypeVar("RestrictiveFormulaInstanceParams")


# values that parameterize a specific instance generated by the module and will be used by
# the runner implementations to reconstruct the formula in the format of which ever solver is used


class RestrictiveFormulaModuleBase(
    Generic[RestrictiveFormulaParams, RestrictiveFormulaProperties, RestrictiveFormulaInstanceParams],
    ABC,
):
    @classmethod
    @abstractmethod
    def get_uid(cls) -> str:
        """
        UID of the restrictive formula module that needs to be deterministic and
        unique across all other restrictive formula module implementations.

        An abbreviation of the name that is unlikely to be reused is suggested and possibly a
        version number in order to differentiate between different generations of the same module.
        """

        raise NotImplementedError()

    @classmethod
    @abstractmethod
    def get_restrictive_formula_properties(
        cls,
        params: Params,
        restrictive_formula_params: RestrictiveFormulaParams,
    ) -> RestrictiveFormulaProperties:
        """
        Returns properties that the restrictive formula generation posses with the given parameters.
        """

        raise NotImplementedError()


class UPI_RestrictiveFormulaProperties:
    """
    Property format for UPI_RestrictiveFormulaModuleBase implementations
    """

    def __init__(self, probability: Fraction):
        self.probability: Fraction = probability
        """
        probability for each formula assignment to be included in the model set of the generated restrictive formula
        instance
        """

UPI_RestrictiveFormulaPropertiesType = TypeVar(
    "UPI_RestrictiveFormulaPropertiesType", bound=UPI_RestrictiveFormulaProperties
)


class UPI_RestrictiveFormulaModuleBase(
    Generic[RestrictiveFormulaParams, UPI_RestrictiveFormulaPropertiesType, RestrictiveFormulaInstanceParams],
    ABC,
    RestrictiveFormulaModuleBase[
        RestrictiveFormulaParams, UPI_RestrictiveFormulaPropertiesType, RestrictiveFormulaInstanceParams
    ],
):
    """
    Modules that implement restrictive formula generation of which
    the events that any two variable assignments are satisfying are independent (i.e. the set of these kind of events is
    pairwise independent) and each variable assignment has exactly the same probability of being satisfying.

    UPI = Uniform Pairwise Independent
    """

    pass


class DPIS_UPI_RestrictiveFormulaParams(RestrictiveFormulaParamsBase):
    def __init__(self, c: Tuple[int, ...]):
        self.c: Tuple[int, ...] = c

    def get_key(self) -> str:
        # c that has dropped all zeros at the end
        c = tuple(reversed(
            dropwhile(lambda cj: cj == 0, reversed(self.c)),
        ))

        return str(c)


class DPIS_UPI_RestrictiveFormulaModuleBase(
    Generic[UPI_RestrictiveFormulaPropertiesType, RestrictiveFormulaInstanceParams],
    ABC,
    UPI_RestrictiveFormulaModuleBase[
        DPIS_UPI_RestrictiveFormulaParams,
        UPI_RestrictiveFormulaPropertiesType,
        RestrictiveFormulaInstanceParams,
    ],
):
    """
    Modules that implement UPI restrictive formula generation based on the UPI_RestrictiveFormulaModuleBase and
    use as parameters a sequence of integers which have the property that incrementing an entry decreases the inclusion
    probability and incrementing the entry at a higher index will decrease the probability more than incrementing it
    on a lower entry.

    DPIS = Decreasing Probability Integer Sequence
    """

    def get_j_