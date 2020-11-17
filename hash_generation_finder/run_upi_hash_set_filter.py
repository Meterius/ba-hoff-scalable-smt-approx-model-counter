from hash_generation_finder.uniform_pairwise_independent_hash_sets.incomplete_bit_count_domain_based.upi_sets_n2k3_exec import upi_sets_n2k3
from hash_generation_finder.uniform_pairwise_independent_hash_sets.incomplete_bit_count_domain_based.upi_sets_n3k4_exec import upi_sets_n3k4
from hash_generation_finder.utility import is_hash_set_dual_extension, is_hash_set_symmetric, \
    get_hash_set_dual_extension_via_paired_inverses, convert_hash_set_to_tuple_representation
from hash_generation_finder.old_code.hashing import is_pairwise_independent_hash_set
from itertools import combinations, product

# Runs some filtering on the already generated upi hashing generation

if __name__ == "__main__":
    """
    for (i, H1), (j, H2) in product(enumerate(upi_sets_n2k3), enumerate(upi_sets_n3k4)):
        if is_hash_set_dual_extension(H1, H2):
            print(i + 1, j + 1)
    """

    """
    for (i, H1) in enumerate(upi_sets_n3k4):
        if is_hash_set_symmetric(H1):
            print(i + 1)
    """

    """
    for (i, H1), (j, H2) in product(enumerate(upi_sets_n2k3), enumerate(upi_sets_n2k3)):
        H = get_hash_set_dual_extension_via_paired_inverses(H1, H2)
        HC = convert_hash_set_to_tuple_representation(H)

        if is_pairwise_independent_hash_set(len(HC[0]), HC):
            print("-----------------------------")
            print("Using H1 as")
            for h in convert_hash_set_to_tuple_representation(H1): print(h)
            print("Using H2 as")
            for h in convert_hash_set_to_tuple_representation(H2): print(h)
            print("Generates UPI")
            for h in HC: print(h)
            print(i + 1, j + 1)
    """
