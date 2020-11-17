from hash_generation_finder.uniform_pairwise_independent_hash_sets.incomplete_bit_count_domain_based.upi_sets_n2k3_exec import upi_sets_n2k3
from hash_generation_finder.uniform_pairwise_independent_hash_sets.incomplete_bit_count_domain_based.upi_sets_n3k4_exec import upi_sets_n3k4
from hash_generation_finder.utility import is_hash_set_dual_extension
from itertools import combinations, product

# Runs some filtering on the already generated upi hashing generation

if __name__ == "__main__":
    for (i, H1), (j, H2) in product(enumerate(upi_sets_n2k3), enumerate(upi_sets_n3k4)):
        if is_hash_set_dual_extension(H1, H2):
            print(i + 1, j + 1)
