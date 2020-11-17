from hash_generation_finder.old_code.hashing import is_pairwise_independent_hash_set
from hash_generation_finder.upi_hashing import generate_upi_hash_sets_via_solver, generate_upi_hash_sets, convert_hash_set_to_tuple_representation
import os

if __name__ == "__main__":
    n = 3
    k = n + 1

    code_dir = os.path.dirname(__file__)
    file_base = os.path.join(code_dir, "output", "upi_sets_n{n}k{k}".format(n=n, k=k))

    file_listed = file_base + "_listed.txt"
    file_exec = file_base + "_exec.py"

    with open(file_listed, "w") as fl, open(file_exec, "w") as fe:
        fe.write("import numpy as np\n\n\n")
        fe.write("upi_sets_n{n}k{k} = []\n".format(n=n, k=k))

        for H in generate_upi_hash_sets_via_solver(n, k):
            HC = convert_hash_set_to_tuple_representation(H)

            fe.write("upi_sets_n{n}k{k}.append(np.".format(n=n, k=k))
            fe.write(repr(H).replace("\n", "").replace("\t", "").replace("\r", "").replace(" ", "").replace(",", ", "))
            fe.write(")\n")

            fl.write(str(convert_hash_set_to_tuple_representation(H)))
            fl.write("\n")
