from hash_generation_finder.upi_hashing import generate_upi_hash_sets_via_solver, \
    convert_hash_set_to_tuple_representation
from hash_generation_finder.utility import convert_hash_set_to_bit_table, get_hash_set_identifier
import os

if __name__ == "__main__":
    n = 3
    k = n + 1

    hash_sets = generate_upi_hash_sets_via_solver(n, k)

    code_dir = os.path.dirname(__file__)
    file_base = os.path.join(code_dir, "output", "upi_sets_n{n}k{k}".format(n=n, k=k))

    file_listed_tables = file_base + "_tabled.txt"
    file_listed = file_base + "_listed.txt"
    file_exec = file_base + "_exec.py"

    with open(file_listed, "w") as fl, open(file_exec, "w") as fe, open(file_listed_tables, "w") as ft:
        fe.write("import numpy as np\n\n\n")
        fe.write("upi_sets_n{n}k{k} = []\n".format(n=n, k=k))

        for i, H in enumerate(hash_sets):
            HC = convert_hash_set_to_tuple_representation(H)
            table = convert_hash_set_to_bit_table(H)
            ident = get_hash_set_identifier(HC)

            fe_data = "upi_sets_n{n}k{k}.append(np.".format(n=n, k=k) \
                      + repr(H).replace("\n", "").replace("\t", "").replace("\r", "")\
                      .replace(" ", "").replace(",", ", ") \
                      + ")\n"

            fl_data = f"{i+1} ({ident}): " + str(convert_hash_set_to_tuple_representation(H)) + "\n"

            ft_data = f"{i+1} ({ident}):\n"
            for line in table:
                ft_data += "    " + line + "\n"
            ft_data += "\n"

            fe.write(fe_data)
            fl.write(fl_data)
            ft.write(ft_data)
