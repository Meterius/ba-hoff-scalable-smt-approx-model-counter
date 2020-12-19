from ast import literal_eval
import os
from collections import Counter


def read_benchmark_file(content: str):
    lines = content.splitlines()

    benchmark_map = {}

    for line in lines:
        benchmark, benchmark_idx, duration, result = line.split(";")

        entry = benchmark_map.get(benchmark, {"results": [], "durations": []})

        entry["results"].append(literal_eval(result))
        entry["durations"].append(literal_eval(duration))

        benchmark_map[benchmark] = entry

    for entry in benchmark_map.values():
        entry["avg_duration"] = sum(entry["durations"]) / len(entry["durations"])
        entry["result"] = Counter(entry["results"]).most_common()[0][0]

    return benchmark_map


if __name__ == "__main__":
    code_dir = os.path.dirname(__file__)
    ib_file_name = os.path.join(code_dir, "output", "integrator_benchmark_results.txt")
    bc_file_name = os.path.join(code_dir, "output", "branching_counter_benchmark_results.txt")

    with open(ib_file_name, "r") as fbc:
        ib_content = fbc.read()

    ib_bm = read_benchmark_file(ib_content)
    ib_bms = sorted(ib_bm.keys(), key=lambda bm: ib_bm[bm]["avg_duration"])

    print(f"Benchmarks {ib_bms}")

    for benchmark in ib_bms:
        print(f"{benchmark}:")
        print("Avg. Duration: ", ib_bm[benchmark]["avg_duration"])
        print("Most Occurred Result: ", ib_bm[benchmark]["result"])
