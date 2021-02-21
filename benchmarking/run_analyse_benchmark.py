from rfb_mc.implementation.eamp.eamp_edge_scheduler import *


def read_benchmark_file(content: str):
    lines = content.splitlines()

    benchmark_map = {}

    for line in lines:
        benchmark, benchmark_idx, duration, result = line.split(";")

        entry = benchmark_map.get(benchmark, {"results": [], "durations": []})

        literal_result = eval(result)
        entry["results"].append(literal_result)
        literal_duration = eval(duration)
        entry["durations"].append(literal_duration)

        benchmark_map[benchmark] = entry

    for entry in benchmark_map.values():
        entry["avg_duration"] = sum(entry["durations"]) / len(entry["durations"])
        entry["result"] = Counter(entry["results"]).most_common()[0][0]

    return benchmark_map

if __name__ == "__main__":
    file_a = ""
    file_b = ""

    with open(file_a, "r") as f:
        content_a = f.read()
    with open(file_b, "r") as f:
        content_b = f.read()

    a = read_benchmark_file(content_a)
    b = read_benchmark_file(content_b)

    for bm in a:
        print(f"---- {bm} ----")
        print("Content A:")
        print(a[bm]["avg_duration"])
        print(a[bm]["result"])
        print("Content B:")
        print(b[bm]["avg_duration"])
        print(b[bm]["result"])
