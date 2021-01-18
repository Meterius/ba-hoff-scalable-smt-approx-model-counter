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
    with open("C:\\Users\\jonah\\Desktop\\output_rfmbi_full\\benchmark_results.txt", "r") as f:
        content_rfmbi = f.read()
    with open("C:\\Users\\jonah\\Desktop\\output_estimate\\benchmark_results.txt", "r") as f:
        content_est = f.read()

    est = read_benchmark_file(content_est)
    rfmbi = read_benchmark_file(content_rfmbi)

    for bm in est:
        print("Estimate:")
        print(est[bm]["avg_duration"])
        print(est[bm]["result"])
        print("Rfmbi:")
        print(rfmbi[bm]["avg_duration"])
        print(rfmbi[bm]["result"])
