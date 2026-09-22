#!/usr/bin/env python3
"""One row per run directory: wall, CPU, RSS, GPU utilization and the span
unions that the seed work touches. Usage: compare.py <spans.py> <run dir>..."""
import importlib.util, re, sys, csv
spec = importlib.util.spec_from_file_location("spans", sys.argv[1])
spans = importlib.util.module_from_spec(spec); spec.loader.exec_module(spans)
NAMES = ["aiur/prove_planned", "stark/stage1_commit", "stark/lookup_construction",
         "stark/quotient", "stark/fri_open", "aiur/witness", "aiur/cpu_witness",
         "aiur/codegen_seeds", "aiur/codegen_device_rows", "aiur/execute_ixvm"]
def unions(path):
    by = {}
    for s in spans.load(path):
        by.setdefault(s["name"], []).extend(s["intervals"])
    return {n: (spans.union(by[n]) / 1e9 if n in by else 0.0, len(by.get(n, []))) for n in NAMES}
rows = []
for d in sys.argv[2:]:
    err = open(f"{d}/stderr.log").read()
    wall = re.search(r"Elapsed.*?(\d+):(\d+\.\d+)", err)
    wall_s = int(wall.group(1)) * 60 + float(wall.group(2)) if wall else float("nan")
    user = float(re.search(r"User time \(seconds\): ([\d.]+)", err).group(1))
    rss = int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", err).group(1)) / 2**20
    util = [float(r[2]) for r in csv.reader(open(f"{d}/gpu.csv")) if len(r) == 3]
    u = unions(f"{d}/spans.jsonl")
    rows.append((d.rstrip("/").split("/")[-1], wall_s, user, rss, sum(util) / max(len(util), 1), u))
print(f"{'run':34s} {'wall s':>7s} {'cpu s':>7s} {'rss GiB':>8s} {'gpu %':>6s} " + " ".join(f"{n.split('/')[1][:14]:>14s}" for n in NAMES))
for name, wall, user, rss, util, u in rows:
    print(f"{name:34s} {wall:7.1f} {user:7.0f} {rss:8.1f} {util:6.1f} " + " ".join(f"{u[n][0]:14.1f}" for n in NAMES))
print("spans n:")
for name, *_, u in rows:
    print(f"{name:34s} {'':31s}" + " ".join(f"{u[n][1]:14d}" for n in NAMES))
