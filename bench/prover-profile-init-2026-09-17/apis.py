"""CUDA runtime API calls active during a phase's kernel-idle time."""
import sys, json, bisect
from collections import defaultdict
d, phase = sys.argv[1], sys.argv[2]
defs, live, ph = {}, {}, []
for line in open(f"{d}/spans.jsonl"):
    e = json.loads(line)
    if e["event"] == "new": defs[e["id"]] = e["name"]
    elif e["event"] == "enter": live[(e["id"], e["tid"])] = e["ts_ns"]
    elif e["event"] == "exit":
        t0 = live.pop((e["id"], e["tid"]), None)
        if t0 is not None and defs.get(e["id"]) == phase: ph.append((t0, e["ts_ns"]))
kern, apis = [], []
for line in open(f"{d}/cuda.jsonl"):
    a = json.loads(line)
    if a["kind"] == "kernel": kern.append((a["start"], a["end"]))
    elif a["kind"] in ("runtime", "driver"): apis.append((a["start"], a["end"], a["name"]))
def merge(iv):
    out = []
    for a, b in sorted(iv):
        if out and a <= out[-1][1]: out[-1][1] = max(out[-1][1], b)
        else: out.append([a, b])
    return out
kern = merge(kern); ph = merge(ph)
idle = []
for a, b in ph:
    t = a
    for ka, kb in kern:
        if kb <= a: continue
        if ka >= b: break
        if ka > t: idle.append((t, ka))
        t = max(t, kb)
    if t < b: idle.append((t, b))
idle = merge(idle); starts = [i[0] for i in idle]
def overlap(a, b):
    tot = 0; i = max(bisect.bisect_right(starts, a) - 1, 0)
    while i < len(idle) and idle[i][0] < b:
        lo, hi = max(a, idle[i][0]), min(b, idle[i][1])
        if lo < hi: tot += hi - lo
        i += 1
    return tot
by = defaultdict(lambda: [0, 0]); covered = []
for a, b, n in apis:
    o = overlap(a, b)
    if o: by[n][0] += o; by[n][1] += 1; covered.append((a, b))
tot_idle = sum(b - a for a, b in idle)
cov = merge(covered); cov_t = sum(overlap(a, b) for a, b in cov)
print(f"{phase}: idle {tot_idle/1e9:.2f}s, with a CUDA API call active {cov_t/1e9:.2f}s, pure host {(tot_idle-cov_t)/1e9:.2f}s")
for n, (t, c) in sorted(by.items(), key=lambda kv: -kv[1][0])[:8]: print(f"  {n:40s} {t/1e9:6.2f}s n={c}")
