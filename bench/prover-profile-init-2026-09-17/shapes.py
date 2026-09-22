"""Kernel time by the host span that launched it: NTT stages and hashing per
LDE shape, FRI sub-phases and commit sources with their kernel-idle time.
Needs the collector's system thread ids. Usage: shapes.py <profile dir>"""
import sys, json, bisect
from collections import defaultdict
d = sys.argv[1]
defs, live, spans = {}, {}, []          # spans: (tid, start, end, name, fields)
for line in open(f"{d}/spans.jsonl"):
    e = json.loads(line)
    if e["event"] == "new": defs[e["id"]] = (e["name"], e.get("fields") or {})
    elif e["event"] == "enter": live[(e["id"], e["tid"])] = e["ts_ns"]
    elif e["event"] == "exit":
        t0 = live.pop((e["id"], e["tid"]), None)
        if t0 is not None and e["id"] in defs:
            name, fields = defs[e["id"]]; spans.append((int(e["tid"]), t0, e["ts_ns"], name, fields))
by_tid = defaultdict(list)
for s in spans: by_tid[s[0]].append(s)
for tid in by_tid: by_tid[tid].sort(key=lambda s: s[1])
# CUPTI's thread ids are pthread ids, which the short-lived commit threads
# reuse, so a launch is attributed by time alone: the innermost span with
# the prefix active on any thread at the launch instant. Concurrent spans
# on different threads make that ambiguous; the count is reported.
ambiguous = 0
def innermost(_tid, t, prefix):
    global ambiguous
    found = []
    for tid, lst in by_tid.items():
        for s in lst:
            if s[1] > t: break
            if s[2] >= t and s[3].startswith(prefix): found.append(s)
    if len({s[0] for s in found}) > 1: ambiguous += 1
    return min(found, key=lambda s: s[2] - s[1]) if found else None
launch = {}; kernels = []; launches = []
for line in open(f"{d}/cuda.jsonl"):
    a = json.loads(line)
    if a["kind"] == "runtime" and a["name"].startswith("cudaLaunchKernel"):
        launch[a["correlation"]] = (a["tid"], a["start"]); launches.append((a["tid"], a["start"]))
    elif a["kind"] == "kernel": kernels.append(a)
# CUPTI records pthread ids, the span collector Linux tids. A thread keeps
# both for its life, so pair them by co-occurrence: a launch is credited to
# every Linux tid with a cuda/* span active at that instant, and each CUPTI
# tid takes the Linux tid it co-occurs with most.
cuda_spans = defaultdict(list)
for s in spans:
    if s[3].startswith("cuda/"): cuda_spans[s[0]].append((s[1], s[2]))
for ltid in cuda_spans: cuda_spans[ltid].sort()
cooc = defaultdict(int)
for ptid, t in launches:
    for ltid, iv in cuda_spans.items():
        i = bisect.bisect_right(iv, (t, float("inf"))) - 1
        if i >= 0 and iv[i][0] <= t <= iv[i][1]: cooc[(ptid, ltid)] += 1
best = {}
for (ptid, ltid), n in cooc.items():
    if ptid not in best or n > best[ptid][1]: best[ptid] = (ltid, n)
tid_map = {p: l for p, (l, n) in best.items()}
claimed = defaultdict(list)
for p, (l, n) in best.items(): claimed[l].append((p, n))
print("thread pairs:", len(tid_map), "linux tids claimed by more than one CUPTI tid:", sum(1 for v in claimed.values() if len(v) > 1))
launch = {c: (tid_map.get(p, p), t) for c, (p, t) in launch.items()}
def family(n):
    n = n.split("kernels_cu_")[-1]
    for f in ("radix8_dif", "radix4_dif", "radix2_dif_tail", "radix2_dif", "blake3_hash_rows", "blake3_hash_short", "blake3_hash_digest", "evaluate_quotient", "accumulate_reduced", "lookup_messages", "gather_resident"):
        if f in n: return f
    return "other"
table = defaultdict(lambda: [0.0, 0]); unmatched = 0.0
for k in kernels:
    fam = family(k["name"]); dur = (k["end"] - k["start"]) / 1e9
    l = launch.get(k["correlation"])
    s = innermost(l[0], l[1], "cuda/") if l else None
    if s is None and l: s = innermost(l[0], l[1], "stark/")
    if s is None: unmatched += dur; key = (fam, "?", "", "", ""); 
    else:
        f = s[4]; key = (fam, s[3], f.get("kind", f.get("path", "")), f.get("height", ""), f.get("width", f.get("num_lookups", "")))
    table[key][0] += dur; table[key][1] += 1
print(f"kernel time unmatched to a cuda/* span: {unmatched:.2f}s; launches with concurrent candidate spans on several threads: {ambiguous}")
print(f"{'family':20s} {'span':18s} {'kind':10s} {'height':>9s} {'width':>7s} {'sum s':>7s} {'n':>6s}")
for key, (t, n) in sorted(table.items(), key=lambda kv: -kv[1][0])[:40]:
    print(f"{key[0]:20s} {key[1]:18s} {str(key[2]):10s} {str(key[3]):>9s} {str(key[4]):>7s} {t:7.2f} {n:6d}")
# phase unions with kernel-idle
kern = sorted((k["start"], k["end"]) for k in kernels); merged = []
for a, b in kern:
    if merged and a <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], b)
    else: merged.append([a, b])
starts = [m[0] for m in merged]
def busy_within(a, b):
    tot = 0; i = bisect.bisect_right(starts, a) - 1
    if i < 0: i = 0
    while i < len(merged) and merged[i][0] < b:
        lo, hi = max(a, merged[i][0]), min(b, merged[i][1])
        if lo < hi: tot += hi - lo
        i += 1
    return tot
def union(iv):
    out = []
    for a, b in sorted(iv):
        if out and a <= out[-1][1]: out[-1][1] = max(out[-1][1], b)
        else: out.append([a, b])
    return out
print()
groups = defaultdict(list)
for s in spans:
    if s[3].startswith("stark/fri_") or s[3] in ("stark/commit_merkle", "stark/fri_open"):
        groups[s[3]].append((s[1], s[2]))
    if s[3] == "stark/commit_source":
        groups[(s[3], s[4].get("kind"), s[4].get("height"), s[4].get("width"))].append((s[1], s[2]))
rows = []
for key, iv in groups.items():
    u = union(iv); tot = sum(b - a for a, b in u); busy = sum(busy_within(a, b) for a, b in u)
    rows.append((str(key), tot / 1e9, (tot - busy) / 1e9, len(iv)))
for key, tot, idle, n in sorted(rows, key=lambda r: -r[2])[:30]:
    print(f"{key:60s} union {tot:6.2f}s idle {idle:6.2f}s n={n}")
