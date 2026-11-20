#!/usr/bin/env python3
"""Summarise IX_KERNEL_HINTS_TRACE output for one run.

  analyze.py CHECK.log TRACE.jsonl HINTS.tsv NAMES.tsv OUT.json

CHECK.log gives the claim order (`[aiur] execute NAME` / `verified claim`);
TRACE.jsonl has one line per accepted claim, in the same order.
"""
import collections
import json
import re
import sys

log_path, trace_path, hints_path, names_path, out_path = sys.argv[1:6]
hints = dict(l.rstrip("\n").split("\t") for l in open(hints_path))
names = {}
for line in open(names_path):
    n, a = line.rstrip("\n").split("\t")
    names.setdefault(a, n)

claims = []
current = None
for line in open(log_path):
    m = re.match(r"\[aiur\] execute (.*)", line)
    if m:
        current = m.group(1).strip()
        continue
    m = re.match(r"verified claim in ([\d.]+)s \((\d+) queries, (\d+) instructions\)", line)
    if m and current:
        claims.append(current)
        current = None
traces = [json.loads(l) for l in open(trace_path)]
assert len(traces) == len(claims), (len(traces), len(claims))

DEFEQ = ("KernelDefEq::",)
total_rows = collections.Counter()
pairs = collections.Counter()
pair_rows = collections.Counter()
branch = collections.Counter()
per_claim = []
const_rows = collections.Counter()


def rank(addr):
    h = hints.get(addr)
    if h is None:
        return None
    return 0 if h == "opaque" else 0xFFFFFFFF if h == "abbrev" else 1 + int(h)


for name, t in zip(claims, traces):
    rows = {f: v[0] for f, v in t["functions"].items()}
    total = sum(rows.values())
    defeq = sum(v for f, v in rows.items() if f.startswith(DEFEQ))
    whnf = sum(v for f, v in rows.items() if f.startswith("KernelWhnf::"))
    total_rows.update(rows)
    steps = t["steps"]
    for a, b, fuel, ok, uses in steps:
        key = tuple(sorted((a, b)))
        pairs[key] += 1
        ra, rb = rank(a), rank(b)
        if ra is None or rb is None:
            branch["one side not a hinted definition"] += 1
        elif ra > rb:
            branch["unfold a (higher rank)"] += 1
        elif rb > ra:
            branch["unfold b (higher rank)"] += 1
        else:
            branch["equal ranks: unfold both"] += 1
        for x in (a, b):
            const_rows[x] += 1
    per_claim.append({"claim": name, "rows": total, "defeq_rows": defeq,
                      "whnf_rows": whnf, "steps": len(steps),
                      "hint_loads": len(t["hint_loads"]),
                      "instructions": t["instructions"]})

grand = sum(total_rows.values())
by_module = collections.Counter()
for f, v in total_rows.items():
    by_module[f.split("::")[0]] += v
out = {
    "claims": len(claims),
    "total_rows": grand,
    "rows_by_module": by_module.most_common(),
    "top_functions": total_rows.most_common(40),
    "defeq_functions": sorted(((f, v) for f, v in total_rows.items() if f.startswith(DEFEQ)),
                              key=lambda x: -x[1]),
    "lazy_delta_steps": sum(pairs.values()),
    "branches": branch.most_common(),
    "top_pairs": [[names.get(a, a), names.get(b, b), hints.get(a), hints.get(b), n]
                  for (a, b), n in pairs.most_common(40)],
    "top_head_constants": [[names.get(a, a), hints.get(a), n] for a, n in const_rows.most_common(40)],
    "per_claim": per_claim,
}
json.dump(out, open(out_path, "w"), indent=1)
print(json.dumps({k: out[k] for k in ("claims", "total_rows", "lazy_delta_steps", "branches")}))
