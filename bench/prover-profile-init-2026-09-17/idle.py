"""Kernel-idle time inside one phase, attributed to the host spans active then."""
import sys, json, importlib.util
spec = importlib.util.spec_from_file_location("spans", sys.argv[1]); sp = importlib.util.module_from_spec(spec); spec.loader.exec_module(sp)
d = sys.argv[2]; phase = sys.argv[3]
S = sp.load(f"{d}/spans.jsonl")
kern = []
for line in open(f"{d}/cuda.jsonl"):
    a = json.loads(line)
    if a.get("kind") == "kernel": kern.append((a["start"], a["end"]))
def merge(iv):
    out = []
    for a, b in sorted(iv):
        if out and a <= out[-1][1]: out[-1][1] = max(out[-1][1], b)
        else: out.append([a, b])
    return [tuple(x) for x in out]
def inter(x, y):
    out = []; i = j = 0; x = merge(x); y = merge(y)
    while i < len(x) and j < len(y):
        a = max(x[i][0], y[j][0]); b = min(x[i][1], y[j][1])
        if a < b: out.append((a, b))
        if x[i][1] < y[j][1]: i += 1
        else: j += 1
    return out
def sec(iv): return sum(b - a for a, b in merge(iv)) / 1e9
kern = merge(kern)
ph = merge(iv for s in S if s["name"] == phase for iv in s["intervals"])
busy = inter(ph, kern)
# complement of kernels within the phase
idle = []
for a, b in ph:
    t = a
    for ka, kb in kern:
        if kb <= a: continue
        if ka >= b: break
        if ka > t: idle.append((t, ka))
        t = max(t, kb)
    if t < b: idle.append((t, b))
print(f"{phase}: union {sec(ph):.2f}s, kernel {sec(busy):.2f}s, idle {sec(idle):.2f}s")
by = {}
for s in S:
    if s["name"] in (phase,): continue
    by.setdefault(s["name"], []).extend(s["intervals"])
rows = [(n, sec(inter(iv, idle))) for n, iv in by.items()]
covered = merge(iv for n, ivs in by.items() if n.startswith(("aiur/codegen_", "aiur/cpu_", "aiur/witness")) for iv in ivs)
print(f"  idle with no witness/packing span active: {sec(idle) - sec(inter(covered, idle)):.2f}s")
for n, v in sorted(rows, key=lambda r: -r[1])[:14]:
    if v > 0.05: print(f"  {n:30s} {v:6.2f}s")
