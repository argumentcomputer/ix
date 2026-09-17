import sys, json, re, importlib.util, bisect
from collections import defaultdict
d = sys.argv[1]
# reuse shapes.py's machinery by exec'ing it with output suppressed
import io, contextlib
src = open(sys.argv[2]).read()
g = {"__name__": "shapes", "sys": sys}
sys.argv = [sys.argv[2], d]
with contextlib.redirect_stdout(io.StringIO()): exec(src, g)
table = g["table"]; spans = g["spans"]; union = g["union"]; busy_within = g["busy_within"]
narrow = wide = unmatched = 0.0; per = defaultdict(float)
for (fam, span, kind, height, width), (t, n) in table.items():
    if fam != "radix2_dif": continue
    if span == "?": unmatched += t; per["unmatched (no cuda/* span on that thread)"] += t
    elif span == "cuda/quotient_lde": narrow += t; per["quotient codeword"] += t
    elif span == "cuda/lookup_lde": narrow += t; per["lookup LDE (narrow widths)"] += t
    elif span == "cuda/lde" and width != "" and int(width) < 8: narrow += t; per[f"main trace width {width}"] += t
    else: wide += t; per["residue stage of a wide transform"] += t
print(f"radix-2 total {narrow+wide+unmatched:.2f}s: narrow {narrow:.2f}s, wide residue {wide:.2f}s, unmatched {unmatched:.2f}s")
for k, v in sorted(per.items(), key=lambda kv: -kv[1]): print(f"  {k:44s} {v:6.2f}s")
tot = defaultdict(lambda: [0.0, 0.0])
for s in spans:
    if s[3] == "stark/commit_source":
        u = [(s[1], s[2])]; t = s[2] - s[1]; b = busy_within(s[1], s[2]); k = s[4].get("kind")
        tot[k][0] += t / 1e9; tot[k][1] += (t - b) / 1e9
for k, (t, i) in tot.items(): print(f"commit sources {k:12s} sum of spans {t:6.2f}s, idle inside {i:6.2f}s")
for name in ("stark/commit_merkle", "stark/fri_open", "stark/fri_streamed", "stark/fri_prepare", "stark/fri_interpolate", "stark/fri_observe_openings", "stark/fri_reduce", "stark/fri_prove", "stark/fri_round_commit", "stark/fri_commit_grind", "stark/fri_queries", "stark/fri_query_grind", "stark/fri_input_openings", "stark/fri_commit_phase_opening", "cuda/fri_fold"):
    iv = [(s[1], s[2]) for s in spans if s[3] == name]
    if not iv: print(f"{name}: absent"); continue
    u = union(iv); t = sum(b - a for a, b in u); b = sum(busy_within(a, b) for a, b in u)
    print(f"{name:32s} union {t/1e9:6.2f}s idle {(t-b)/1e9:6.2f}s n={len(iv)}")
