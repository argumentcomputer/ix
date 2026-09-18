"""Per-leaf profiled cost (.ixprof) against the records the lanes run measured."""
import re, struct, sys
from collections import defaultdict

PROF = "/home/sam/benchdata/flt/anthropic-flt.ixprof"
IXES = "/home/sam/benchdata/flt/anthropic-flt-572.ixes"
ERR = "/home/sam/benchdata/flt/runs/flt572-lanes4-exec3/lanes.err"
ERR256 = "/home/sam/benchdata/flt/runs/flt572-lanes4-exec3/lanes-resume256.err"

# .ixprof: magic(8) version(u32) n(u32) then n × 80-byte block records.
b = open(PROF, "rb").read()
n = struct.unpack_from("<I", b, 12)[0]
p = 16
prof = {}
for _ in range(n):
    addr = b[p:p + 32].hex()
    hb, size, cc, subst, whnf, defeq, nat, intern = struct.unpack_from("<QIIQQQQQ", b, p + 32)
    prof[addr] = (hb, size, cc, subst, whnf, defeq, nat, intern)
    p += 88
print(f"profile: {n} blocks, total heartbeats {sum(v[0] for v in prof.values()):.3e}")

# .ixes: leaves with their block addresses.
m = open(IXES, "rb").read(); q = 8 + 16
nl = struct.unpack_from("<I", m, q)[0]; q += 4
leaves = []
for i in range(nl):
    q += 4 + 24
    tag = m[q]; q += 1 + (32 if tag == 1 else 0)
    blen = struct.unpack_from("<I", m, q)[0]; q += 4
    leaves.append([m[q + 32 * k:q + 32 * k + 32].hex() for k in range(blen)]); q += 32 * blen
    flen = struct.unpack_from("<I", m, q)[0]; q += 4 + 32 * flen

# Measured records per claim id (the original run, plus leaf 570 whole from the restart).
rec = {}
for path in (ERR, ERR256):
    for line in open(path, errors="replace"):
        mm = re.search(r"claim (\d+) executed in [\d.]+s, record (\d+) B", line)
        if mm:
            k = int(mm.group(1))
            if k < 572:
                rec[k] = int(mm.group(2)) / 2**30
print(f"measured records: {len(rec)} claims")

rows = []
for i, blocks in enumerate(leaves):
    hb = sum(prof[a][0] for a in blocks if a in prof)
    size = sum(prof[a][1] for a in blocks if a in prof)
    whnf = sum(prof[a][4] for a in blocks if a in prof)
    defeq = sum(prof[a][5] for a in blocks if a in prof)
    rows.append((i, hb, size, whnf, defeq, rec.get(i)))

import statistics as st
xs = [r[1] for r in rows if r[5]]; ys = [r[5] for r in rows if r[5]]
def corr(a, b):
    ma, mb = st.mean(a), st.mean(b)
    cov = sum((x - ma) * (y - mb) for x, y in zip(a, b))
    return cov / (sum((x - ma)**2 for x in a) * sum((y - mb)**2 for y in b)) ** 0.5
print(f"correlation heartbeats vs record: r = {corr(xs, ys):.3f}")
print(f"correlation serialized bytes vs record: r = {corr([r[2] for r in rows if r[5]], ys):.3f}")
k = st.mean(ys) / st.mean(xs)
print(f"record bytes per heartbeat (mean fit): {k * 2**30:.1f} B")

print("\ntop 10 leaves by profiled heartbeats (rank, leaf, heartbeats, bytes, measured record, predicted from heartbeats):")
for r_, row in enumerate(sorted(rows, key=lambda r: -r[1])[:10], 1):
    i, hb, size, whnf, defeq, rc = row
    print(f"  {r_:2d}  leaf {i:3d}  hb {hb:.3e}  {size/1e6:5.1f} MB  record {rc if rc else float('nan'):6.1f} GiB  predicted {k*hb:6.1f} GiB")
rank = sorted(rows, key=lambda r: -r[1])
pos = [r[0] for r in rank].index(570) + 1
print(f"\nleaf 570 rank by heartbeats: {pos} of {nl}; heartbeats/bytes vs median leaf: "
      f"{rows[570][1]/rows[570][2] / st.median(r[1]/r[2] for r in rows if r[2]):.1f}x")
print("\ntop 10 leaves by measured record (leaf, record, heartbeat rank):")
for row in sorted((r for r in rows if r[5]), key=lambda r: -r[5])[:10]:
    print(f"  leaf {row[0]:3d}  {row[5]:6.1f} GiB  hb rank {[r[0] for r in rank].index(row[0]) + 1}")

# Two-term fits: record ~ a*bytes + b*counter, ordinary least squares via normal equations.
names = ["heartbeats", "subst", "whnf", "def_eq", "nat_arith", "intern"]
idx = [0, 3, 4, 5, 6, 7]
data = [(i, sum(prof[a][1] for a in blocks if a in prof), [sum(prof[a][j] for a in blocks if a in prof) for j in idx], rec[i]) for i, blocks in enumerate(leaves) if i in rec]
def solve2(xs1, xs2, ys):
    s11 = sum(x*x for x in xs1); s22 = sum(x*x for x in xs2); s12 = sum(x*y for x, y in zip(xs1, xs2))
    s1y = sum(x*y for x, y in zip(xs1, ys)); s2y = sum(x*y for x, y in zip(xs2, ys))
    det = s11*s22 - s12*s12
    return (s22*s1y - s12*s2y)/det, (s11*s2y - s12*s1y)/det
ys = [d[3] for d in data]; bs = [d[1] for d in data]
print("\nsingle counters, correlation with record, and leaf 570 rank by that counter:")
for k, nm in enumerate(names):
    xs = [d[2][k] for d in data]
    order = sorted(data, key=lambda d: -d[2][k]); r570 = [d[0] for d in order].index(570) + 1
    print(f"  {nm:10s} r = {corr(xs, ys):.3f}   leaf 570 rank {r570:3d}")
print("\ntwo-term fits record = a*bytes + b*counter:")
for k, nm in enumerate(names):
    xs = [d[2][k] for d in data]
    a, bb = solve2(bs, xs, ys)
    pred = [a*x1 + bb*x2 for x1, x2 in zip(bs, xs)]
    order = sorted(zip(pred, [d[0] for d in data]), reverse=True); r570 = [i for _, i in order].index(570) + 1
    p570 = next(pr for pr, i in zip(pred, [d[0] for d in data]) if i == 570)
    print(f"  bytes + {nm:10s} r = {corr(pred, ys):.3f}   a = {a*2**30/1e6:6.0f} B/byte  leaf 570: predicted {p570:6.1f} GiB, rank {r570:3d}")

print("\nbytes + nat_arith model: top 12 predicted leaves, and the measured heavy tail")
xs = [d[2][4] for d in data]; a, bb = solve2(bs, xs, ys)
pred = {d[0]: a*d[1] + bb*d[2][4] for d in data}
print(f"  fit: {a*2**30:.0f} record bytes per serialized byte + {bb*2**30:.0f} record bytes per nat_arith op")
for i in sorted(pred, key=lambda i: -pred[i])[:12]:
    print(f"  leaf {i:3d}  predicted {pred[i]:6.1f} GiB  measured {rec[i]:6.1f} GiB  nat_arith {next(d[2][4] for d in data if d[0]==i):.2e}")
print("  measured over 64 GiB:")
for i in sorted(rec, key=lambda i: -rec[i])[:8]:
    print(f"  leaf {i:3d}  measured {rec[i]:6.1f} GiB  predicted {pred[i]:6.1f} GiB  rank {sorted(pred, key=lambda j: -pred[j]).index(i)+1}")
med = st.median(pred.values()); print(f"  predicted median {med:.1f} GiB, p90 {sorted(pred.values())[int(0.9*len(pred))]:.1f} GiB; measured median {st.median(rec.values()):.1f}, p90 {sorted(rec.values())[int(0.9*len(rec))]:.1f} GiB")
