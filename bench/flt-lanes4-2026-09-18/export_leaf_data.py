"""Per-leaf features (profile, manifest, delta graph) and measured targets (lanes logs, metrics) as CSV,
plus per-claim round-one rows by circuit. Usage: export_leaf_data.py <out_dir>"""
import re, struct, json, csv, sys, collections
import numpy as np
D = "/home/sam/benchdata/flt"; RUN = f"{D}/runs/flt572-lanes4-exec3"
PROF, IXES = f"{D}/anthropic-flt.ixprof", f"{D}/anthropic-flt-572.ixes"
out = sys.argv[1]
b = open(PROF, "rb").read(); n = struct.unpack_from("<I", b, 12)[0]; p = 16; prof = {}; order = []
for _ in range(n):
    a = b[p:p + 32].hex(); prof[a] = struct.unpack_from("<QIIQQQQQ", b, p + 32); order.append(a); p += 88
ne = struct.unpack_from("<Q", b, p)[0]; p += 8
row = np.frombuffer(b, dtype="<u8", count=n + 1, offset=p); p += 8 * (n + 1); col = np.frombuffer(b, dtype="<u4", count=ne, offset=p)
sizes = np.array([prof[a][1] for a in order], float); idx = {a: i for i, a in enumerate(order)}
m = open(IXES, "rb").read(); q = 8 + 16; nl = struct.unpack_from("<I", m, q)[0]; q += 4; leaves = []
for i in range(nl):
    q += 4; hb, own, cross = struct.unpack_from("<QQQ", m, q); q += 24; tag = m[q]; q += 1 + (32 if tag == 1 else 0)
    blen = struct.unpack_from("<I", m, q)[0]; q += 4; bl = [m[q + 32 * k:q + 32 * k + 32].hex() for k in range(blen)]; q += 32 * blen
    flen = struct.unpack_from("<I", m, q)[0]; q += 4 + 32 * flen; leaves.append((bl, own, cross))
rec, ex, ts = {}, {}, {}; plan = None
for path in (f"{RUN}/lanes.err", f"{RUN}/lanes-resume256.err"):
    for line in open(path, errors="replace"):
        mm = re.match(r"\[trace-shards\] (\d+) shards?, ", line)
        if mm: plan = int(mm.group(1)); continue
        mm = re.search(r"claim (\d+) executed in ([\d.]+)s, record (\d+) B", line)
        if mm and int(mm.group(1)) < 572:
            k = int(mm.group(1)); rec[k] = int(mm.group(3)); ex[k] = float(mm.group(2))
            if plan: ts[k] = plan; plan = None
proof = {}; circ = collections.defaultdict(float)
for path in (f"{RUN}/metrics.jsonl", f"{RUN}/metrics-resume256.jsonl"):
    for line in open(path):
        if '"summary"' not in line: continue
        d = json.loads(line); mm = re.match(r"Claim\((\d+)\)", str(d["identity"].get("work", "")))
        if not mm: continue
        k = int(mm.group(1))
        if k >= 572: continue
        if d["boundary"] == "aiur/prove_planned": proof[k] = d["wall_elapsed_ns"] / 1e9
        elif d["boundary"] == "aiur/witness" and d["identity"].get("round") == 1:
            for mt in d["metrics"]:
                if mt["name"] == "trace" and mt["counters"]["rows"] > 0:
                    L = mt["labels"]; circ[(k, L["kind"], L["circuit"], L["width"])] += mt["counters"]["rows"]
with open(f"{out}/leaves.csv", "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["leaf", "blocks", "consts", "bytes", "own_size", "frontier_bytes", "heartbeats", "subst", "whnf", "def_eq", "nat_arith", "intern",
                "unfolded_bytes", "foreign_unfolded_bytes", "delta_edges", "foreign_delta_edges", "record_bytes", "execution_s", "proof_s", "trace_shards"])
    for i, (bl, own, cross) in enumerate(leaves):
        P = [prof[a] for a in bl if a in prof]; mem = set(idx[a] for a in bl if a in idx); unf = funf = 0.0; edges = fedges = 0
        for a in bl:
            c = idx.get(a)
            if c is None: continue
            prods = col[row[c]:row[c + 1]]; edges += len(prods); unf += sizes[prods].sum()
            fp = [pp for pp in prods if pp not in mem]; fedges += len(fp); funf += sizes[fp].sum()
        w.writerow([i, len(bl), sum(x[2] for x in P), sum(x[1] for x in P), own, cross, sum(x[0] for x in P), sum(x[3] for x in P), sum(x[4] for x in P),
                    sum(x[5] for x in P), sum(x[6] for x in P), sum(x[7] for x in P), int(unf), int(funf), edges, fedges,
                    rec.get(i, ""), ex.get(i, ""), round(proof.get(i, 0), 3) or "", ts.get(i, "")])
with open(f"{out}/circuit_rows_round1.csv", "w", newline="") as f:
    w = csv.writer(f); w.writerow(["leaf", "kind", "circuit", "width", "rows"])
    for (k, kind, c, wd), r in sorted(circ.items()): w.writerow([k, kind, c, wd, int(r)])
print("leaves:", nl, "with records:", len(rec), "proofs:", len(proof), "circuit rows:", len(circ))
