"""Renumber a .ixes manifest so leaves dispatch heaviest-first by predicted record size.

Predicted size: the non-negative fit over the profile, record = 1205*bytes + 570*frontier + 502*subst + 2487*nat_arith.
The aggregation tree keeps its shape; its leaf references are relabeled. Measured peaks, if present, are permuted.
"""
import struct, sys, csv
import numpy as np
PROF, SRC, DST, MAP = sys.argv[1:5]
b = open(PROF, "rb").read(); n = struct.unpack_from("<I", b, 12)[0]; p = 16; prof = {}
for _ in range(n):
    a = b[p:p + 32].hex(); prof[a] = struct.unpack_from("<QIIQQQQQ", b, p + 32); p += 88

m = open(SRC, "rb").read(); q = 0
magic = m[q:q + 8]; q += 8; total_cross = m[q:q + 16]; q += 16
nl = struct.unpack_from("<I", m, q)[0]; q += 4
entries = []  # (payload bytes after the id, blocks)
for i in range(nl):
    s = q; sid = struct.unpack_from("<I", m, q)[0]; assert sid == i; q += 4
    hb, own, cross = struct.unpack_from("<QQQ", m, q); q += 24; tag = m[q]; q += 1 + (32 if tag == 1 else 0)
    blen = struct.unpack_from("<I", m, q)[0]; q += 4; blocks = [m[q + 32 * k:q + 32 * k + 32].hex() for k in range(blen)]; q += 32 * blen
    flen = struct.unpack_from("<I", m, q)[0]; q += 4 + 32 * flen
    entries.append((m[s + 4:q], blocks, cross))
tree = None; peaks = None
if q < len(m):
    tag = m[q]; q += 1
    if tag == 1:
        def rd():
            global q
            t = m[q]; q += 1
            if t == 0:
                v = struct.unpack_from("<I", m, q)[0]; q += 4; return ("leaf", v)
            return ("node", rd(), rd())
        tree = rd()
    if q < len(m):
        tag = m[q]; q += 1
        if tag == 1:
            peaks = list(struct.unpack_from("<%dQ" % nl, m, q)); q += 8 * nl
assert q == len(m), (q, len(m))

def feats(blocks, cross):
    P = [prof[a] for a in blocks if a in prof]
    return sum(x[1] for x in P), cross, sum(x[3] for x in P), sum(x[6] for x in P)
coef = np.array([1204.9, 569.6, 502.4, 2486.5]) / 2**30
pred = [float(np.array(feats(bl, cross)) @ coef) for _, bl, cross in entries]
order = sorted(range(nl), key=lambda i: -pred[i])  # new index -> old index
new_of = {old: new for new, old in enumerate(order)}

out = bytearray(); out += magic + total_cross + struct.pack("<I", nl)
for new, old in enumerate(order):
    out += struct.pack("<I", new) + entries[old][0]
if tree is not None:
    out += b"\x01"
    def wr(t):
        if t[0] == "leaf": out.extend(b"\x00" + struct.pack("<I", new_of[t[1]]))
        else: out.extend(b"\x01"); wr(t[1]); wr(t[2])
    wr(tree)
else:
    out += b"\x00"
if peaks is not None:
    out += b"\x01" + struct.pack("<%dQ" % nl, *[peaks[old] for old in order])
open(DST, "wb").write(out)
with open(MAP, "w", newline="") as f:
    w = csv.writer(f); w.writerow(["new_index", "old_index", "predicted_gib"])
    for new, old in enumerate(order): w.writerow([new, old, round(pred[old], 2)])
print(f"wrote {DST}: {nl} leaves, tree {'kept' if tree else 'balanced'}, peaks {'permuted' if peaks else 'none'}, {len(out)} bytes")
print("first 8 (new idx: old idx, predicted GiB):", [(new, old, round(pred[old], 1)) for new, old in enumerate(order[:8])])
