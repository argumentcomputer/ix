#!/usr/bin/env python3
"""Per-unit execution and proof times from a lanes stderr log."""
import re, sys
from collections import OrderedDict
log = open(sys.argv[1]).read().splitlines()
ex = re.compile(r"\[lanes\] executor \d+: (claim \d+|join \d+|root) executed in ([\d.]+)s, record (\d+) B")
ps = re.compile(r"\[lanes\] worker \d+: (claim \d+|join \d+|root) proving started at \+(\d+)s")
pe = re.compile(r"\[lanes\] worker \d+: (claim \d+|join \d+|root) (?:proven|published) at \+(\d+)s")
units = OrderedDict()
for l in log:
    m = ex.search(l)
    if m: units.setdefault(m[1], {})['exec'] = float(m[2]); units[m[1]]['gib'] = int(m[3]) / 2**30
    m = ps.search(l)
    if m: units.setdefault(m[1], {})['start'] = int(m[2])
    m = pe.search(l)
    if m: units.setdefault(m[1], {})['end'] = int(m[2])
rows = []
for name, u in units.items():
    if 'end' in u: rows.append((name, u.get('exec'), u.get('gib'), u['end'] - u['start'], u['end']))
print(f"{'unit':10} {'exec s':>7} {'rec GiB':>8} {'proof s':>8} {'proven at':>10}")
for r in rows: print(f"{r[0]:10} {r[1]:7.1f} {r[2]:8.1f} {r[3]:8d} {r[4]:10d}")
for kind in ('claim', 'join'):
    k = [r for r in rows if r[0].startswith(kind)]
    if k: print(f"{kind}s proven={len(k)} exec mean={sum(r[1] for r in k)/len(k):.1f}s proof mean={sum(r[3] for r in k)/len(k):.1f}s proof total={sum(r[3] for r in k)}s last at +{k[-1][4]}s")
