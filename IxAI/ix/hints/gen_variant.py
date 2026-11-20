#!/usr/bin/env python3
"""Write a hint-edit file (address<TAB>hint) for a named variant of the default hints.

  gen_variant.py HINTS.tsv VARIANT OUT.tsv

Variants:
  flat          every regular height -> 0 (equal ranks: lazy delta unfolds both sides)
  invert        regular h -> 64 - h (unfold the lower definition first)
  abbrev2reg    abbrev -> regular(0)
  noise:SEED    regular h -> h + U{-3..3}, clamped at 0
  abbrev:P:SEED each regular definition becomes abbrev with probability P
  opaque:P:SEED each regular definition becomes opaque with probability P
  swap:P:SEED   each regular definition becomes regular(64 - h) with probability P
"""
import random
import sys

hints_path, variant, out_path = sys.argv[1:4]
parts = variant.split(":")
kind = parts[0]
rng = random.Random(int(parts[-1]) if len(parts) > 1 else 0)
p = float(parts[1]) if len(parts) == 3 else 1.0
changed = 0
with open(out_path, "w") as out:
    for line in open(hints_path):
        addr, hint = line.rstrip("\n").split("\t")
        regular = hint not in ("opaque", "abbrev")
        new = None
        if kind == "flat" and regular:
            new = "0"
        elif kind == "invert" and regular:
            new = str(max(0, 64 - int(hint)))
        elif kind == "abbrev2reg" and hint == "abbrev":
            new = "0"
        elif kind == "noise" and regular:
            new = str(max(0, int(hint) + rng.randint(-3, 3)))
        elif kind in ("abbrev", "opaque", "swap") and regular and rng.random() < p:
            new = {"abbrev": "abbrev", "opaque": "opaque",
                   "swap": str(max(0, 64 - int(hint)))}[kind]
        if new is not None and new != hint:
            out.write(f"{addr}\t{new}\n")
            changed += 1
print(f"{variant}: {changed} hints changed")
