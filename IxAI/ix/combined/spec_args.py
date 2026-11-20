#!/usr/bin/env python3
"""The full configuration's training run, recomputed from the specification by the untrusted
Python reimplementation (`shell/triage.py`), in the layout `combine_check` and `aiur_exec_check`
read: `ARGS` holds `m0 (331) || lr || xs (600 * 160) || ts (600 * 220)` and `OUTPUT` the trained
model (331), as signed integers. A model is `w1 (16 x 8) || b1 (16) || w2 (11 x 16) || b2 (11)`.

Usage: spec_args.py ARGS OUTPUT
"""

import os
import sys

# Importing `triage` from `shell/` must not leave a bytecode cache in that source directory.
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "shell"))
import triage  # noqa: E402


def flat(m):
    w1, b1, w2, b2 = m
    return [v for row in w1 for v in row] + list(b1) + [v for row in w2 for v in row] + list(b2)


def main():
    args_path, output_path = sys.argv[1], sys.argv[2]
    c = triage.CONFIGS["full"]
    r = triage.Rng(c["seed"])
    data = [triage.gen(3, r) for _ in range(c["train"])]
    examples = [([v * 256 for v in triage.features(f)], triage.targets(f)) for f in data]
    m = triage.init(c, 8, 11)
    m0 = flat(m)
    xs, ts = [], []
    for idx in triage.schedule(c):
        batch = [examples[i] for i in idx]
        xs += [v for x, _ in batch for v in x]
        ts += [v for _, t in batch for v in t]
        m = triage.step(c["lr"], m, batch)
    with open(args_path, "w") as f:
        f.write(" ".join(map(str, m0 + [c["lr"]] + xs + ts)) + "\n")
    with open(output_path, "w") as f:
        f.write(" ".join(map(str, flat(m))) + "\n")


if __name__ == "__main__":
    main()
