"""Read the load-bearing Zisk cost-model constants straight from the planner
(`crates/kernel/src/shard.rs`).

We deliberately do NOT define the model here. `shard.rs` is the single source of
truth; this just parses its calibrated `pub const`s so the validation plots
overlay the *actual* code model against measured data (no Python-fit function).
"""
import os
import re

# The planner is vendored in this repo; resolve it relative to this file
# (Benchmarks/Statistics/benchstats/ -> repo root). Fall back to a sibling
# `~/ix` checkout for anyone running outside a full worktree.
_HERE = os.path.dirname(os.path.abspath(__file__))
_IN_REPO = os.path.normpath(os.path.join(_HERE, "..", "..", "..", "crates", "kernel", "src", "shard.rs"))
_SIBLING = os.path.expanduser("~/ix/crates/kernel/src/shard.rs")
DEFAULT_SHARD_RS = _IN_REPO if os.path.exists(_IN_REPO) else _SIBLING

NAMES = [
    "STEPS_PER_HEARTBEAT", "STEPS_PER_SUBST", "STEPS_PER_INGRESS_BYTE",
    "SHARD_STEP_FLOOR", "RAM_BASE_GIB", "RAM_GIB_PER_BCYCLE",
    "PROVE_SETUP_SECS", "PROVE_SECS_PER_BCYCLE",
]


def read_constants(path=None):
    """Parse the planner constants from shard.rs. Returns {NAME: float}."""
    path = path or DEFAULT_SHARD_RS
    if not os.path.exists(path):
        raise SystemExit(f"shard.rs not found at {path}; pass --shard-rs <path>")
    txt = open(path).read()
    out = {}
    for n in NAMES:
        m = re.search(rf"pub const {n}\s*:\s*\w+\s*=\s*([0-9_.]+)", txt)
        if not m:
            raise SystemExit(f"constant {n} not found in {path}")
        out[n] = float(m.group(1).replace("_", ""))
    return out
