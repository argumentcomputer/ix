#!/usr/bin/env python3
"""Parse the `!benchmark` PR-comment command into the benchmark job matrix:

  parse    COMMENT_BODY env → matrix + config (writes $GITHUB_OUTPUT)

Everything downstream of the parse (constant selection, the measured runs,
BMF conversion, the bencher fetch, compare tables, the PR comment body)
lives in the `ix bench` CLI (Ix/Cli/BenchCmd.lean, Ix/Cli/BenchReport.lean).
This script remains only because the setup job must parse the comment before
any `ix` binary has been built or restored.

Backends and envs come from Benchmarks/bench-config.json (the registry).
Backend command tokens are the registry's backend entries; a disabled one
(sp1) is recognised but skipped, with a note in the config summary.
"""
import json
import os
import sys

CONFIG_PATH = "Benchmarks/bench-config.json"
CONFIG_KEYS = {"BENCH_ENVS", "BENCH_SHARD", "BENCH_FULL"}
PASSTHROUGH_KEYS = {"RUST_LOG", "WITHOUT_VK_VERIFICATION", "RUSTFLAGS"}


def cmd_parse():
    with open(CONFIG_PATH) as f:
        cfg = json.load(f)
    table = {b: e for b, e in cfg["backends"].items() if "testbed" in e}
    env_table = cfg["envs"]
    runner = cfg["runner"]

    body = os.environ.get("COMMENT_BODY", "")
    lines = [ln.replace("\r", "") for ln in body.splitlines()]
    cmd = next((ln for ln in lines if "!benchmark" in ln), "")
    toks = cmd.split("!benchmark", 1)[1].split() if "!benchmark" in cmd else []

    backends, skipped, execute_flag = [], [], False
    for t in (t.lower() for t in toks):
        if t == "all":
            for b in table:
                if table[b].get("enabled"):
                    if b not in backends:
                        backends.append(b)
                elif b not in skipped:
                    skipped.append(b)
        elif t in table and t not in backends:
            if table[t].get("enabled"):
                backends.append(t)
            elif t not in skipped:
                skipped.append(t)
        elif t == "execute":
            execute_flag = True
    if not backends:
        backends = ["aiur"]

    cfg_kv, passthrough = {}, []
    for ln in lines[(lines.index(cmd) + 1) if cmd in lines else 0:]:
        s = ln.strip()
        if not s or "=" not in s:
            continue
        key, val = (x.strip() for x in s.split("=", 1))
        if key in CONFIG_KEYS:
            cfg_kv[key] = val
        elif key in PASSTHROUGH_KEYS:
            passthrough.append(f"{key}={val}")

    # Env tokens match the registry keys case-insensitively (users type
    # BENCH_ENVS=initstd as often as InitStd); the canonical key wins.
    by_lower = {e.lower(): e for e in env_table}
    envs = [by_lower[e.strip().lower()]
            for e in cfg_kv.get("BENCH_ENVS", "InitStd").split(",")
            if e.strip().lower() in by_lower]
    envs = list(dict.fromkeys(envs)) or ["InitStd"]
    shard = "1" if cfg_kv.get("BENCH_SHARD") == "1" else "0"
    full = "1" if cfg_kv.get("BENCH_FULL") == "1" else "0"  # full set vs primary subset

    def mode_for(b):
        # Cells run the backend's default mode (aiur: prove — the cell that
        # simulates the real workload, measuring Phase 1 inside it). The
        # bare `execute` token flips a backend with an execute metrics
        # entry to execute-only — a real switch only for aiur, whose two
        # modes bench-main runs as separate cells on separate testbeds, so
        # either kind of PR cell finds a cached bencher baseline.
        if execute_flag and "execute" in table[b].get("metrics", {}):
            return "execute"
        return table[b]["default_mode"]

    # `env` (e.g. InitStd) is the single identifier: the `<env>.ixe`
    # filename, the cache-key suffix, and the env-keyed bencher benchmark
    # name.
    cells = []
    for b in backends:
        m = mode_for(b)
        for e in envs:
            cells.append({"backend": b, "env": e, "mode": m,
                          "runner": runner, "label": f"{b}-{e}-{m}"})

    modes = " ".join(f"{b}={mode_for(b)}" for b in backends)
    summary = (f"backends: `{modes}` · envs: `{','.join(envs)}` · "
               f"set: `{'full' if full == '1' else 'primary'}` · "
               f"shard: `{shard}`")
    for b in skipped:
        reason = table[b].get("disabled_reason", "disabled in bench-config.json")
        summary += f" · skipped `{b}` ({reason})"
    if passthrough:
        summary += " · env: `" + " ".join(passthrough) + "`"

    with open(os.environ.get("GITHUB_OUTPUT", "/dev/stdout"), "a") as f:
        f.write(f"matrix={json.dumps(cells)}\n")
        f.write(f"shard={shard}\nfull={full}\n")
        f.write(f"config-summary={summary}\n")
        f.write("passthrough-env<<PTENV\n" + "\n".join(passthrough)
                + ("\n" if passthrough else "") + "PTENV\n")
    print(summary)
    print(json.dumps(cells, indent=2))


if __name__ == "__main__":
    if sys.argv[1:] != ["parse"]:
        raise SystemExit("usage: bench.py parse  (everything else moved to `ix bench`)")
    cmd_parse()
