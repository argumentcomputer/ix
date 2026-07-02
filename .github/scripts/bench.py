#!/usr/bin/env python3
"""All data-wrangling for the `!benchmark` PR workflow, as subcommands:

  parse       COMMENT_BODY env → matrix + config (writes $GITHUB_OUTPUT)
  manifest    Benchmarks/Vectors.csv → the constant names for one cell
  fetch-main  base SHA + cell → main.json pulled from bencher.dev
  compare     main.json + pr.json → a Markdown main-vs-PR table
  comment     per-cell table files → the final PR comment body

The neutral results JSON every backend normalises to (see run.sh) is
`{ "<name>": { "<metric>": <number>, ... }, ... }`. All metrics are
lower-is-better, so a positive Δ% is a regression.
"""
import argparse
import glob
import json
import os
import urllib.parse
import urllib.request


# ───────────────────────── parse ─────────────────────────
# Default mode per backend. Aiur is the only backend with a real choice:
# `prove` (default) is the full pipeline; `execute` skips Phase 2
# (`--execute-only`) and reports the `fft-cost` / `execute-time` subset —
# users opt in via the bare `execute` token in `!benchmark`. The zkVMs and
# `ooc` always run execute; `compile` runs `ix compile`.
DEFAULT_MODE = {
    "aiur":    "prove",
    "zisk":    "execute",
    "sp1":     "execute",
    "ooc":     "execute",
    # `compile` benchmarks `ix compile <env>.lean → <env>.ixe` — the same job
    # `bench-main.yml`'s `compile` matrix uploads under testbed `ix-compile-*`.
    # Mode is `compile` (there's no execute/prove split); the "benchmark name"
    # in bencher is the CamelCase env slug (`InitStd`, `Lean`, `Mathlib`, `FLT`).
    "compile": "compile",
}
BACKENDS = tuple(DEFAULT_MODE)
ENVS = ("initStd", "lean", "mathlib")
CONFIG_KEYS = {"BENCH_ENVS", "BENCH_TIER", "BENCH_SHARD", "BENCH_FULL"}
PASSTHROUGH_KEYS = {"RUST_LOG", "WITHOUT_VK_VERIFICATION", "RUSTFLAGS"}


RUNNER = "warp-ubuntu-latest-x64-32x"


def cmd_parse(_a):
    body = os.environ.get("COMMENT_BODY", "")
    lines = [ln.replace("\r", "") for ln in body.splitlines()]
    cmd = next((ln for ln in lines if "!benchmark" in ln), "")
    toks = cmd.split("!benchmark", 1)[1].split() if "!benchmark" in cmd else []

    backends, execute_flag = [], False
    for t in (t.lower() for t in toks):
        if t == "all":
            backends = list(BACKENDS)
        elif t in BACKENDS and t not in backends:
            backends.append(t)
        elif t == "execute":
            execute_flag = True
    if not backends:
        backends = ["aiur"]

    cfg, passthrough = {}, []
    for ln in lines[(lines.index(cmd) + 1) if cmd in lines else 0:]:
        s = ln.strip()
        if not s or "=" not in s:
            continue
        key, val = (x.strip() for x in s.split("=", 1))
        if key in CONFIG_KEYS:
            cfg[key] = val
        elif key in PASSTHROUGH_KEYS:
            passthrough.append(f"{key}={val}")

    envs = [e.strip() for e in cfg.get("BENCH_ENVS", "initStd").split(",") if e.strip()]
    envs = [e for e in envs if e in ENVS] or ["initStd"]
    tier = cfg.get("BENCH_TIER", "")
    if tier not in ("cheap", "heavy", "all"):
        tier = ""             # empty ⇒ derived from mode at manifest time
    shard = "1" if cfg.get("BENCH_SHARD") == "1" else "0"
    full = "1" if cfg.get("BENCH_FULL") == "1" else "0"  # full set vs primary subset

    def mode_for(b):
        # `execute` only affects aiur (the zkVMs and ooc are execute-only anyway).
        return "execute" if (b == "aiur" and execute_flag) else DEFAULT_MODE[b]

    cells = []
    for b in backends:
        m = mode_for(b)
        for e in envs:
            cells.append({"backend": b, "env": e, "mode": m,
                          "runner": RUNNER,
                          "label": f"{b}-{e}-{m}"})

    modes = " ".join(f"{b}={mode_for(b)}" for b in backends)
    summary = (f"backends: `{modes}` · envs: `{','.join(envs)}` · "
               f"set: `{'full' if full == '1' else 'primary'}` · "
               f"tier: `{tier or 'auto'}` · shard: `{shard}`")
    if passthrough:
        summary += " · env: `" + " ".join(passthrough) + "`"

    with open(os.environ.get("GITHUB_OUTPUT", "/dev/stdout"), "a") as f:
        f.write(f"matrix={json.dumps(cells)}\n")
        f.write(f"tier={tier}\nshard={shard}\nfull={full}\n")
        f.write(f"config-summary={summary}\n")
        f.write("passthrough-env<<PTENV\n" + "\n".join(passthrough)
                + ("\n" if passthrough else "") + "PTENV\n")
    print(summary)
    print(json.dumps(cells, indent=2))


# ──────────────────────── manifest ────────────────────────
def cmd_manifest(a):
    # `compile` doesn't consume Vectors.csv — the "benchmark name" on bencher
    # is the CamelCase env slug (`initStd` → `InitStd`), one per cell.
    if a.backend == "compile":
        name = a.env[:1].upper() + a.env[1:]
        with open(a.out, "w") as f:
            f.write(name + "\n")
        print(f"count=1\ntier=n/a")
        return
    # prove defaults to the cheap tier to keep the full set bounded; the curated
    # primary subset is exempt — run.sh's aiur prove path attempts prove for
    # every primary (RAM watchdog catches OOMs), so all primaries are selected
    # here regardless of tier.
    tier = a.tier or ("cheap" if (a.mode == "prove" and not a.primary) else "all")
    names = []
    with open(a.csv) as f:
        for line in f:
            row = line.rstrip("\n")
            if not row or row.startswith("#"):
                continue
            cols = row.split(",")
            if cols[0] == "name" or len(cols) < 3:
                continue
            # `shard_target` and `primary` default to "0" when the column is
            # omitted, so rows can drop trailing zero fields (most only carry
            # the first three).
            name, env, ctier = cols[:3]
            shard = cols[3] if len(cols) >= 4 else "0"
            rep = cols[4] if len(cols) >= 5 else "0"
            if env != a.env:
                continue
            if a.primary and rep != "1":
                continue
            if tier in ("cheap", "heavy") and ctier != tier:
                continue
            if a.shard == "1" and shard != "1":
                continue
            names.append(name)
    with open(a.out, "w") as f:
        f.write("\n".join(names) + ("\n" if names else ""))
    print(f"count={len(names)}\ntier={tier}")


# ───────────────────────── compare ─────────────────────────
# Compare-column set per (backend, mode). Aiur has both modes: `prove` shows
# the full execute+prove metric set; `execute` is a subset (Phase 1 only, no
# prove-time / no throughput). Bencher stores only the prove set for main —
# `execute` mode filters that same JSON down to the execute-side columns.
METRICS = {
    ("aiur",    "prove"):    ["fft-cost", "execute-time", "prove-time", "peak-rss"],
    ("aiur",    "execute"):  ["fft-cost", "execute-time", "peak-rss"],
    ("zisk",    "execute"):  ["cycles", "execute-time", "throughput", "peak-rss"],
    ("sp1",     "execute"):  ["cycles", "execute-time", "throughput", "peak-rss"],
    ("ooc",     "execute"):  ["throughput", "check-time", "peak-rss"],
    ("compile", "compile"):  ["compile-time", "throughput", "file-size", "constants"],
}


def _num(d, name, metric):
    v = d.get(name, {}).get(metric)
    return v if isinstance(v, (int, float)) else None


# Per-metric formatting kind. Metric names are the neutral-JSON keys the tools
# emit (see METRICS above). Unknown metrics fall through to `_human_auto`.
_METRIC_KIND = {
    # bytes
    "peak-rss": "bytes",
    "file-size": "bytes",
    # seconds
    "execute-time": "seconds",
    "prove-time": "seconds",
    "check-time": "seconds",
    "compile-time": "seconds",
    # large counts (10^6+ typical)
    "fft-cost": "count",
    "cycles": "count",
    "steps": "count",
    "max-shard-cycles": "count",
    "throughput": "count",
    # small integers
    "constants": "int",
    "shards": "int",
}


def _human_bytes(v):
    v = float(v)
    for unit in ("B", "KiB", "MiB", "GiB", "TiB"):
        if abs(v) < 1024:
            return f"{int(v):,} {unit}" if unit == "B" else f"{v:,.2f} {unit}"
        v /= 1024
    return f"{v:,.2f} PiB"


def _human_seconds(v):
    v = float(v)
    if abs(v) < 1e-3:
        return f"{v * 1e6:.1f} µs"
    if abs(v) < 1:
        return f"{v * 1e3:.1f} ms"
    if abs(v) < 60:
        return f"{v:.3f} s"
    m, s = divmod(v, 60)
    return f"{int(m)}m {s:.1f}s"


def _human_count(v):
    v = float(v)
    if abs(v) < 1000:
        return f"{int(v):,}" if v == int(v) else f"{v:.3f}"
    for unit in ("K", "M", "B", "T"):
        v /= 1000
        if abs(v) < 1000:
            return f"{v:.2f}{unit}"
    return f"{v:.2f}Q"


def _human_auto(v):
    if isinstance(v, int) or (isinstance(v, float) and v.is_integer()):
        return f"{int(v):,}"
    return f"{v:,.3f}"


def _human(v, metric=None):
    if v is None:
        return "n/a"
    kind = _METRIC_KIND.get(metric, "auto")
    if kind == "bytes":   return _human_bytes(v)
    if kind == "seconds": return _human_seconds(v)
    if kind == "count":   return _human_count(v)
    if kind == "int":     return f"{int(v):,}"
    return _human_auto(v)


def _delta(main, pr):
    if main is None or pr is None or main == 0:
        return None
    return (pr - main) / main * 100.0


def _ratio(main, pr):
    """(factor, direction) with `factor` always ≥ 1.0. Metrics are lower-
    is-better, so `pr > main` reads as slower / larger; `pr < main` as
    faster / smaller. Returns None if either side is missing or non-positive."""
    if main is None or pr is None or main <= 0 or pr <= 0:
        return None
    return (pr / main, "slower") if pr >= main else (main / pr, "faster")


def _load(path):
    try:
        with open(path) as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


# TODO: re-add the per-constant Aiur phase (sub-span) drill-down. run.sh's
# `merge_phases` still folds tracing-texray JSON-Lines into `phases: { span:
# seconds }` on each entry; the compare renderer previously emitted a
# collapsible `<details>` block per constant showing main-vs-PR per-span deltas
# so a regression could be traced to `aiur/execute`, `aiur/witness`,
# `stark/fri_open`, etc. Removed while the compare surface is being stabilised;
# reinstate once we've settled on the primary table's flag/threshold semantics.


def cmd_compare(a):
    metrics = a.metric or METRICS.get((a.backend, a.mode))
    if not metrics:
        raise SystemExit("compare: pass --metric or a known --backend/--mode")
    title = a.title
    if title is None and a.backend:
        src = a.main_source or "unknown"
        cnt = f"{a.count} constants · " if a.count else ""
        title = f"### `{a.backend}` · `{a.env}` · `{a.mode}` — {cnt}main from: {src}"

    def emit(text):
        if a.out:
            open(a.out, "w").write(text + "\n")
        else:
            print(text)

    main_d, pr_d = _load(a.main), _load(a.pr)
    names = sorted(set(main_d) | set(pr_d))
    if not names:
        emit((title or "") + "\n\n_No results were produced (every constant failed, "
             "timed out, or was dropped). See the workflow logs._")
        return

    primary = metrics[0]
    names.sort(key=lambda n: (0, -v) if (v := (_num(pr_d, n, primary)
               if _num(pr_d, n, primary) is not None else _num(main_d, n, primary))) is not None
               else (1, 0))

    head = ["constant"]
    for m in metrics:
        head += [f"{m} (main)", f"{m} (PR)", "Δ%"]
    rows = ["| " + " | ".join(head) + " |", "|" + "|".join(["---"] * len(head)) + "|"]

    def _oom(d, n):
        return isinstance(d.get(n), dict) and d[n].get("oom") is True

    regressed, improved = set(), set()
    worst = None  # (dp, name, metric)
    for n in names:
        cells = [f"`{n}`"]
        main_oom, pr_oom = _oom(main_d, n), _oom(pr_d, n)
        for m in metrics:
            mv, pv = _num(main_d, n, m), _num(pr_d, n, m)
            mv_h = "OOM" if main_oom else _human(mv, m)
            pv_h = "OOM" if pr_oom else _human(pv, m)
            if main_oom or pr_oom:
                cells += [mv_h, pv_h, "n/a"]
                continue
            dp = _delta(mv, pv)
            cell = "n/a" if dp is None else f"{dp:+.1f}%"
            if dp is not None:
                # Ratio only when the change is big enough that "1.18× slower"
                # carries new signal beyond the percentage — sub-5% deltas would
                # just add `(1.03× slower)` noise to the cell.
                r = _ratio(mv, pv)
                if r is not None and r[0] >= 1.05:
                    cell += f" ({r[0]:.2f}× {r[1]})"
                if dp > a.threshold:
                    cell += " ⚠️"; regressed.add(n)
                elif dp < -a.threshold:
                    cell += " 🟢"; improved.add(n)
                if worst is None or dp > worst[0]:
                    worst = (dp, n, m)
            cells += [mv_h, pv_h, cell]
        rows.append("| " + " | ".join(cells) + " |")

    out = ([title, ""] if title else []) + rows + [""]
    s = (f"_{len(names)} constants · {len(regressed)} regressed · "
         f"{len(improved)} improved (|Δ| > {a.threshold:g}% on any metric)._")
    if worst and worst[0] is not None and worst[0] > a.threshold:
        s += f" Worst: `{worst[1]}` `{worst[2]}` {worst[0]:+.1f}%."
    out.append(s)
    # TODO: emit per-constant phase drill-down (see the TODO by _phase_details).
    emit("\n".join(out))


# ───────────────────────── comment ─────────────────────────
def cmd_comment(a):
    commit = f"[`{a.head[:7]}`]({a.repo_url}/commit/{a.head})"
    parts = [f"## `!benchmark` — main vs {commit}", "", a.summary, ""]
    tables = sorted(glob.glob(os.path.join(a.tables, "table-*.md")))
    if tables:
        for t in tables:
            parts += [open(t).read().rstrip(), ""]
    else:
        parts += ["_No result tables were produced — see the workflow logs._", ""]
    parts.append(f"[Workflow logs]({a.repo_url}/actions/runs/{a.run_id})")
    open(a.out, "w").write("\n".join(parts) + "\n")
    print(open(a.out).read())


# ─────────────────────── fetch-main ──────────────────────
# Testbeds bench-main.yml uploads to, keyed by (backend, mode). Only the
# pairs main actually runs land here — anything else (e.g. `aiur execute`,
# `zisk prove`) has no bencher data; fetch-main exits non-zero for those and
# bench-pr.yml falls back to running main locally.
MAIN_TESTBEDS = {
    # `aiur execute` uses the same testbed as `aiur prove` — bencher stores
    # only prove and the execute columns are extracted from that JSON.
    ("aiur",    "prove"):    "aiur-check-x64-32x",
    ("aiur",    "execute"):  "aiur-check-x64-32x",
    ("zisk",    "execute"):  "zisk-check-x64-32x",
    ("sp1",     "execute"):  "sp1-check-x64-32x",
    ("ooc",     "execute"):  "ooc-check-x64-32x",
    ("compile", "compile"):  "ix-compile-x64-32x",
}


def cmd_fetch_main(a):
    """Pull the base SHA's neutral results JSON from bencher.dev.

    Exits 2 if (backend, mode) isn't a combination main runs. Exits 3 if
    bencher has no report at that hash yet (freshly-pushed main whose CI is
    still ingesting) or the request failed. Callers fall back to running
    main locally on any non-zero exit.
    """
    testbed = MAIN_TESTBEDS.get((a.backend, a.mode))
    if not testbed:
        print(f"fetch-main: no main testbed for {a.backend}/{a.mode}")
        raise SystemExit(2)
    wanted = set(open(a.names).read().split()) if a.names else None
    # TODO: support any base/PR branch, not just `main`. Today bench-main.yml
    # only runs on push to main and this query hardcodes `branch=main`, so a PR
    # against a non-main base branch (e.g. a long-running feature branch) always
    # falls through to the local base-run path. To generalise: (1) let
    # bench-main.yml (or a sibling) upload reports for other tracked branches,
    # (2) plumb `--branch` here from `github.base_ref` in bench-pr.yml, (3) fall
    # back to `main` when the base branch has no bencher data.
    params = {"branch": "main", "testbed": testbed, "per_page": 255}
    url = "https://api.bencher.dev/v0/projects/ix/reports?" + urllib.parse.urlencode(params)
    try:
        with urllib.request.urlopen(url, timeout=15) as f:
            reports = json.load(f)
    except Exception as e:
        print(f"fetch-main: bencher API error: {e}")
        raise SystemExit(3)
    # Bencher stores the git hash at `branch.head.version.hash`.
    at_sha = [
        r for r in reports
        if (((r.get("branch") or {}).get("head") or {}).get("version") or {}).get("hash") == a.sha
    ]
    if not at_sha:
        print(f"fetch-main: no reports for {a.backend}/{a.mode} @ {a.sha[:8]}")
        raise SystemExit(3)
    # Matrix envs upload separately to the same testbed at the same commit,
    # each contributing its own benchmark subset — aggregate across reports.
    # Filter/emit by `name` (Bencher's `slug` is a lower-kebab-cased derivation
    # that would mangle Lean names like `Nat.add_comm` → `nat-add-comm`).
    out = {}
    for r in at_sha:
        for iteration in r.get("results", []):
            for bench in iteration:
                name = bench["benchmark"]["name"]
                if wanted is not None and name not in wanted:
                    continue
                metrics = {
                    m["measure"]["name"]: m["metric"]["value"]
                    for m in bench.get("measures", [])
                }
                if metrics:
                    out[name] = metrics
    if not out:
        print(f"fetch-main: reports found but no matching benchmarks in --names")
        raise SystemExit(3)
    with open(a.out, "w") as f:
        json.dump(out, f)
    print(f"fetch-main: {len(out)} constant(s) from bencher for {a.backend}/{a.mode}")


# ────────────────────────── cli ──────────────────────────
def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("parse").set_defaults(fn=cmd_parse)

    m = sub.add_parser("manifest")
    m.add_argument("--csv", required=True); m.add_argument("--env", required=True)
    m.add_argument("--mode", required=True); m.add_argument("--tier", default="")
    m.add_argument("--shard", default="0"); m.add_argument("--out", required=True)
    m.add_argument("--backend", default="",
                   help="Backend for this cell (used to special-case `compile`, "
                        "which doesn't consume Vectors.csv).")
    m.add_argument("--primary", action="store_true",
                   help="Restrict to the primary subset (the primary=1 column).")
    m.set_defaults(fn=cmd_manifest)

    fm = sub.add_parser("fetch-main")
    fm.add_argument("--sha", required=True)
    fm.add_argument("--backend", required=True)
    fm.add_argument("--mode", required=True)
    fm.add_argument("--names", help="Only fetch benchmarks whose names appear in this file.")
    fm.add_argument("--out", required=True)
    fm.set_defaults(fn=cmd_fetch_main)

    c = sub.add_parser("compare")
    c.add_argument("--main", required=True); c.add_argument("--pr", required=True)
    c.add_argument("--metric", action="append", default=[])
    c.add_argument("--threshold", type=float, default=3.0)
    c.add_argument("--title"); c.add_argument("--backend"); c.add_argument("--env")
    c.add_argument("--mode"); c.add_argument("--count"); c.add_argument("--main-source", default="")
    c.add_argument("--out")
    c.set_defaults(fn=cmd_compare)

    cm = sub.add_parser("comment")
    cm.add_argument("--tables", required=True); cm.add_argument("--summary", default="")
    cm.add_argument("--head", required=True); cm.add_argument("--repo-url", required=True)
    cm.add_argument("--run-id", required=True); cm.add_argument("--out", required=True)
    cm.set_defaults(fn=cmd_comment)

    a = ap.parse_args()
    a.fn(a)


if __name__ == "__main__":
    main()
