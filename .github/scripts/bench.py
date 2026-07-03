#!/usr/bin/env python3
"""All data-wrangling for the `!benchmark` PR workflow, as subcommands:

  parse       COMMENT_BODY env → matrix + config (writes $GITHUB_OUTPUT)
  manifest    Benchmarks/Vectors.csv → the constant names for one cell
  bmf         neutral results JSON → Bencher Metric Format (bench-main.yml)
  fetch-main  base SHA + cell → main.json pulled from bencher.dev
  compare     main.json + pr.json → a Markdown main-vs-PR table
  comment     per-cell table files → the final PR comment body

The neutral results JSON every backend normalises to (see run.sh) is
`{ "<name>": { "<metric>": <number>, ... }, ... }`. Most metrics are
lower-is-better (a positive Δ% is a regression); the exceptions live in
HIGHER_IS_BETTER (throughput), where the polarity is flipped.
"""
import argparse
import glob
import json
import os
import time
import urllib.parse
import urllib.request


# ─────────────────── backend identity table ────────────────────
# Single source of truth for what each backend is:
#   default_mode — what `!benchmark <backend>` runs. The bare `execute` token
#     switches to the "execute" metrics entry when one exists (only aiur has
#     a real choice: `prove` is the full pipeline; `execute` skips Phase 2 via
#     `--execute-only`).
#   testbed — the bencher testbed bench-main.yml uploads main's numbers to.
#     MUST match that workflow's `testbed:` strings; fetch-main fails a cell
#     loudly (exit 2) when a (backend, mode) has no entry here, so drift shows
#     up as a red cell instead of a silent local-rebuild fallback.
#   metrics — compare-table columns per supported mode. aiur's execute entry
#     reads the SAME testbed as prove (bencher stores only prove runs; the
#     execute-side columns — incl. execute-peak-rss, sampled at the Phase 1/2
#     boundary — are extracted from that JSON, apples-to-apples).
# `compile` benchmarks `ix compile <env>.lean → <env>.ixe`; its benchmark name
# on bencher is the CamelCase env slug (ENV_CC below).
BACKEND_TABLE = {
    "aiur": {
        "default_mode": "prove",
        "testbed": "aiur-check-x64-32x",
        "metrics": {
            "prove":   ["fft-cost", "execute-time", "prove-time", "verify-time",
                        "proof-size", "peak-rss"],
            "execute": ["fft-cost", "execute-time", "execute-peak-rss"],
        },
    },
    "zisk": {
        "default_mode": "execute",
        "testbed": "zisk-check-x64-32x",
        "metrics": {
            "execute": ["cycles", "execute-time", "throughput", "execute-peak-rss"],
        },
    },
    "sp1": {
        "default_mode": "execute",
        "testbed": "sp1-check-x64-32x",
        "metrics": {
            "execute": ["cycles", "execute-time", "throughput", "execute-peak-rss"],
        },
    },
    "ooc": {
        "default_mode": "execute",
        "testbed": "ooc-check-x64-32x",
        "metrics": {
            "execute": ["throughput", "check-time", "peak-rss"],
        },
    },
    "compile": {
        "default_mode": "compile",
        "testbed": "ix-compile-x64-32x",
        "metrics": {
            "compile": ["compile-time", "throughput", "file-size", "constants"],
        },
    },
}
BACKENDS = tuple(BACKEND_TABLE)
ENVS = ("initStd", "lean", "mathlib")
# CamelCase benchmark key per env — must match bench-main.yml's matrix.bench
# values (the names bencher stores env-keyed rows under: ooc whole-env,
# compile). One explicit table, not a first-letter-upper derivation, so an
# env whose CamelCase isn't mechanical (e.g. a future `flt` → `FLT`) can't
# silently diverge from the workflow.
ENV_CC = {"initStd": "InitStd", "lean": "Lean", "mathlib": "Mathlib"}
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
        # The bare `execute` token selects a backend's execute entry when it
        # has one — a real switch only for aiur (everything else already
        # defaults to execute, or has no execute mode at all: compile).
        if execute_flag and "execute" in BACKEND_TABLE[b]["metrics"]:
            return "execute"
        return BACKEND_TABLE[b]["default_mode"]

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
        with open(a.out, "w") as f:
            f.write(ENV_CC[a.env] + "\n")
        print(f"count=1\ntier=n/a")
        return
    # prove defaults to the cheap tier to keep the full set bounded; the curated
    # primary subset is exempt — run.sh's aiur prove path attempts prove for
    # every primary (RAM watchdog catches OOMs), so all primaries are selected
    # here regardless of tier.
    tier = a.tier or ("cheap" if (a.mode == "prove" and not a.primary) else "all")
    names, heavy = [], []
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
            if ctier == "heavy":
                heavy.append(name)
    with open(a.out, "w") as f:
        f.write("\n".join(names) + ("\n" if names else ""))
    # The selected names that are heavy-tier — the subset the zisk cells run
    # through the closure-sharded pipeline (ix extract → profile → shard)
    # instead of a single full-closure leaf.
    if a.heavy_out:
        with open(a.heavy_out, "w") as f:
            f.write("\n".join(heavy) + ("\n" if heavy else ""))
    print(f"count={len(names)}\ntier={tier}")


# ───────────────────────── compare ─────────────────────────
def _num(d, name, metric):
    v = d.get(name, {}).get(metric)
    return v if isinstance(v, (int, float)) else None


# Per-metric formatting kind. Metric names are the neutral-JSON keys the tools
# emit (see BACKEND_TABLE). Unknown metrics fall through to `_human_auto`.
_METRIC_KIND = {
    # bytes
    "peak-rss": "bytes",
    "execute-peak-rss": "bytes",
    "file-size": "bytes",
    "proof-size": "bytes",
    # seconds
    "execute-time": "seconds",
    "prove-time": "seconds",
    "verify-time": "seconds",
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


# Metrics where a LARGER value is the improvement. Everything else is
# lower-is-better (times, RAM, cycles, fft-cost, sizes).
HIGHER_IS_BETTER = {"throughput"}


def _delta(main, pr):
    if main is None or pr is None or main == 0:
        return None
    return (pr - main) / main * 100.0


def _badness(dp, metric):
    """Signed regression magnitude: positive ⇒ the PR got worse on `metric`.
    For lower-is-better metrics that's a positive Δ%; for higher-is-better
    (throughput) it's a negative Δ%."""
    if dp is None:
        return None
    return -dp if metric in HIGHER_IS_BETTER else dp


# Ratio direction words per metric kind (grew, shrank). Rates and times read
# as faster/slower; sizes as larger/smaller; counts (cycles, fft-cost, …) as
# more/fewer — "1.15× slower" is meaningless for a byte or count metric.
_RATIO_WORDS = {
    "seconds": ("slower", "faster"),
    "bytes":   ("larger", "smaller"),
    "count":   ("more", "fewer"),
    "int":     ("more", "fewer"),
}


def _ratio(main, pr, metric):
    """(factor, direction word) with `factor` always ≥ 1.0. Wording follows
    the metric's kind and polarity: throughput (a rate) and the time metrics
    read as faster/slower, sizes as larger/smaller, counts as more/fewer.
    Returns None if either side is missing or non-positive."""
    if main is None or pr is None or main <= 0 or pr <= 0:
        return None
    grew = pr >= main
    factor = pr / main if grew else main / pr
    if metric in HIGHER_IS_BETTER:      # rate: more per second = faster
        return (factor, "faster" if grew else "slower")
    kind = _METRIC_KIND.get(metric, "auto")
    words = _RATIO_WORDS.get(kind, ("larger", "smaller"))
    return (factor, words[0] if grew else words[1])


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
    metrics = a.metric or BACKEND_TABLE.get(a.backend, {}).get("metrics", {}).get(a.mode)
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
    # One side empty while the other measured is almost always a broken side
    # (e.g. the base-run fallback hit a CLI-incompatible base), not a real
    # all-regressed/all-new comparison — say so instead of a silent n/a column.
    side_note = ""
    if not main_d:
        side_note = ("\n\n_⚠️ main produced no results — the base-side run "
                     "failed entirely (often a CLI-incompatible base binary "
                     "when bencher had no data). Deltas unavailable; see the "
                     "workflow logs._")
    elif not pr_d:
        side_note = ("\n\n_⚠️ the PR side produced no results — every "
                     "constant failed or was dropped. See the workflow logs._")

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

    def _failed(d, n):
        return isinstance(d.get(n), dict) and d[n].get("failed") is True

    regressed, improved = set(), set()
    failures = []  # (name, side) — typecheck failures, surfaced loudly below
    worst = None  # (badness, dp, name, metric)
    for n in names:
        cells = [f"`{n}`"]
        main_oom, pr_oom = _oom(main_d, n), _oom(pr_d, n)
        main_failed, pr_failed = _failed(main_d, n), _failed(pr_d, n)
        if main_failed:
            failures.append((n, "main"))
        if pr_failed:
            failures.append((n, "PR"))
        for m in metrics:
            mv, pv = _num(main_d, n, m), _num(pr_d, n, m)
            # An OOM entry may still carry real Phase-1 measurements (run.sh
            # merges the sentinel into whatever was recorded before the kill);
            # render those, and OOM only for the metrics the kill prevented.
            # A typecheck FAILURE outranks everything — the constant is
            # rejected, not benchmarked. Spell it out in the cell: a bare ❌
            # would read as any generic failure.
            mv_h = ("❌ failed typecheck" if main_failed
                    else "OOM" if (main_oom and mv is None) else _human(mv, m))
            pv_h = ("❌ failed typecheck" if pr_failed
                    else "OOM" if (pr_oom and pv is None) else _human(pv, m))
            dp = _delta(mv, pv)
            bad = _badness(dp, m)
            cell = "n/a" if dp is None else f"{dp:+.1f}%"
            if dp is not None:
                # Ratio only when the change is big enough that "1.18× slower"
                # carries new signal beyond the percentage — sub-5% deltas would
                # just add `(1.03× slower)` noise to the cell.
                r = _ratio(mv, pv, m)
                if r is not None and r[0] >= 1.05:
                    cell += f" ({r[0]:.2f}× {r[1]})"
                if bad > a.threshold:
                    cell += " ⚠️"; regressed.add(n)
                elif bad < -a.threshold:
                    cell += " 🟢"; improved.add(n)
                if worst is None or bad > worst[0]:
                    worst = (bad, dp, n, m)
            cells += [mv_h, pv_h, cell]
        rows.append("| " + " | ".join(cells) + " |")

    out = ([title, ""] if title else []) + rows + [""]
    # Typecheck failures first and loud — a constant the kernel REJECTS is a
    # correctness signal, not a benchmark blip.
    for n, side in failures:
        out.append(f"❌ **`{n}` FAILED TO TYPECHECK on the {side} side** — "
                   "the kernel rejected it; see the workflow logs.")
    if failures:
        out.append("")
    s = (f"_{len(names)} constants · {len(regressed)} regressed · "
         f"{len(improved)} improved (|Δ| > {a.threshold:g}% on any metric)._")
    if worst and worst[0] is not None and worst[0] > a.threshold:
        s += f" Worst: `{worst[2]}` `{worst[3]}` {worst[1]:+.1f}%."
    out.append(s)
    if side_note:
        out.append(side_note.strip())
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


# ──────────────────────── bmf ─────────────────────────
def cmd_bmf(a):
    """Neutral results JSON → Bencher Metric Format.

    One converter for every bench-main.yml upload site (previously four
    hand-copied jq pipelines): flattens each entry's `phases` object into
    `phase:<span>` measures, strips the boolean `oom` sentinel (BMF values
    must be numeric — one boolean would fail the whole `bencher run` upload;
    the sentinel is for the PR comparison table only), and drops entries left
    with no measures.
    """
    with open(a.infile) as f:
        neutral = json.load(f)
    out = {}
    for name, entry in (neutral or {}).items():
        if not isinstance(entry, dict):
            continue
        measures = {}
        for k, v in entry.items():
            if k in ("oom", "failed"):
                continue
            # Nested objects are per-sub-measure breakdowns: `phases` (span →
            # seconds) flattens to `phase:<span>`; anything else (e.g. the
            # zisk env row's `shard-cycles`) to `<key>:<sub>`. Both stay
            # un-thresholded on bencher (dynamic names).
            if isinstance(v, dict):
                prefix = "phase" if k == "phases" else k
                for sub, sv in v.items():
                    if isinstance(sv, (int, float)) and not isinstance(sv, bool):
                        measures[f"{prefix}:{sub}"] = {"value": sv}
            elif isinstance(v, (int, float)) and not isinstance(v, bool):
                measures[k] = {"value": v}
        if measures:
            out[name] = measures
    with open(a.out, "w") as f:
        json.dump(out, f, indent=1)
    print(f"bmf: {len(out)} benchmark(s) → {a.out}")


# ─────────────────────── fetch-main ──────────────────────
def cmd_fetch_main(a):
    """Pull the base SHA's neutral results JSON from bencher.dev.

    The testbed comes from BACKEND_TABLE — supported (backend, mode) pairs are
    exactly the table's metrics keys. Exit codes are load-bearing for
    bench-pr.yml: 3 = transient (bencher has no report at that hash yet, or
    the API failed after retries) — the caller falls back to running main
    locally; 2 = permanent config error ((backend, mode) not in BACKEND_TABLE,
    i.e. table / bench-main.yml drift) — the caller fails the cell loudly
    instead of paying the fallback forever.

    A PARTIAL miss (bencher answered, but some --names entries have no data —
    e.g. constants the PR adds to Vectors.csv) still exits 0: main.json holds
    what bencher had, and --missing-out lists the uncovered names so the
    caller can measure just those against the base checkout and merge.
    """
    entry = BACKEND_TABLE.get(a.backend)
    testbed = entry["testbed"] if entry and a.mode in entry["metrics"] else None
    if not testbed:
        print(f"fetch-main: no main testbed for {a.backend}/{a.mode}")
        raise SystemExit(2)
    wanted = set(open(a.names).read().split()) if a.names else None
    # ooc's headline row is keyed by the CamelCase env slug (not a Vectors.csv
    # constant), so names.txt alone would filter it out — admit it explicitly.
    if wanted is not None and a.env:
        wanted.add(ENV_CC.get(a.env, a.env))
    # TODO: support any base/PR branch, not just `main`. Today bench-main.yml
    # only runs on push to main and this query hardcodes `branch=main`, so a PR
    # against a non-main base branch (e.g. a long-running feature branch) always
    # falls through to the local base-run path. To generalise: (1) let
    # bench-main.yml (or a sibling) upload reports for other tracked branches,
    # (2) plumb `--branch` here from `github.base_ref` in bench-pr.yml, (3) fall
    # back to `main` when the base branch has no bencher data.
    # Bencher stores the git hash at `branch.head.version.hash`.
    def _report_hash(r):
        return (((r.get("branch") or {}).get("head") or {}).get("version") or {}).get("hash")

    def _get_json(url, attempts=3):
        for i in range(attempts):
            try:
                with urllib.request.urlopen(url, timeout=15) as f:
                    return json.load(f)
            except Exception as e:
                if i == attempts - 1:
                    raise
                print(f"fetch-main: attempt {i + 1} failed ({e}); retrying")
                time.sleep(2 ** i)

    # Page newest-first until the base SHA's reports are found (a matrix env
    # uploads one report each, all within one push's CI window, so once we've
    # matched and a later page yields nothing new we're past it). A transient
    # API error is retried before the expensive local-base fallback fires.
    per_page = 255
    at_sha, page = [], 1
    while page <= 8:  # 2040 newest reports — far beyond a realistic backlog
        params = {"branch": "main", "testbed": testbed,
                  "per_page": per_page, "page": page}
        url = ("https://api.bencher.dev/v0/projects/ix/reports?"
               + urllib.parse.urlencode(params))
        try:
            reports = _get_json(url)
        except Exception as e:
            print(f"fetch-main: bencher API error: {e}")
            raise SystemExit(3)
        matches = [r for r in reports if _report_hash(r) == a.sha]
        if at_sha and not matches:
            break            # past the SHA's window
        at_sha += matches
        if len(reports) < per_page:
            break            # end of data
        page += 1
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
    # Names the PR side selected (its Vectors.csv) that bencher has no data
    # for at this SHA — typically constants the PR itself adds to the CSV.
    # The caller runs the base checkout on JUST these and merges, so a new
    # constant still gets a real main-vs-PR delta on its first !benchmark.
    # Computed against names.txt verbatim (not the ENV_CC-augmented `wanted`):
    # the env-keyed row is an admit-filter, not a per-constant expectation.
    if a.missing_out:
        name_set = set(open(a.names).read().split()) if a.names else set()
        missing = sorted(name_set - set(out))
        with open(a.missing_out, "w") as f:
            f.write("\n".join(missing) + ("\n" if missing else ""))
        if missing:
            print(f"fetch-main: {len(missing)} name(s) not on bencher @ "
                  f"{a.sha[:8]} (base run will measure): " + ", ".join(missing))
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
    m.add_argument("--heavy-out", dest="heavy_out",
                   help="Also write the selected heavy-tier names (one per "
                        "line) — the subset zisk runs closure-sharded.")
    m.set_defaults(fn=cmd_manifest)

    b = sub.add_parser("bmf")
    b.add_argument("--in", dest="infile", required=True,
                   help="Neutral results JSON (run.sh output).")
    b.add_argument("--out", required=True,
                   help="Bencher Metric Format JSON for `bencher run`.")
    b.set_defaults(fn=cmd_bmf)

    fm = sub.add_parser("fetch-main")
    fm.add_argument("--sha", required=True)
    fm.add_argument("--backend", required=True)
    fm.add_argument("--mode", required=True)
    fm.add_argument("--env", default="",
                    help="Cell env; admits the env-keyed row (ooc whole-env) "
                         "past the --names filter.")
    fm.add_argument("--names", help="Only fetch benchmarks whose names appear in this file.")
    fm.add_argument("--missing-out", dest="missing_out",
                    help="Write the --names entries bencher had no data for "
                         "(one per line; empty file when none) — the subset "
                         "the caller should measure against the base checkout.")
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
