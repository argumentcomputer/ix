#!/usr/bin/env python3
"""All data-wrangling for the `!benchmark` PR workflow, as subcommands:

  parse     COMMENT_BODY env → matrix + config (writes $GITHUB_OUTPUT)
  manifest  Benchmarks/Vectors.csv → the constant names for one cell
  compare   main.json + pr.json   → a Markdown main-vs-PR table
  comment   per-cell table files  → the final PR comment body

The neutral results JSON every backend normalises to (see run.sh) is
`{ "<name>": { "<metric>": <number>, ... }, ... }`. All metrics are
lower-is-better, so a positive Δ% is a regression.
"""
import argparse
import glob
import hashlib
import json
import os


# ───────────────────────── parse ─────────────────────────
BACKENDS = ("aiur", "zisk", "sp1", "native")
MODES = ("execute", "prove")
ENVS = ("initStd", "lean", "mathlib")
CONFIG_KEYS = {"BENCH_ENVS", "BENCH_TIER", "BENCH_SHARD", "BENCH_GPU", "BENCH_FULL"}
PASSTHROUGH_KEYS = {"RUST_LOG", "WITHOUT_VK_VERIFICATION", "RUSTFLAGS"}


def runner_for(backend, mode, gpu):
    """(runs-on label, skip?) for a cell."""
    if backend == "aiur":
        return "warp-ubuntu-latest-x64-32x", False
    if backend == "native":   # whole-env parallel check; no proving, never skips
        return "warp-ubuntu-latest-x64-32x", False
    if mode == "execute":
        return "warp-ubuntu-latest-x64-16x", False
    if gpu:                       # zkVM prove needs a GPU
        return "self-hosted-gpu", False
    return "ubuntu-latest", True


def cmd_parse(_a):
    body = os.environ.get("COMMENT_BODY", "")
    lines = [ln.replace("\r", "") for ln in body.splitlines()]
    cmd = next((ln for ln in lines if "!benchmark" in ln), "")
    toks = cmd.split("!benchmark", 1)[1].split() if "!benchmark" in cmd else []

    backends, mode = [], "execute"
    for t in (t.lower() for t in toks):
        if t == "all":
            backends = list(BACKENDS)
        elif t in BACKENDS and t not in backends:
            backends.append(t)
        elif t in MODES:
            mode = t
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
    gpu = cfg.get("BENCH_GPU") == "1"

    cells = []
    for b in backends:
        for e in envs:
            runner, skip = runner_for(b, mode, gpu)
            cells.append({"backend": b, "env": e, "mode": mode, "runner": runner,
                          "skip": "true" if skip else "false", "label": f"{b}-{e}-{mode}"})

    summary = (f"backends: `{' '.join(backends)}` · mode: `{mode}` · "
               f"envs: `{','.join(envs)}` · set: `{'full' if full == '1' else 'primary'}` · "
               f"tier: `{tier or 'auto'}` · shard: `{shard}` · gpu: `{int(gpu)}`")
    if passthrough:
        summary += " · env: `" + " ".join(passthrough) + "`"

    with open(os.environ.get("GITHUB_OUTPUT", "/dev/stdout"), "a") as f:
        f.write(f"matrix={json.dumps(cells)}\n")
        f.write(f"mode={mode}\ntier={tier}\nshard={shard}\nfull={full}\n")
        f.write(f"config-summary={summary}\n")
        f.write("passthrough-env<<PTENV\n" + "\n".join(passthrough)
                + ("\n" if passthrough else "") + "PTENV\n")
    print(summary)
    print(json.dumps(cells, indent=2))


# ──────────────────────── manifest ────────────────────────
def cmd_manifest(a):
    # prove defaults to the cheap tier to keep the full set bounded; the curated
    # primary subset is exempt — run.sh proves each primary that fits the Aiur RAM
    # ceiling and execute-only's the rest, so all primaries are selected here.
    tier = a.tier or ("cheap" if (a.mode == "prove" and not a.primary) else "all")
    names = []
    with open(a.csv) as f:
        for line in f:
            row = line.rstrip("\n")
            if not row or row.startswith("#"):
                continue
            cols = row.split(",")
            if cols[0] == "name" or len(cols) < 4:
                continue
            name, env, ctier, shard = cols[:4]
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
    vhash = hashlib.sha256(open(a.csv, "rb").read()).hexdigest()[:16]
    print(f"count={len(names)}\nvhash={vhash}\ntier={tier}")


# ───────────────────────── compare ─────────────────────────
METRICS = {
    ("aiur", "execute"): ["fft-cost", "execute-time"],
    ("aiur", "prove"): ["prove-time", "peak-rss"],
    ("zisk", "execute"): ["cycles", "execute-time", "throughput", "peak-rss"],
    ("sp1", "execute"): ["cycles", "execute-time", "throughput", "peak-rss"],
    ("zisk", "prove"): ["prove-time", "steps", "peak-rss"],
    ("sp1", "prove"): ["prove-time", "peak-rss"],
    # native is whole-env (one row per env); mode is ignored (it never proves).
    ("native", "execute"): ["throughput", "check-time", "peak-rss"],
    ("native", "prove"): ["throughput", "check-time", "peak-rss"],
}


def _num(d, name, metric):
    v = d.get(name, {}).get(metric)
    return v if isinstance(v, (int, float)) else None


def _human(v):
    if v is None:
        return "n/a"
    if isinstance(v, int) or (isinstance(v, float) and v.is_integer()):
        return f"{int(v):,}"
    return f"{v:,.3f}"


def _delta(main, pr):
    if main is None or pr is None or main == 0:
        return None
    return (pr - main) / main * 100.0


def _load(path):
    try:
        with open(path) as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def _phases(entry):
    """The `phases` object (span → seconds) on a constant's entry, or {}."""
    p = entry.get("phases") if isinstance(entry, dict) else None
    return p if isinstance(p, dict) else {}


def _phase_details(main_d, pr_d, names):
    """Collapsible per-constant phase (span) timing tables — the drill-down that
    shows *where* time moved between main and PR. Emitted only for constants that
    carry tracing-texray span data."""
    blocks = []
    for n in names:
        mp, pp = _phases(main_d.get(n, {})), _phases(pr_d.get(n, {}))
        # Only worth a drill-down when there's more than one phase; a lone phase
        # (zisk/sp1 execute, native check) just restates the headline metric.
        if len(set(mp) | set(pp)) < 2:
            continue
        rows = ["| phase | main (s) | PR (s) | Δ% |", "|---|--:|--:|--:|"]
        # Slowest-on-PR (else main) first, so the dominant phase leads.
        spans = sorted(set(mp) | set(pp),
                       key=lambda s: -(pp.get(s) if isinstance(pp.get(s), (int, float))
                                       else mp.get(s) if isinstance(mp.get(s), (int, float)) else 0))
        for s in spans:
            mv, pv = mp.get(s), pp.get(s)
            mv = mv if isinstance(mv, (int, float)) else None
            pv = pv if isinstance(pv, (int, float)) else None
            dp = _delta(mv, pv)
            rows.append(f"| `{s}` | {_human(mv)} | {_human(pv)} | "
                        f"{'n/a' if dp is None else f'{dp:+.1f}%'} |")
        blocks.append(f"<details><summary><code>{n}</code> — phase breakdown</summary>\n\n"
                      + "\n".join(rows) + "\n\n</details>")
    return blocks


def cmd_compare(a):
    metrics = a.metric or METRICS.get((a.backend, a.mode))
    if not metrics:
        raise SystemExit("compare: pass --metric or a known --backend/--mode")
    title = a.title
    if title is None and a.backend:
        hit = "hit (cached)" if a.cache_hit == "true" else "miss (ran main)"
        cnt = f"{a.count} constants · " if a.count else ""
        title = f"### `{a.backend}` · `{a.env}` · `{a.mode}` — {cnt}main cache: {hit}"

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

    n_reg = n_imp = 0
    worst = None
    for n in names:
        cells = [f"`{n}`"]
        for i, m in enumerate(metrics):
            mv, pv = _num(main_d, n, m), _num(pr_d, n, m)
            dp = _delta(mv, pv)
            cell = "n/a" if dp is None else f"{dp:+.1f}%"
            if i == 0 and dp is not None:
                if dp > a.threshold:
                    cell += " ⚠️"; n_reg += 1
                elif dp < -a.threshold:
                    cell += " 🟢"; n_imp += 1
                if worst is None or dp > worst[0]:
                    worst = (dp, n)
            cells += [_human(mv), _human(pv), cell]
        rows.append("| " + " | ".join(cells) + " |")

    out = ([title, ""] if title else []) + rows + [""]
    s = (f"_{len(names)} constants · {n_reg} regressed · {n_imp} improved "
         f"(|Δ| > {a.threshold:g}% on `{primary}`)._")
    if worst and worst[0] is not None and worst[0] > a.threshold:
        s += f" Worst: `{worst[1]}` {worst[0]:+.1f}%."
    out.append(s)
    details = _phase_details(main_d, pr_d, names)
    if details:
        out += ["", "<details><summary>Per-phase timing drill-down</summary>", ""]
        out += details
        out += ["", "</details>"]
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


# ────────────────────────── cli ──────────────────────────
def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("parse").set_defaults(fn=cmd_parse)

    m = sub.add_parser("manifest")
    m.add_argument("--csv", required=True); m.add_argument("--env", required=True)
    m.add_argument("--mode", required=True); m.add_argument("--tier", default="")
    m.add_argument("--shard", default="0"); m.add_argument("--out", required=True)
    m.add_argument("--primary", action="store_true",
                   help="Restrict to the primary subset (the primary=1 column).")
    m.set_defaults(fn=cmd_manifest)

    c = sub.add_parser("compare")
    c.add_argument("--main", required=True); c.add_argument("--pr", required=True)
    c.add_argument("--metric", action="append", default=[])
    c.add_argument("--threshold", type=float, default=3.0)
    c.add_argument("--title"); c.add_argument("--backend"); c.add_argument("--env")
    c.add_argument("--mode"); c.add_argument("--count"); c.add_argument("--cache-hit", default="")
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
