# Benchmarking

One orchestrator — `ix bench` — runs every benchmark cell, locally and in CI.
A **cell** is `(backend, env, mode)`, e.g. `zisk-InitStd-execute`. CI is a
thin wrapper: the same `ix bench run` you type in a terminal is what both
workflows execute, so every CI number is reproducible on your machine.

- **`!benchmark` PR comment** (`.github/workflows/bench-pr.yml`) — on demand,
  posts a **main-vs-PR** comparison table on the pull request. main's numbers
  come from bencher.dev (`ix bench fetch-main`); the PR side is measured
  fresh. When bencher can't supply the base SHA (not ingested yet, or the PR
  adds new constants), the workflow measures the gap on a base checkout.
- **Bencher.dev** (`.github/workflows/bench-main.yml`) — on every push to
  `main`, tracks each measure over time at <https://bencher.dev> (project
  `ix`), the canonical store the PR path reads from.

## The row contract

Every measured tool reports through one shape — the **benchmark results JSON** —
and one exit-code convention (Rust: `crates/bench`; Lean:
`Ix/Benchmark/Results.lean`):

```json
{ "<name>": { "status": "ok", "<metric>": 123, "phase:<span>": 1.5 } }
```

- Rows are flushed after every name, so a killed run keeps its completed rows.
- `status` is `ok` or `rejected` (written by the tool) or `oom` (merged in by
  `ix bench run` after an abnormal exit — a process never observes its own
  OOM kill). An `oom` row keeps whatever metrics landed before the kill.
- Exit codes: `0` all ok · `2` usage error · `3` the kernel **rejected** a
  constant (its row is on disk) · anything else is an infrastructure failure.

There is no output scraping anywhere: no marker lines, no log grepping, no
sentinel-key jq. State flows through rows and exit codes only. A rejected or
OOM'd constant never reaches bencher (`ix bench bmf` drops non-`ok` rows),
and a run that produces zero rows exits nonzero — an empty cell can't be
green.

## `ix bench` subcommands

| subcommand | job |
|---|---|
| `run`        | run one cell: select names, ensure the `.ixe`, spawn the tool under the RAM watchdog (one process per constant on aiur/zkVM), fold each spawn's span window into its row, gate on the rows |
| `shard`      | pre-cut the closure-shard artifacts for the env's heavy-tier constants (`ix shard extract` → `ix profile` → `ix shard`) |
| `compare`    | two rows files → Markdown main-vs-PR table (thresholds, ratios, OOM/❌ rows) |
| `bmf`        | rows → Bencher Metric Format (non-`ok` rows dropped) |
| `fetch-main` | pull a base SHA's rows from bencher.dev (exit 3 = fall back to a local base run) |
| `comment`    | assemble per-cell tables into the PR comment body |
| `matrix`     | emit the workflows' job matrices from `bench-config.json` |

### Local usage

```shell
# Run the ooc cell over InitStd's primary constants:
ix bench run --backend ooc --env InitStd

# Change something, run again, and diff against your previous run
# (runs are saved as baselines under .bench/<cell>{,.prev}.json):
ix bench run --backend ooc --env InitStd --reuse-ixe
ix bench compare --backend ooc --env InitStd
```

`--repo <dir>` points the run at another checkout: the *measured* tools
resolve from `<dir>/.lake/build/bin` first, so one `ix` can drive a base and
a PR tree and compare them — exactly what the PR workflow does.

## Backends

| backend | what it measures | tool |
|---|---|---|
| `aiur`    | Aiur STARK check, one bench-main cell per mode on its own testbed: prove — the real-workload simulation (prove-time, proof-size, verify-time, peak-rss, plus fft-cost / execute-time from its own Phase 1) — and execute, the fast Phase-1-only signal (fft-cost, execute-time, throughput, peak-rss). `!benchmark aiur [execute]` picks the mode | `bench-typecheck` |
| `zisk`    | ZisK VM execute: cycles, execute-time, throughput, peak-rss | `zisk-host` |
| `sp1`     | SP1 VM execute (currently disabled in `bench-config.json`) | `sp1-host` |
| `ooc`     | out-of-circuit Rust kernel: whole-env row + one full-closure row per primary (`check-time` wraps only the check — the env loads once, outside every row's timed window) | `ix check-rs --json` |
| `compile` | `ix compile <env>.lean → <env>.ixe`: compile-time, file-size, constants, throughput | `ix compile --json` |

All tools take the same `--consts`/`--consts-file` grammar and emit the same
rows. The ooc and zkVM cells share per-constant **full-closure** scope, so
their delta isolates in-circuit vs out-of-circuit overhead.

With `--texray`, tools write per-phase span timings (`aiur/prove_ixvm`,
`aiur/witness`, `stark/*`, `zisk/execute`, …) to `<json>.spans`. The
per-constant backends run **one process per constant**, so each spawn's
window belongs wholly to its constant: `ix bench run` folds it into the
row as flat `phase:<span>` fields, which flow to bencher as independent
measures (witness gen, stage commits, quotient, … each get a trend line)
and render in the PR comment as a collapsible per-constant drill-down.

## RAM: watchdog, OOM rows, sharding

`ix bench run` wraps each tool in `.github/scripts/watchdog.sh <ceiling-gb>
<cmd>`: a sidecar that samples the process tree's RSS and, on breach, sends
SIGTERM (tools flush their in-flight row and clean up), then SIGKILL after a
10s grace. A killed per-constant process gets its row marked `status: oom`
(keeping whatever was flushed) and the loop continues — one constant's
death costs one constant. There are **no per-constant timeouts**;
the job-level `timeout-minutes` is the only clock.

Heavy-tier zisk constants (whose single-leaf closure would blow the runner's
RAM) run as their closure-shard partition instead: `ix shard extract` →
`ix profile` → `ix shard` cut a manifest, and one `--shard-plan` host run
executes the shards sequentially, emitting the constant's row with per-shard
breakdowns. bench-main's compile job pre-cuts these artifacts
(`ix bench shard`) and ships them via cache.

## Registry and constant set

- **`Benchmarks/Vectors.csv`** — the curated constants: one row per
  `(name, env, tier[, shard_target[, primary]])`. `tier: heavy` marks
  constants whose full prove is expected to OOM (they still run; the row
  records it). `primary: 1` is the default `!benchmark` subset.
- **`Benchmarks/bench-config.json`** — everything else: env slugs and compile
  modules, backends (enabled flag, default mode, bencher testbed, compare
  columns), the runner, the watchdog ceiling. The workflows' matrices are
  generated from it (`ix bench matrix`), the `!benchmark` parser reads it,
  and `bencher-thresholds-reset.yml` derives its workload lists from it —
  add or disable a backend in one place.

## `!benchmark` grammar

```
!benchmark ([aiur] [zisk] [ooc] [compile] | all) [execute]
BENCH_ENVS=InitStd,Mathlib     # default InitStd (case-insensitive)
BENCH_FULL=1                   # full curated set, not just primary
BENCH_SHARD=1                  # only the multi-shard target constants
RUST_LOG=info                  # allowlisted passthrough env
```

Parsed by `.github/scripts/bench.py` (the one Python remnant — it must run
before any Lean build exists). Mode defaults per backend from
`bench-config.json`; the bare `execute` token flips `aiur` to Phase-1 only.

## CI shape

**bench-main.yml**: `build` (compile `ix` + `bench-typecheck` once, cache by
SHA) → `plan` (`ix bench matrix` → job matrices) + `compile` (per env:
`ix bench run --backend compile`, cache the `.ixe` + pre-cut zisk shards) →
`aiur` (execute + prove cells) / `zkvm-execute` / `ooc-check` (each: restore caches, one
`ix bench run … --reuse-ixe`, `ix bench bmf`, upload via
`.github/actions/bencher-track`). A kernel rejection exits 3 and reddens the
run step while the clean rows still upload.

**bench-pr.yml**: `setup` (parse the comment) → `build` (PR binaries, cached
by head SHA) → `benchmark` matrix (per cell: PR-side `ix bench run`;
`ix bench fetch-main` for main's numbers, with a targeted base-checkout run
covering only what bencher lacked; `ix bench compare` → table artifact) →
`comment` (`ix bench comment` → one PR comment).

## Not yet covered

- **zkVM prove** — the hosts prove, but CI has no GPU runner; cells are
  execute-only.
- **sp1** — disabled in `bench-config.json` (execute too slow per push);
  re-enable it there and it returns to the matrices and the parser.
- **Non-`main` base branches** — `fetch-main` queries `branch=main`; a PR
  against another base always pays the local base run.
