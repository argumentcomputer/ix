# Benchmarking

Ix is benchmarked on two surfaces, both driven by one curated constant set and
the same backend drivers:

- **`!benchmark` PR comment** (`.github/workflows/bench-pr.yml`) — on demand,
  posts a **main-vs-PR** comparison table on the pull request. main's numbers
  are pulled from bencher.dev via its public reports API (`bench.py fetch-main`);
  the PR side is measured fresh. If bencher hasn't ingested the base SHA yet
  (freshly-pushed main whose push CI is still running), the workflow falls
  back to re-running the base SHA locally.
- **Bencher.dev** (`.github/workflows/bench-main.yml`) — on every push to `main`,
  tracks each measure over time at <https://bencher.dev> (project `ix`). This is
  the canonical store for main-branch measurements; the `!benchmark` PR path
  reads from it.

## Backends

| backend | what it measures | metrics |
|---|---|---|
| `aiur` | IxVM kernel typecheck in the Aiur STARK prover (out-of-circuit execute + in-circuit prove) | `fft-cost`, `execute-time`, `execute-peak-rss`, `prove-time`, `peak-rss` |
| `zisk` / `sp1` | the same kernel in the Zisk / SP1 zkVM hosts, **execute** only (proving needs a GPU) | `cycles`, `execute-time`, `throughput`, `execute-peak-rss` |
| `ooc` | the same kernel run **out-of-circuit and in parallel** (`ix check-rs`) — far faster | `throughput`, `check-time`, `peak-rss` |
| `compile` | `ix compile <env>.lean → <env>.ixe` on the current PR — measures the compile step itself, keyed by CamelCase env slug (`InitStd`, `Lean`, `Mathlib`, `FLT`) | `compile-time`, `throughput`, `file-size`, `constants` |

In **prove** mode, `run.sh` attempts a full prove for every primary — cheap
*and* heavy. A RAM watchdog (`watch_ram_kill`) samples the process tree's RSS
every ~3 s and `SIGKILL`s the tree if it exceeds `AIUR_PROVE_MAX_RSS_GB`
(default 120 GB — 8 GB headroom under a 128 GB runner). When killed, the
constant records the neutral `{"oom": true}` sentinel and `bench.py compare`
renders `OOM` cells (with `n/a` Δ%) in the table for that row.

The `ooc` backend reports two views: the **whole env** (`ix check-rs --anon`,
keyed by env) and a **per-primary full-closure check** (`ix check-rs --anon
--consts <name>`, keyed by constant). The per-primary view runs the constant's
full dependency closure in anon mode — the same mode and scope as the zkVM
execute — so the delta isolates in-circuit vs out-of-circuit overhead rather
than mixing in closure-size or metadata effects. (`--skip-deps` exists on both
sides for a subject-only variant, but the benchmarks use full-closure.)

All are driven by `.github/scripts/run.sh` (compile the env `.ixe`, run the
backend, emit a neutral `{ "<name>": { "<metric>": n } }` JSON). The PR workflow
compares two such JSONs; the bencher workflow wraps one in Bencher Metric
Format.

### Peak RAM and the per-phase drill-down (tracing-texray)

Every tool sources `peak-rss` from **tracing-texray's process-tree sampler** — a
background thread that sums `VmRSS` across the process *and its children* and
tracks the high-water mark. This captures memory that a bare `/proc/self/status`
read misses, most importantly Zisk's ASM microservices (separate PIDs).

Each tool also writes its per-phase span timings (tracing-texray's JSON-Lines
sink, one `{"span","seconds"}` per closed span) to a side file, which `run.sh`
aggregates into a `phases` object on the constant's entry. `aiur` yields a rich
breakdown (`aiur/execute`, `aiur/witness`, `stark/fri_open`, …) since the prover
instruments those spans; `zisk`/`sp1` record a single `execute`/`prove` phase;
`ooc` records none. `bench-main.yml` flattens the `phases` object into
`phase:<span>` measures on the way to bencher, so each span is tracked over
time. (**TODO**: `bench.py compare` used to emit a per-constant collapsible
drill-down in the PR comment; that renderer was removed while the primary
table's flag / threshold semantics were being stabilised — see the TODO in
`bench.py` at the previous `_phase_details` location. The `phases` data is
still populated in the neutral JSON, ready to consume.)

## Constant set — `Benchmarks/Vectors.csv`

One CSV is the single source of truth for *which* constants to run:
`name,env,tier,shard_target,primary`. Rows may omit trailing zero fields — the
parser tolerates 3, 4, or 5 columns, defaulting `shard_target` and `primary`
to `0`. Measurements never live here; they live in each tool's neutral results
JSON and in bencher.dev.

- `env` — compile target the constant resolves in (`initStd` / `lean` / `mathlib`).
- `tier` — `cheap` (prove-feasible on a CI runner under Aiur's ~128 GB RAM
  ceiling) or `heavy` (a single-shard prove exceeds the RAM watchdog ceiling
  and records an OOM row). Consumed only by `bench.py manifest` for selection
  (the `BENCH_TIER` filter, and the non-primary prove set defaults to cheap);
  `run.sh` itself never branches on tier — it attempts a full prove of every
  selected constant under the watchdog.
- `primary` — the curated **primary subset** (currently ~20 constants across
  initStd + mathlib), spanning shape and cost range. Default for the
  `!benchmark` PR comment and the bencher jobs. Set `BENCH_FULL=1` to include
  everything (~68 total).
- `shard_target` — marks a heavy constant designated for the manifest-sharded
  prove path (currently 4 rows).

`bench.py manifest` selects names by env + `--primary` (plus optional
`--tier`, `--shard`). The `compile` backend short-circuits this — its
"benchmark" is the env slug itself, so `manifest` writes a one-line
`names.txt` with the CamelCase env name (`InitStd`, etc.) and skips the CSV.
`bench.py compare` renders the PR table from the two side JSONs.

## `!benchmark` grammar

Maintainer comment on a PR:

```
!benchmark ([aiur] [zisk] [sp1] [ooc] [compile] | all) [execute]
BENCH_ENVS=initStd,mathlib     # which compiled envs (default initStd)
BENCH_FULL=1                   # run the full curated set, not just primary
BENCH_TIER=cheap|heavy|all     # tier override (default: all)
BENCH_SHARD=1                  # restrict to the multi-shard target constants
RUST_LOG=info                  # passthrough env (allowlisted)
```

Mode is fixed per backend: `aiur` runs `prove` by default (its report also
carries the execute-side columns `fft-cost` / `execute-time` /
`execute-peak-rss` alongside `prove-time` / `peak-rss` — `execute-peak-rss`
is sampled at the Phase 1/2 boundary, before proving allocations, precisely
so execute-mode comparisons stay apples-to-apples against prove-run
baselines); `zisk` / `sp1` / `ooc` run `execute`; `compile` runs `ix
compile`. The optional bare `execute` token flips `aiur` to execute-only
(`bench-typecheck --execute-only`, skips Phase 2); on other backends it's a
no-op. Defaults: `aiur`, `initStd`, primary subset. Backends fan out as a
matrix; each cell is one `(backend, env, mode)` job. main's numbers are
pulled from bencher.dev.

## Bencher jobs (`bench-main.yml`)

`build → compile → { prove, zkvm-execute, ooc-check }`, each reporting to its
own testbed + **workload** (`aiur-check`, `zisk-check`, `sp1-check`,
`ooc-check`, `ix-compile`). The four typecheck testbeds share the shape
`<backend>-check-x64-32x`; the compile job uses `ix-compile-x64-32x`. Every
bench job runs on the same runner (`warp-ubuntu-latest-x64-32x`).

Threshold semantics per measure kind:
- **`constants`** — pinned exactly (0/0). A definitional count; either
  direction is worth flagging (someone added/removed a def).
- **`fft-cost`, `cycles`, `shards`, `max-shard-cycles`** — deterministic but
  directional: `upper 0` (any increase is a real regression), `lower _`
  (drops are legitimate wins — algorithmic improvements, better packing).
- **`execute-time`, `prove-time`, `check-time`, `compile-time`, `peak-rss`,
  `execute-peak-rss`, `file-size`** — noisy wall-clock or size measures:
  `upper 0.05–0.10`, `lower _`. `execute-peak-rss` is the execute phase's RSS
  high-water on every backend that has one (bench-typecheck samples it at the
  Phase 1/2 boundary; the zkVM hosts' execute peak carries the same name);
  bare `peak-rss` is a prove-phase (or, for ooc, whole-check) peak.
- **`throughput`** — higher-is-better: `upper _`, `lower 0.05–0.10`.
- **`phase:<span>`** — uploaded for trend visibility, intentionally left
  un-thresholded (dynamic names + noise; the PR-comment drill-down is where
  phase-level attention goes when the drill-down is reinstated).

All thresholds are windowed to the per-workload
`bencher-thresholds-reset-<workload>` tag.

To re-baseline a workload after an intended step change, comment
`!bencher-thresholds-reset <workload|all>` on the merging PR, or run the
`bencher-thresholds-reset` workflow
(`.github/workflows/bencher-thresholds-reset.yml`).

## Not yet covered

- **zkVM proving** (Zisk/SP1 `prove`) is not wired up — needs a self-hosted
  GPU runner. `bench.py`'s parse layer treats `zisk`/`sp1` as `execute`-only.
- **Per-constant phase drill-down** in the PR comment (was removed while the
  primary table's semantics were stabilised; TODO in `bench.py` marks the
  reinstatement point — the `phases` data is still populated in the
  neutral JSON and flattened to `phase:<span>` on bencher).
- **Non-`main` base branches** — `bench.py fetch-main` hardcodes
  `branch=main`; a PR against a non-main base always falls through to the
  local base-run path. TODO in `bench.py` lays out the three-step plan
  (producer / consumer / fallback).
