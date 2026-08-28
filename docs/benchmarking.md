# Benchmarking

One orchestrator — `ix bench` — runs every benchmark cell, locally and in CI.
A **cell** is `(backend, env, mode)`, e.g. `zisk-InitStd-execute`. CI is a
thin wrapper: the same `ix bench run` you type in a terminal is what both
workflows execute, so every CI number is reproducible on your machine.

- **`!benchmark` PR comment** (`.github/workflows/bench-pr.yml`) — on demand,
  posts a **base-vs-PR** comparison table on the pull request. The base is the
  PR's actual target branch. Its numbers come from bencher.dev (`ix bench
  fetch-main`) when that SHA was ingested on main; otherwise the workflow
  measures them on a checkout of the base SHA.
- **Bencher.dev** (`.github/workflows/bench-main.yml`) — on every push to
  `main`, tracks each measure over time at <https://bencher.dev> (project
  `ix`), the canonical store the PR path reads from.

## The row contract

Every measured tool reports through one shape — the **benchmark results JSON** —
and one exit-code convention (Rust: `crates/bench`; Lean:
`Ix/Benchmark/Results.lean`):

```json
{ "<name>": { "status": "ok", "<metric>": 123, "phase-<span>": 1.5 } }
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
and `ix bench run` exits nonzero unless **every selected name produced a
row** — an empty or quietly-partial cell can't be green.

## `ix bench` subcommands

| subcommand | job |
|---|---|
| `run`        | run one cell: select names, ensure the `.ixe`, spawn the tool under the RAM watchdog (one process per constant on aiur/zkVM), fold each spawn's span window into its row, gate on the rows |
| `shard`      | pre-cut the closure-shard artifacts for the env's zisk constants (`ix shard extract` → `ix profile` → `ix shard`) |
| `compare`    | two rows files → Markdown base-vs-PR table (thresholds, ratios, OOM/❌ rows; per-constant phase drop-downs under `BENCH_PHASES=1`) |
| `bmf`        | rows → Bencher Metric Format (non-`ok` rows dropped) |
| `fetch-main` | pull a base SHA's rows from bencher.dev (exit 3 = transient, fall back to a local base run; exit 2 = config error, fail loudly) |
| `report`     | assemble per-cell tables into one Markdown report (CI posts it as the PR comment) |
| `plots`      | sync the bencher dashboard plots to the registry (via the bencher CLI; `--dry-run` previews) |
| `ci matrix`  | emit the workflows' job matrices from the registry (CI adapter) |
| `ci parse`   | `!benchmark` comment → job matrix (CI adapter; `--comment` pre-flights a comment locally) |

### Local usage

```shell
# Run the ooc cell over InitStd's benchmark constants:
ix bench run --backend ooc --env InitStd

# Change something, run again, and diff against your previous run
# (runs save baselines under .lake/benches/<cell>{,.prev}.json — the same
# BENCH_OUTPUT_DIR root the Ix.Benchmark framework writes to):
ix bench run --backend ooc --env InitStd --ixe InitStd.ixe
ix bench compare --backend ooc --env InitStd

# One constant through aiur — the fast Phase-1 signal, then the full prove
# (cap the watchdog to what your machine can spare):
ix bench run --backend aiur --env InitStd --mode execute \
  --consts Nat.add_comm --ixe InitStd.ixe --ceiling-gb 50
ix bench run --backend aiur --env InitStd --mode prove \
  --consts Nat.add_comm --ixe InitStd.ixe --ceiling-gb 50

# Optional aggregate W0 diagnostic: prove two singleton CheckEnv shards,
# lift both, then benchmark one flat join. This direct tool invocation emits
# the two child rows plus `Nat.add_comm + String.append` with join-* metrics;
# it is deliberately not part of the scheduled one-constant CI cell.
bench-typecheck --ixe InitStd.ixe \
  --consts Nat.add_comm,String.append --recursive --join --json join.json

# Compare a local run against main's numbers straight from bencher.dev
# (no token needed; --consts filters to your constants — the testbed
# holds every benched env's):
ix bench fetch-main --sha $(git merge-base origin/main HEAD) \
  --backend aiur --mode prove --consts Nat.add_comm --out main.json
ix bench compare --backend aiur --env InitStd --mode prove \
  --base main.json --pr .lake/benches/aiur-InitStd-prove.json

# The lean4lean reference kernel over InitStd — whole-library replay plus
# per-constant closure rows, from oleans (no .ixe needed). Read next to the
# ooc cell's rows for the Rust-vs-reference-kernel gap on the same library:
ix bench run --backend lean4lean --env InitStd
ix bench compare --backend lean4lean --env InitStd
```

`--repo <dir>` points the run at another checkout: the *measured* tools
resolve from `<dir>/.lake/build/bin` first, so one `ix` can drive a base and
a PR tree and compare them — exactly what the PR workflow does.

## Backends

| backend | what it measures | tool |
|---|---|---|
| `aiur`    | the Aiur proof pipeline, per constant: the `ixvm` stage proves the IxVM typecheck, the `fri-verifier` stage executes and proves the in-circuit multi-stark verifier over that fresh proof (the KZG stages fold in as they land, each with its own measure prefix), closed by the pipeline ledger (total-time, pipeline-throughput, pipeline-peak-rss). Each stage's measures carry its prefix (`ixvm-prove-time`, `fri-verifier-fft-cost`, …). The whole system runs under the recursion-tuned FRI parameters. A second mode, execute, is the fast Phase-1-only signal (fft-cost, execute-time, throughput, peak-rss) — unscheduled, local/on-demand only (`!benchmark aiur execute`). The direct `--recursive --join` diagnostic takes exactly two constants as singleton `CheckEnv` shards and appends one pair row carrying `join-{execute-time,fft-cost,prove-time,peak-rss,proof-size,verify-time}`; it remains unscheduled until a runner can carry W0. | `bench-typecheck --recursive` |
| `zisk`    | ZisK VM execute: cycles, execute-time, throughput, peak-rss, constants (pre-shard closure count, same universe as aiur's), shards (the runtime-planned partition size; 1 when the closure fits) | `zisk-host` |
| `sp1`     | SP1 VM execute (currently disabled in the registry) | `sp1-host` |
| `ooc`     | out-of-circuit Rust kernel: whole-env row + one full-closure row per constant (`check-time` wraps only the check — the env loads once, outside every row's timed window) | `ix check-rs --json` |
| `lean4lean` | the reference Lean4-in-Lean4 kernel ([digama0/lean4lean](https://github.com/digama0/lean4lean), required by the lakefile at a pinned rev) — the external yardstick for the Ix kernels on the same libraries. Olean-driven (no `.ixe`): the whole-library row replays every module in the env's import closure through lean4lean, module-parallel (check-time, constants, throughput, peak-rss; tune parallelism with `LEAN_NUM_THREADS`), plus one full-closure row per constant (the name's transitive closure into a fresh kernel env), mirroring ooc's row shape. Registry-disabled for CI (no bencher testbed yet); `ix bench run --backend lean4lean` works locally regardless | `bench-lean4lean` |
| `compile` | `ix compile <env>.lean → <env>.ixe`: compile-time, file-size, constants, throughput | `ix compile --json` |
| `decompile` | inverse of compile — `ix decompile <env>.ixe → Lean consts`: decompile-time, throughput, peak-rss, constants, file-size (input `.ixe`). Consumes the compile cell's `.ixe` rather than producing one; a malformed decompile reddens the cell. Deep roundtrip fidelity is gated by the canonical checks (`ix validate` / roundtrip tests), which need the original Lean env the `.ixe` can't supply | `ix decompile --json` |

### Aggregate W0 baselines

The pre-E2 lift-size pin (2026-08-28) uses the 247-function production
recursion system, default q=100/PoW-20 parameters, and the verified
one-constant aggregate fixture. Its lift proof is **7,986,166 bytes**;
the containing `Ixon.Proof` wrapper is 7,986,204 bytes at store address
`090bea6f1c976ef6677fad94f86286295b2eea751fefb7af4c82ce9f84ca1535`.
Positive-PoW grinding may change the proof contents, but its structural byte
length is stable. WP-E2 measures its proof-size delta against this value.

The box-independent `--queries 0` join wiring gate produced a 246,014-byte
flat-join proof, 10,280,903,348 FFT cost, 6.57 s prove time, 10,798,899,200-byte
peak RSS, and 1.44 ms native verification. Those are smoke values, not W0 cost
estimates; the q=50 join run remains a large-box benchmark.

All tools emit the same rows, and all the constant-driven ones take the same
`--consts`/`--consts-file` grammar. The ooc and zkVM cells share per-constant
**full-closure** scope, so their delta isolates in-circuit vs out-of-circuit
overhead.

With `--texray`, tools write per-phase span timings (`aiur/prove_ixvm`,
`aiur/witness`, `stark/*`, `zisk/execute`, …) to `<json>.spans`. The
per-constant backends run **one process per constant**, so each spawn's
window belongs wholly to its constant: `ix bench run` folds it into the
row as flat `phase-<span>` fields, which flow to bencher as independent
measures (witness gen, stage commits, quotient, … each get a trend line)
and render as a collapsible per-constant drill-down under `BENCH_PHASES=1`
(a `!benchmark` config line, or the env var for a local `ix bench
compare`; off by default — the spans are noisy and dynamically named).

## RAM: watchdog, OOM rows, sharding

`ix bench run` wraps each tool in the typed watchdog (`Ix.Watchdog`,
also used by `lake exe truthmines build`): a `systemd-run --user
--scope` invocation that runs the tool under a cgroup-v2 `memory.max`
cap with swap disabled, probed end to end before any tool spawns (no
watchdog, no run). The kernel
OOM-kills at the ceiling — SIGKILL, exit 137 — with no sampler to race
and nothing to sum: the cgroup charges the whole tree's resident memory,
locked shared segments included, while an allocator's cached virtual
reservations don't count. A killed per-constant process gets
its row marked `status: oom`
(keeping whatever was flushed, spans included) and the loop continues — one
constant's death costs one constant. A kill that lands *after* the row
carries the mode's completion metric hit teardown (the prover releasing
tens of GB right after the final write), so the finished row stays `ok`.
ooc and compile run as single processes instead — their checks never
approach the ceiling, and a kill there means missing rows and a red cell.
There are **no per-constant timeouts**; the job-level `timeout-minutes` is
the only clock.

Every zisk constant runs as a closure-shard partition sized at bench
runtime: `ix shard extract` → `ix profile` → `ix shard` cut a manifest
whose shard count comes from the planner's RAM budget (a closure that
fits gets a one-shard plan), and one `--shard-plan` host run executes the
shards sequentially, emitting the constant's row with per-shard
breakdowns. bench-main's compile job pre-cuts these artifacts
(`ix bench shard`) and ships them via cache; a zisk run cuts lazily when
they're absent, and falls back to the whole closure if the cut fails.

## Registry and constant set

- **`Ix/BenchConstants.lean`** — the shared constant set: one
  `(name, env)` entry per benchmark constant, compiled into `ix`.
  Every per-constant backend runs this same set (a constant whose prove
  exceeds the host's RAM still runs; the row records the OOM), minus the
  hard feasibility exclusions in `benchExclusions`
  (`Ix/Cli/BenchCmd.lean`).
- **The registry** (`envSpecs`/`backendSpecs` in `Ix/Cli/BenchCmd.lean`) —
  everything else: env modules, backends (disabled reason, default mode,
  bencher testbeds, compare columns). Typed Lean data with one owner: the
  workflows never read it directly — `ix bench ci matrix` serves the job
  matrices and `ix bench ci parse` the `!benchmark` cells, both post-build.
  (`bencher-thresholds-reset.yml` keeps a static workload list with a sync
  note.) CI-only data stays out of it: the runner name lives with the `ci`
  adapters. The watchdog ceiling defaults to the machine's RAM minus 15 GB
  (`--ceiling-gb` overrides). The heaviest compile/decompile workload is
  `ix decompile` on Mathlib and FLT, approaching 40 GB now that Pass 2
  holds its kenv rather than clearing it (compile itself peaks around half
  that), so the default only clears it on machines with roughly 55 GB or
  more; cap explicitly below that.

## `!benchmark` grammar

```
!benchmark ([aiur] [zisk] [sp1] [ooc] [compile] [decompile] | all)
           [execute] [fresh] [KEY=VALUE …]
BENCH_ENVS=InitStd,Mathlib     # default InitStd (case-insensitive); a
                               # compile-only request may name any registry
                               # env (Lean, FLT compile fine, just unbenched)
BENCH_CONSTS=Nat.gcd,…         # bench exactly these constants on the
                               # per-constant backends (each name's env is
                               # found automatically)
BENCH_PHASES=1                 # add the per-constant phase drill-downs
                               # to the comment (off by default)
RUST_LOG=info                  # passthrough env (allowlist: BENCH_PHASES,
                               # RUST_LOG, WITHOUT_VK_VERIFICATION, RUSTFLAGS,
                               # IX_COMPILE_EAGER, IX_COMPILE_DEMOTE,
                               # IX_COMPILE_WORKERS,
                               # IX_DECOMPILE_KENV_CLEAR_ENTRIES)
IX_DECOMPILE_KENV_CLEAR_ENTRIES=0
                               # decompile Pass 2 cache limit; 0 disables
                               # clearing (default: 131072)
```

The `KEY=VALUE` config works both as lines below the command (the comment
form above) and inline on the command line, whitespace-separated — the
single-line form for `bench-pr.yml`'s manual workflow_dispatch, whose
input box can't hold newlines:
`!benchmark aiur execute BENCH_ENVS=InitStd,Mathlib`.

The `IX_COMPILE_*` settings change compile-time RAM and speed but produce a
bit-identical `.ixe`, so normal `.ixe` and compile-row caches are keyed only by
commit and env. Add `fresh` when remeasuring a compile knob on an already
benchmarked commit.

Parsed by `ix bench ci parse` in the PR build job, right after the `ix`
binary exists — the registry lives in Lean, so nothing pre-build reads it
(and no Python remains). Mode defaults per backend from the registry; the
bare `execute` token flips `aiur` from the full proof pipeline to the fast
Phase-1-only mode (unscheduled testbed, so no bencher baseline — its base
side comes from a base-SHA run). The bare `fresh`
token makes every cell bypass its bencher baseline and keeps persistent cached
benchmark binaries, compiled `.ixe` files, and compile rows out of measured
jobs. A cached head `ix` may bootstrap the canonical command parser, but the
workflow replaces the full binary bundle before publishing it. Both the PR and
base products are rebuilt; run-scoped artifacts carry them between jobs. Cargo
and package dependency caches remain enabled. PR runs never upload to bencher,
so the comparison prints in the comment and the canonical baseline is
untouched.

## CI shape

**bench-main.yml**: `build` (compile `ix` + `bench-typecheck` once, cache by
SHA) → `plan` (`ix bench ci matrix` → job matrices) + `compile` (per env:
`ix bench run --backend compile`, cache the `.ixe` and pre-cut zisk shards
separately) →
one `benchmark` job per remaining cell — aiur / zisk / ooc / decompile —
(each: restore caches, one `ix bench run … --ixe`, `ix bench bmf`,
upload via `.github/actions/bencher-track`). A kernel
rejection exits 3 and reddens the
run step while the clean rows still upload.

**Dashboard plots**: `ix bench plots` pins one plot per (testbed, measure)
to <https://bencher.dev/console/projects/ix/plots> — main-branch trend
lines, one per benchmark row the cell uploads, plus the cross-kernel
input-constants overlay. Registry-derived like the job matrices (titles,
ordering, and skips live in `Ix/Cli/BenchPlots.lean`), so rerun the sync
after changing the registry or the constant set — either locally
(needs the bencher CLI and a user API key in `BENCHER_API_KEY`;
`--dry-run` previews) or via the `bencher-plots.yml` workflow_dispatch
(run it after bench-main has built the merged registry). Idempotent:
matching plots are kept, stale ones replaced, hand-pinned ones untouched.
The sync also asserts every measure's canonical units (bencher
auto-creates measures with placeholder units on first upload).

**bench-pr.yml**: `setup` (authorize the comment, resolve base/head SHAs) →
`build` (select or build the PR binaries, publish a run-scoped artifact,
then `ix bench ci parse`) → `compile` (one measured `ix compile` per env,
publishing a run-scoped `.ixe` + row artifact) → `benchmark` matrix (per cell:
download only those run artifacts; run the PR side; fetch main's numbers,
with a base-checkout run covering what bencher lacked (including every
non-`main` base, whose `.ixe` can be restored from its earlier PR run);
`ix bench compare` → table artifact) → `assemble` (`ix bench report` builds
the comment body, unprivileged) → `comment` (posts it — the only job with a
write token, running no PR code). Normal runs may seed the run artifacts from
persistent head/base-SHA caches. `fresh` bypasses those caches and rebuilds
the measured products while retaining dependency caches.

Every job that creates a timing row logs its CPU model, instruction set,
effective CPU count, affinity, and cgroup allocation. Because the benchmark
binaries use native codegen, their build jobs also record the build CPU and
carry that report inside the binary cache or run artifact; measurement jobs
print it next to their own host report. A cache entry created before this
provenance was introduced remains usable and is reported as having an unknown
build CPU. The exact `lscpu` model name is compared; a difference (or missing
build provenance) is rendered as a warning in that cell's PR comment table.
This is diagnostic only: the CPU model does not participate in cache keys, and
only an explicit `fresh` request bypasses the measured-product caches.

## Palomar compatibility corpus

The Palomar registry snapshot, isolated workspaces, and Lean-4.33 source ports
live in the standalone sibling repository `Palomar.ix`. That repository uses
ix as its compiler dependency and owns the resulting `palomar.ixc`; Palomar
projects are not duplicated in TruthMines' package graph. A full artifact can
flatten the verified Palomar members into TruthMines without reopening those
workspaces:

```console
(cd ../Palomar.ix && nix develop --command lake exe palomar build)
lake exe truthmines build --palomar-ixc ../Palomar.ix/palomar.ixc
```

The resulting catalog has 97 members: 78 native TruthMines members followed by
the 19 Palomar members, with Palomar's source pins, compatibility-overlay
identities, toolchains, and internal dependency indices preserved.

## TruthMines corpus baselines

`lake exe truthmines build` (the `.ixc` piece pipeline: per-member
watchdogged `ix compile` → self-contained catalog directory →
`ix catalog assemble` + `verify`), first full run recorded 2026-08-21
on the shared 124 GiB box:

The table predates the TauCeti admission and external Palomar composition. The
native full admission spec has 78 members; `--palomar-ixc` expands it to 97.

| leg | figure |
|---|---|
| full corpus build (77 members, cold pieces except 11 cache hits) | **19 min** wall at `--jobs 4` × 25 GiB per-member ceiling; zero member failures, zero OOM kills |
| `truthmines.ixc/` | 50 GB (77 fat pieces; largest: FLT 3.44 GB, Fad 3.38 GB, Mathlib 3.33 GB), manifest 16,237 B |
| union | 906,738 unique constant addresses; `members_root 483bfe87…`, `content_root 5cae665f…` recomputed by verify |
| mini tier (12 members: fixtures + spine + Mathlib + FLT) | ~7 min cold / seconds cached; `truthmines-mini.ixc/` 8.9 GB, 690,628-const union |
| warm rerun | all members cache-hit (pin-closure keys); assemble + verify only |
| `ix merge` of Aesop+Mathlib+FLT pieces | 687,757-const union `.ixe` in 28 s |

For context, the retired union `ix catalog` peaked 35.3 GiB at spine
scale (N=12) and OOM'd this box on its first full-corpus attempt; the
piece pipeline's box pressure is `jobs × member`, never a union.
Per-member kernel checking (`lake exe truthmines check`, suite
`truthmines-check`) and metadata fidelity (`lake exe truthmines
validate`, suite `truthmines-validate`) are the other two rungs over
the same artifacts.

## Not yet covered

- **zkVM prove** — the hosts prove, but CI has no GPU runner; cells are
  execute-only.
- **sp1** — disabled in the registry (execute too slow per push);
  re-enable it there and it returns to the matrices and the parser.
- **aiur prove numbers for the biggest closures** — every constant in the
  shared set runs the full pipeline, but the largest ones exceed the CI
  host's RAM ceiling and land as honest `oom` rows, which never upload
  (`ix bench bmf` drops non-`ok` rows) — their trend lines stay empty
  until the prover's RAM drops under the ceiling.
