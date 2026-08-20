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
| `shard`      | pre-cut the closure-shard artifacts for the env's heavy-tier constants (`ix shard extract` → `ix profile` → `ix shard`) |
| `compare`    | two rows files → Markdown base-vs-PR table (thresholds, ratios, OOM/❌ rows; per-constant phase drop-downs under `BENCH_PHASES=1`) |
| `bmf`        | rows → Bencher Metric Format (non-`ok` rows dropped) |
| `fetch-main` | pull a base SHA's rows from bencher.dev (exit 3 = transient, fall back to a local base run; exit 2 = config error, fail loudly) |
| `report`     | assemble per-cell tables into one Markdown report (CI posts it as the PR comment) |
| `plots`      | sync the bencher dashboard plots to the registry (via the bencher CLI; `--dry-run` previews) |
| `ci matrix`  | emit the workflows' job matrices from the registry (CI adapter) |
| `ci parse`   | `!benchmark` comment → job matrix (CI adapter; `--comment` pre-flights a comment locally) |

### Local usage

```shell
# Run the ooc cell over InitStd's primary constants:
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

# Compare a local run against main's numbers straight from bencher.dev
# (no token needed; --consts filters to your constants — the testbed
# holds every benched env's):
ix bench fetch-main --sha $(git merge-base origin/main HEAD) \
  --backend aiur --mode prove --consts Nat.add_comm --out main.json
ix bench compare --backend aiur --env InitStd --mode prove \
  --base main.json --pr .lake/benches/aiur-InitStd-prove.json

# The recursion cell — fixed IxVM statements (Nat.add_comm,
# Array.extract_append), resolved in the env's .ixe:
ix bench run --backend aiur-recursive --env InitStd --ixe InitStd.ixe

# The lean4lean reference kernel over InitStd — whole-library replay plus
# per-primary closure rows, from oleans (no .ixe needed). Read next to the
# ooc cell's rows for the Rust-vs-reference-kernel gap on the same library:
ix bench run --backend lean4lean --env InitStd
ix bench compare --backend lean4lean --env InitStd

# Recursion layered on a real constant (recursion-tuned FRI parameters;
# an IxVM-scale verifier execute exceeds 100 GB, so cap the watchdog and
# expect the honest oom row on anything big):
ix bench run --backend aiur --env InitStd --mode recursive \
  --consts Nat.add_comm --ixe InitStd.ixe --ceiling-gb 50
```

`--repo <dir>` points the run at another checkout: the *measured* tools
resolve from `<dir>/.lake/build/bin` first, so one `ix` can drive a base and
a PR tree and compare them — exactly what the PR workflow does.

## Backends

| backend | what it measures | tool |
|---|---|---|
| `aiur`    | Aiur STARK check, one bench-main cell per mode on its own testbed: prove — the real-workload simulation (prove-time, proof-size, verify-time, peak-rss, plus fft-cost / execute-time from its own Phase 1) — and execute, the fast Phase-1-only signal (fft-cost, execute-time, throughput, peak-rss). `!benchmark aiur [execute]` picks the mode. A third mode, recursive (`bench-typecheck --recursive`), additionally executes AND proves the in-circuit multi-stark verifier over each fresh proof — the whole system runs under recursion-tuned FRI parameters, so its rows land on their own testbed (`aiur-check-recursive`) and are not comparable to the prove cell's. Unscheduled (the full selection is too heavy for per-push CI — the large closures exceed the RAM ceiling and land as OOM rows — so no CI job runs it and nothing uploads to its testbed; the `aiur-recursive` cell below tracks the same measurement over a fixed two-constant subset): run it locally (`ix bench run --backend aiur --mode recursive`) or request it on demand with `!benchmark aiur recursive` — meant for a bigger manual dispatch | `bench-typecheck` |
| `aiur-recursive` | IxVM recursion on two fixed constants at the ~100-query soundness level (`Nat.add_comm`, the cheap-tier small end; `Array.extract_append`, the heavy-tier kernel-scale one): prove each constant's IxVM typecheck, run the in-circuit multi-stark verifier over the fresh proof (recursive-execute-time, recursive-fft-cost — the recursion-cost proxy), then prove that execution end-to-end (recursive-prove-time, recursive-peak-rss, recursive-proof-size, recursive-verify-time). The same measurement as aiur's recursive mode, but over a fixed subset instead of the `Vectors.csv` fan-out: always exactly one cell regardless of `BENCH_ENVS`, with the constants resolved in whichever env's `.ixe` the cell carries | `bench-typecheck --recursive` |
| `zisk`    | ZisK VM execute: cycles, execute-time, throughput, peak-rss, constants (pre-shard closure count, same universe as aiur's), shards (1 when unsharded) | `zisk-host` |
| `sp1`     | SP1 VM execute (currently disabled in the registry) | `sp1-host` |
| `ooc`     | out-of-circuit Rust kernel: whole-env row + one full-closure row per primary (`check-time` wraps only the check — the env loads once, outside every row's timed window) | `ix check-rs --json` |
| `lean4lean` | the reference Lean4-in-Lean4 kernel ([digama0/lean4lean](https://github.com/digama0/lean4lean), required by the lakefile at a pinned rev) — the external yardstick for the Ix kernels on the same libraries. Olean-driven (no `.ixe`): the whole-library row replays every module in the env's import closure through lean4lean, module-parallel (check-time, constants, throughput, peak-rss; tune parallelism with `LEAN_NUM_THREADS`), plus one full-closure row per primary (the name's transitive closure into a fresh kernel env), mirroring ooc's row shape. Registry-disabled for CI (no bencher testbed yet); `ix bench run --backend lean4lean` works locally regardless | `bench-lean4lean` |
| `compile` | `ix compile <env>.lean → <env>.ixe`: compile-time, file-size, constants, throughput | `ix compile --json` |
| `decompile` | inverse of compile — `ix decompile <env>.ixe → Lean consts`: decompile-time, throughput, peak-rss, constants, file-size (input `.ixe`). Consumes the compile cell's `.ixe` rather than producing one; a malformed decompile reddens the cell. Deep roundtrip fidelity is gated by the canonical checks (`ix validate` / roundtrip tests), which need the original Lean env the `.ixe` can't supply | `ix decompile --json` |

All tools emit the same rows, and all the constant-driven ones take the same
`--consts`/`--consts-file` grammar. (`bench-recursive-verifier`, the local
toy-statement harness for parameter sweeps, instead takes its config as
flags — `--trivial`, `--queries`, `--log-blowup` — with the row name
supplied via `--json-name`.) The ooc and zkVM cells share per-constant
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

`ix bench run` wraps each tool in `.github/scripts/watchdog.sh <ceiling-gb>
<cmd>`: a thin wrapper over `systemd-run --user --scope` that runs the
tool under a cgroup-v2 `memory.max` cap with swap disabled. The kernel
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
!benchmark ([aiur] [zisk] [sp1] [ooc] [compile] [decompile] [aiur-recursive] | all)
           [execute | recursive] [fresh] [KEY=VALUE …]
BENCH_ENVS=InitStd,Mathlib     # default InitStd (case-insensitive); a
                               # compile-only request may name any registry
                               # env (Lean, FLT compile fine, just unbenched)
BENCH_FULL=1                   # full curated set, not just primary
BENCH_SHARD=1                  # only the multi-shard target constants
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
`!benchmark aiur execute BENCH_ENVS=InitStd,Mathlib BENCH_FULL=1`.

The `IX_COMPILE_*` settings change compile-time RAM and speed but produce a
bit-identical `.ixe`, so normal `.ixe` and compile-row caches are keyed only by
commit and env. Add `fresh` when remeasuring a compile knob on an already
benchmarked commit.

Parsed by `ix bench ci parse` in the PR build job, right after the `ix`
binary exists — the registry lives in Lean, so nothing pre-build reads it
(and no Python remains). Mode defaults per backend from the registry; the
bare `execute` token flips `aiur` to Phase-1 only, and `recursive` to its
recursive mode (unscheduled testbed, so no bencher baseline; OOMs the
standard CI host — meant for a bigger manual dispatch). The bare `fresh`
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
`aiur` (execute + prove cells) / `zkvm-execute` / `ooc-check` (each: restore caches, one
`ix bench run … --ixe`, `ix bench bmf`, upload via
`.github/actions/bencher-track`) / `aiur-recursive` (same shape — it
restores the cached `.ixe` its fixed constants resolve in). A kernel
rejection exits 3 and reddens the
run step while the clean rows still upload.

**Dashboard plots**: `ix bench plots` pins one plot per (testbed, measure)
to <https://bencher.dev/console/projects/ix/plots> — main-branch trend
lines, one per benchmark row the cell uploads, plus the cross-kernel
input-constants overlay. Registry-derived like the job matrices (titles,
ordering, and skips live in `Ix/Cli/BenchPlots.lean`), so rerun the sync
after changing the registry or the primary constants — either locally
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

## Not yet covered

- **zkVM prove** — the hosts prove, but CI has no GPU runner; cells are
  execute-only.
- **sp1** — disabled in the registry (execute too slow per push);
  re-enable it there and it returns to the matrices and the parser.
- **aiur recursive over the full selection in CI** — the `aiur-recursive`
  cell tracks IxVM recursion on its two fixed constants, but the full
  `Vectors.csv` fan-out of `bench-typecheck --recursive` is too heavy for
  per-push CI (the large closures exceed the RAM ceiling and land as OOM
  rows), so the `aiur-check-recursive` testbed is registered but
  unscheduled: no bench-main job and no `!benchmark` token. Run it
  locally with `ix bench run --backend aiur --mode recursive`.
