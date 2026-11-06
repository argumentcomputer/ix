# Benchmarking

One orchestrator — `ix bench` — runs every benchmark cell, locally and in CI.
A **cell** is `(backend, env, mode)`, e.g. `ooc-InitStd-execute`. For backends
scheduled in CI, the same `ix bench run` you type in a terminal is what both
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
and one exit-code convention (`Ix/Benchmark/Results.lean`):

```json
{ "<name>": { "status": "ok", "<metric>": 123, "phase-<span>": 1.5 } }
```

- Rows are flushed after every name, so a killed run keeps its completed rows.
- `status` is `ok` or `rejected` (written by the tool) or `oom` (merged in by
  `ix bench run` after an abnormal exit — a process never observes its own
  OOM kill). An `oom` row keeps whatever metrics landed before the kill.
  `ix check-lean` also writes `partial` (exit 4: every declaration passed, but
  the whole artifact carries no role binding) and `conditional` (exit 5: it
  passed only with user axioms admitted).
- Exit codes: `0` all ok · `2` usage error · `3` the kernel **rejected** a
  constant (its row is on disk) · `4`/`5` `ix check-lean`'s partial and
  conditional runs (their rows are on disk) · anything else is an
  infrastructure failure.

There is no output scraping anywhere: no marker lines, no log grepping, no
sentinel-key jq. State flows through rows and exit codes only. A rejected or
OOM'd constant never reaches bencher (`ix bench bmf` drops non-`ok` rows),
and `ix bench run` exits nonzero unless **every selected name produced a
row** — an empty or quietly-partial cell can't be green.

## `ix bench` subcommands

| subcommand | job |
|---|---|
| `run`        | run one cell: select names, ensure the `.ixe`, spawn the tool, fold each spawn's span window into its row, gate on the rows |
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
```

`--repo <dir>` points the run at another checkout: the *measured* tools
resolve from `<dir>/.lake/build/bin` first, so one `ix` can drive a base and
a PR tree and compare them — exactly what the PR workflow does.

### PR #665 proving optimization measurement

The 2026-11-03 pass compares against `09ee682af5b0a37ceaad6317683cb772a9cd8ad2`,
the PR revision in [the benchmark comment](https://github.com/argumentcomputer/ix/pull/665#issuecomment-6608664380).
The input is the 253,772,604-byte `InitStd.ixe` with 103 bound roles, 44 evidence
entries and SHA-256
`e48adef624e70bcdd3f22e1d96251682ac046a088700ccf5cf512f1b49afcda1`.
All seven baseline FFT values reproduce the comment's PR column to its
displayed precision. The same constants and admission checks are retained:

| Constant | Checked constants | Baseline FFT cost, billions | Optimized | Reduction |
|---|---:|---:|---:|---:|
| `ByteArray.utf8DecodeChar?_utf8EncodeChar_append` | 3,638 | 126.785 | 121.610 | 4.08% |
| `Char.ofOrdinal_le_of_le` | 3,596 | 91.741 | 87.742 | 4.36% |
| `Array.extract_append` | 2,420 | 92.971 | 90.388 | 2.78% |
| `Std.HashMap` | 2,968 | 63.338 | 60.522 | 4.45% |
| `_private.Init.Data.Range.Polymorphic.SInt.0.Int64.instRxcHasSize_eq` | 2,688 | 55.475 | 53.180 | 4.14% |
| `String.append` | 781 | 4.576 | 4.373 | 4.44% |
| `Nat.add_comm` | 52 | 0.390 | 0.376 | 3.68% |

Paired inner and recursive proofs were generated and verified with 50 FRI
queries, log blowup 2, log final polynomial length 0, max log arity 1 and
zero proof-of-work bits. Each recursive run verifies the corresponding
baseline or optimized inner proof:

| Measure | `Nat.add_comm` | `String.append` |
|---|---:|---:|
| Inner proof bytes | 5,673,393 → 5,390,069 (−4.99%) | 6,450,356 → 6,153,240 (−4.61%) |
| Recursive FFT cost, billions | 94.551 → 88.886 (−5.99%) | 109.191 → 100.616 (−7.85%) |
| Outer proof bytes | 2,807,371 → 2,822,459 (+0.54%) | 2,811,979 → 2,833,115 (+0.75%) |

The wider, four-byte BLAKE3 loop reduces recursive work with a small outer
proof-size increase. These are improvements over the PR revision; some
costs remain above main's figures with the PR's larger checked workload.
Generic bytecode execution was used for source iteration. The regenerated
native backend was checked for correctness with codegen compilation at
optimization level 0; its wall times are not native CI speedup measurements.

The host `IOBuffer.extend` change is separate from those circuit measurements.
On frozen `HEq` and `String.append` fixture environments, old and new native
witness builders produced identical 33,172,696-byte serializations, including
arena and key-map order, offsets and lengths. Local witness construction took
20,023/18,570 ms before and 129/121 ms after. These diagnostics isolate the
arena-copy fix; they do not measure end-to-end proving or CI wall time.

Caching the environment's role binding across constants in the benchmark
runners (`assumeBinding := true` in the retired proving runner, matching the production
claim tree where the binding is proven once and assumed by per-constant claims,
and upfront `verdict_work` support checking in the Rust kernel's anonymous
check, since retired) eliminates redundant per-constant role-table re-admission.
The `ooc` column was measured when `ooc` ran the Rust kernel:

| Constant | Checked constants (assumed binding) | Stage 1 FFT cost, billions (`09ee682` → assumed binding) | `ooc` check-time (s) |
|---|---:|---:|---:|
| `ByteArray.utf8DecodeChar?_utf8EncodeChar_append` | 2,697 | 126.785 → 121.304 (−4.32%) | 0.819 |
| `Char.ofOrdinal_le_of_le` | 2,676 | 91.681 → 86.924 (−5.19%) | 0.153 |
| `Array.extract_append` | 1,509 | 92.985 → 87.989 (−5.37%) | 0.383 |
| `Std.HashMap` | 2,039 | 63.352 → 58.138 (−8.23%) | 0.087 |
| `_private.Init.Data.Range.Polymorphic.SInt.0.Int64.instRxcHasSize_eq` | 1,768 | 55.479 → 50.474 (−9.02%) | 0.086 |
| `String.append` | 263 | 4.581 → 3.070 (−32.98%) | 0.015 |
| `Nat.add_comm` | 34 | 0.390 → 0.377 (−3.33%) | 0.004 |

With `assumeBinding := true` on the 32-vCPU benchmark host (`r8i.8xlarge`),
inactive role-validation circuits drop out of per-constant proofs, reducing
`Nat.add_comm` Stage 1 proof size from 6.08 MiB to 4.99 MiB (−17.9%), Stage 2
`fri-verifier` FFT cost from 114.68B to 90.65B (−21.0%), and end-to-end
recursive `total-time` from 64.47s to 31.38s (−51.3%); `String.append` Stage 1
proof size drops from 6.18 MiB to 5.19 MiB (−16.0%), Stage 2 `fri-verifier`
FFT cost from 115.65B to 99.33B (−14.1%), and `total-time` from 63.85s to
34.42s (−46.1%).

## Backends

| backend | what it measures | tool |
|---|---|---|
| `ooc`     | out-of-circuit Lean kernel (`IxC`): whole-env row + one full-closure row per constant (`check-time` wraps only the check — the env loads once, outside every row's timed window) | `ix check-lean --anon --json` |
| `compile` | `ix compile <env>.lean → <env>.ixe`, the default certified compiler: compile-time, file-size, constants, throughput | `ix compile --json` |
| `decompile` | inverse of compile — `ix decompile <env>.ixe → Lean consts`: decompile-time, throughput, peak-rss, constants, file-size (input `.ixe`). Consumes the compile cell's `.ixe` rather than producing one; a malformed decompile reddens the cell. Deep roundtrip fidelity is gated by the canonical checks (`ix validate` / roundtrip tests), which need the original Lean env the `.ixe` can't supply | `ix decompile --json` |

The `compile` benchmark switches from the uncertified Rust compiler to the
certified default in this change. Certified uploads use the distinct
`ix-compile-certified` workload and testbeds, with the same regression
thresholds. Historical Rust rows remain in `ix-compile` and appear as separate
lines on the compile plots; they never enter the certified alert baseline.
PR comparisons across the switch include the cost of certification and remain
informational: the table displays the delta without failing on its size.
Compiler failures, missing rows and kernel rejections still fail their jobs.

The certified checker's environment check (`kernel-check-ixe`, the verified checker behind the Ixon
reader) is documented in [Benchmarks/Kernel/README.md](../Benchmarks/Kernel/README.md)
and [kernel.md](kernel.md). It is separate from the compiler and `ooc` benchmarks above;
the former Lean4Lean replay backend has been retired.

Formal Aiur proving has no `ix bench` backend. Whole-environment GPU proving
runs are benchmarked by hand as described in
[aiur-gpu-proving.md](aiur-gpu-proving.md#6-benchmarking-a-multi-gpu-run).

All tools emit the same rows, and all the constant-driven ones take the same
`--consts`/`--consts-file` grammar. The ooc cells use per-constant
**full-closure** scope.

With `--texray` or `IX_TEXRAY=1`, tools write per-phase span timings to `<json>.spans`.
`ix bench run` folds a spawn's window into its row as flat `phase-<span>` fields, which flow to bencher as independent
measures (witness gen, stage commits, quotient, … each get a trend line)
and render as a collapsible per-constant drill-down under `BENCH_PHASES=1`
(a `!benchmark` config line, or the env var for a local `ix bench
compare`; off by default — the spans are noisy and dynamically named).

## Memory: OOM rows

The tools set no memory limit of their own. CI runs every `ix bench run`
through `.github/scripts/memory-cap`: a `systemd-run --user --scope` with
cgroup-v2 `MemoryMax` at the runner's RAM minus 15 GiB and swap disabled.
At the cap the kernel OOM-kills the largest process in the scope, the
measured tool, with SIGKILL (exit 137), and `ix bench run` survives to
gate on the rows. ooc and compile run as single processes, so a kill there
means missing rows and a red cell. Preparing a missing `.ixe` uses the
default compiler, outside the consumer's timed window. Wrap a local run in
the same script to get the same cap.
There are **no per-constant timeouts**; the job-level `timeout-minutes` is
the only clock.

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
  note.) Runner provisioning lives in the workflows; `IX_BENCH_MACHINE`
  selects the matching Bencher testbed. Certified compilation can use
  substantially more RAM than the historical Rust compile series; the
  benchmark runners have 256 GiB, leaving about 240 GiB under
  `memory-cap`.

## `!benchmark` grammar

```
!benchmark ([ooc] [compile] [decompile] | all)
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
                               # RUST_LOG, RUSTFLAGS,
                               # IX_COMPILE_EAGER, IX_COMPILE_DEMOTE,
                               # IX_COMPILE_WORKERS, BENCH_TRACE_SHARDS,
                               # IX_DECOMPILE_KENV_CLEAR_ENTRIES)
IX_DECOMPILE_KENV_CLEAR_ENTRIES=0
                               # decompile Pass 2 cache limit; 0 disables
                               # clearing (default: 131072)
```

The `KEY=VALUE` config works both as lines below the command (the comment
form above) and inline on the command line, whitespace-separated — the
single-line form for `bench-pr.yml`'s manual workflow_dispatch, whose
input box can't hold newlines:
`!benchmark ooc BENCH_ENVS=InitStd,Mathlib`.

The allowlisted `IX_COMPILE_*` settings tune the Rust compiler used by older
base checkouts; they do not tune the certified compiler. Normal `.ixe` and
compile-row caches are keyed by commit and env. Add `fresh` when remeasuring
a compile setting on an already benchmarked commit.

Parsed by `ix bench ci parse` in the PR build job, right after the `ix`
binary exists — the registry lives in Lean, so nothing pre-build reads it
(and no Python remains). Mode defaults per backend from the registry, and
every remaining backend has only its `execute` mode. The bare `fresh`
token makes every cell bypass its bencher baseline and keeps persistent cached
benchmark binaries, compiled `.ixe` files, and compile rows out of measured
jobs. A cached head `ix` may bootstrap the canonical command parser, but the
workflow replaces the full binary bundle before publishing it. Both the PR and
base products are rebuilt; run-scoped artifacts carry them between jobs. Cargo
and package dependency caches remain enabled. PR runs never upload to bencher,
so the comparison prints in the comment and the canonical baseline is
untouched.

## CI shape

**bench-main.yml**: `build` (compile `ix` once, cache by
SHA) → `plan` (`ix bench ci matrix` → job matrices) + `compile` (per env:
`ix bench run --backend compile`, cache the `.ixe`) →
one `benchmark` job per remaining cell — ooc / decompile —
(each: restore caches, one `ix bench run … --ixe`, `ix bench bmf`,
upload via `.github/actions/bencher-track`). A kernel
rejection exits 3 and reddens the
run step while the clean rows still upload.

**Dashboard plots**: `ix bench plots` pins one plot per (workload, measure)
to <https://bencher.dev/console/projects/ix/plots> — main-branch trend
lines on the historical Warp and native r8i testbeds, with a separate line
per benchmark row and testbed so hardware changes preserve the visible history,
plus the cross-kernel input-constants overlay, sourced from the native ooc
backend. Registry-derived like the job matrices (titles,
ordering, and skips live in `Ix/Cli/BenchPlots.lean`), so rerun the sync
after changing the registry or the constant set — either locally
(needs the bencher CLI and a user API key in `BENCHER_API_KEY`;
`--dry-run` previews) or via the `bencher-plots.yml` workflow_dispatch
(run it after bench-main has built the merged registry). Idempotent:
matching plots are kept, stale ones replaced, hand-pinned ones untouched.
The sync also asserts every measure's canonical units (bencher
auto-creates measures with placeholder units on first upload).

**bench-pr.yml**: `dispatch` (authorize the comment, resolve base/head SHAs,
then start the cache-writing run) → `build` (select or build the PR binaries,
publish a run-scoped artifact, then `ix bench ci parse`). `announce` posts the
initial running/error comment while `compile` runs one measured `ix compile`
per env and publishes a run-scoped `.ixe` + row artifact. The `benchmark`
matrix downloads only those run artifacts, runs the PR side, and fetches
main's numbers, with a base-checkout run covering what bencher lacked
(including every non-`main`
base, whose `.ixe` can be restored from its earlier PR run); `ix bench compare`
then publishes a table artifact. `assemble` runs `ix bench report` without
write privileges, and `comment` replaces the initial comment. Only `announce`
and `comment` hold write tokens, and neither checks out or runs PR code. Normal
runs may seed the run artifacts from persistent head/base-SHA caches. `fresh`
bypasses those caches and rebuilds the measured products while retaining
dependency caches.

### RunsOn machines and caching

Benchmark jobs use exact `r8i` instance types; CI jobs request the
`r7i+r8i+r7a+r8a` families so Spot has several pools to fill from. All use
the `ubuntu26-full-x64` image with the default Spot policy. RunsOn can fall
back to on-demand capacity and automatically retry interrupted jobs. There
are no GPU benchmark jobs in CI; future GPU jobs should use `spot=false`.
For manual measurements, follow the
[Aiur proving guide](aiur-gpu-proving.md#6-benchmarking-a-multi-gpu-run) or the
[KZG benchmark recipe](../crates/proof-compression/README.md#kzg-benchmarking),
which defines input boundaries, NVMe/cache placement, and cold/warm state.
The CUDA compile job runs its toolchain in an Ubuntu 26.04
container on a CPU runner. Jobs that use `ubuntu-latest` remain on GitHub-hosted runners. See
[CI and merge queue configuration](ci.md) for the required checks and retry
behavior.
The [instance sizes](https://aws.amazon.com/ec2/instance-types/memory-optimized/)
preserve each job's vCPU count, with more RAM per vCPU; every listed r-family
offers the same shapes:

| vCPUs | Size | RAM |
| --- | --- | --- |
| 8 | `2xlarge` | 64 GiB |
| 16 | `4xlarge` | 128 GiB |
| 32 | `8xlarge` | 256 GiB |

Benchmark builds, compile measurements, and runs all use `r8i.8xlarge` with
`-Ctarget-cpu=native`. Jobs that only run the native `ix` to report or sync
plots use the smallest r8i size (`cpu=2/family=r8i`): every r8i size has the
same CPU, so the binary runs there, and nothing they do is timed. CI jobs pin
`x86-64-v4` plus `avx512vbmi2` and `gfni`,
the baseline shared by every family they may land on; Valgrind builds without
AVX-512 into the S3-backed actions cache under its own key. Benchmark product caches and Cargo
caches include the instance family and code generation. Bencher testbeds
include both, such as `ooc-check-runs-on-r8i-8xlarge-native`, so old binaries
and timings from different hardware or compiler flags stay separate.
A hardware trial must change the runner labels, sticky cache lineages,
`IX_BENCH_MACHINE`, `BENCH_CACHE`, the Rust action's cache key, and the allowed
`benchmarkMachines` in `Ix/Cli/BenchCmd.lean` together. Add `fresh` to a PR
benchmark command to remeasure both commits while still reusing dependency
caches.

[RunsOn sticky disks](https://runs-on.com/docs/runners/capabilities/sticky-disks/)
cache the Lake and Cargo directories for CI, merge tests, and Nix. Each CI
job has a separate cache lineage and runs independently. Merge-test partitions
share a lineage, with each job restoring its own snapshot and the last clean
completion advancing the cache. Snapshots restore with provisioned
initialization: `lazy-init` saves that charge but turns every first read of a
cached binary or olean into a slow page fault, which dominates test jobs
that compile nothing. Cachix remains the Nix store's binary cache, with
`/nix` and build scratch space on a 150 GB root volume.

[RunsOn Magic Cache](https://runs-on.com/docs/performance/caching/actions/)
is enabled with `extras=s3-cache` and `runs-on/action@v2` before any cache or
artifact action. Benchmark handoffs and the CUDA container use
`actions/cache@v6` (including restore/save) and the Rust setup action's
standard cache with the RunsOn S3 backend. The RunsOn GitHub App and AWS
stack must already be installed for this repository, in a region with r8i
available. Sticky disks require RunsOn v3.2.0 or later. The first run starts
with cold caches and a new native-codegen benchmark history.

Every job that creates a timing row logs its CPU model, instruction set,
effective CPU count, affinity, and cgroup allocation directly in the Actions
logs. Each table in the `!benchmark` comment ends with one hardware line per
side (CPU model, effective vCPUs, total RAM), because the two sides need not
share a host: the PR compile row is measured in the compile job, and a
bencher-sourced base side was measured by bench-main at the base SHA, which
caches that host next to its upload for the PR run to restore. A base run
performed in the benchmark job is labelled with that job's runner. This is
diagnostic only: the selected instance type determines cache and testbed
names, while the detected CPU description remains a report annotation. A
missing note renders as "not recorded".

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
`ix compile` → self-contained catalog directory →
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
`truthmines-check`) is the other rung over the same artifacts.
