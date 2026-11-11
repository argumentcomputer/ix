# Benchmarking

One orchestrator — `ix bench` — runs every benchmark cell, locally and in CI.
A **cell** is `(backend, env)`, e.g. `ixvm-ooc-InitStd`. Each backend measures
either the shared constants (each in its env) or the envs themselves. For backends
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
{ "<name>": { "status": "ok", "<metric>": 123 } }
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
  conditional runs (their rows are on disk) · `6` `bench-ixvm`'s proving
  failed after the constant executed (the execution row is on disk) ·
  anything else is an infrastructure failure.

There is no output scraping anywhere: no marker lines, no log grepping, no
sentinel-key jq. State flows through rows and exit codes only. A rejected or
OOM'd constant never reaches bencher (`ix bench bmf` drops non-`ok` rows),
and `ix bench run` exits nonzero unless **every selected name produced a
row** — an empty or quietly-partial cell can't be green.

## `ix bench` subcommands

| subcommand | job |
|---|---|
| `run`        | run one cell: select names, ensure the `.ixe`, spawn the tool (one `bench-ixvm` per constant on ixvm), gate on the rows |
| `compare`    | two rows files → one cell's Markdown base-vs-PR table, the renderer the PR comment uses (`base | PR | Δ%` columns per metric, ⚠️/🟢 past ±3%, ❌ OOM and ❌ rejected cells) |
| `bmf`        | rows → Bencher Metric Format (non-`ok` rows dropped) |
| `fetch-main` | pull a base SHA's rows from bencher.dev (exit 3 = transient, fall back to a local base run; exit 2 = config error, fail loudly) |
| `report`     | assemble per-cell results into one Markdown report, one table per backend (CI posts it as the PR comment) |
| `plots`      | sync the bencher dashboard plots to the registry (via the bencher CLI; `--dry-run` previews) |
| `ci matrix`  | emit the workflows' job matrices from the registry (CI adapter) |
| `ci parse`   | `!benchmark` comment → job matrix (CI adapter; `--comment` pre-flights a comment locally) |

### Local usage

```shell
# Run the ixvm-ooc cell over InitStd: its shared constants and its env row:
ix bench run --backend ixvm-ooc --env InitStd

# Only some rows: --constants takes all (default), none, or comma names;
# --no-env-row skips the whole-env measurement:
ix bench run --backend ixvm --env InitStd --constants Nat.add_comm --no-env-row

# Also prove, aggregate, verify and KZG-compress the constant rows:
ix bench run --backend ixvm --mode compress --env InitStd --no-env-row

# One ixvm constant row directly, without the driver (needs the .ixe):
lake exe bench-ixvm --ixe InitStd.ixe --const Nat.add_comm --mode prove --json rows.json

# Change something, run again, and diff against your previous run
# (runs save baselines under .lake/benches/<cell>{,.prev}.json — the same
# BENCH_OUTPUT_DIR root the Ix.Benchmark framework writes to):
ix bench run --backend ixvm-ooc --env InitStd --ixe InitStd.ixe
ix bench compare --backend ixvm-ooc --env InitStd
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

A backend's rows are of two kinds. A **constant row** measures one shared
constant (`Ix/BenchConstants.lean`) in its own env and is keyed by the
constant's name; an **env row** measures a whole registry env (InitStd,
ISLB, Mathlib) and is keyed by the env's name. `ixvm` and `ixvm-ooc` have
both kinds; `compile` and `decompile` have env rows only. Both kinds upload
to the backend's one testbed, so they draw as lines of the same plot per
measure; a measure only one kind carries (e.g. `shards`) has no lines of
the other. A cell `(backend, env)` runs the env's selected constant rows
and, if selected, its env row.

| backend | rows | what it measures | tool |
|---|---|---|---|
| `ixvm` | constant | formal Aiur execution of the certified IxVM claim verifier, no proving, in one `bench-ixvm` process per constant that loads the env and programs once, outside every timed window: `execute-time` (the texray `aiur/execute` span around binding and executing the claim) and `peak-rss` (the process's peak, sampled over the execution) | `bench-ixvm --ixe <env>.ixe --const <name>` |
| `ixvm` | env | the same execution over the whole env: `ix shard --max-ram 100` partitions it (outside the timed window), then one `ix check` executes every shard's claim, one job per core: `execute-time` (the wall clock of that concurrent execution, after the env load, which `ix check --batch-time` records), `peak-rss`, `shards` | `ix check --ixe <env>.ixe --ixes <manifest> --jobs 0` |
| `ixvm prove` | constant | the constant proven end to end, in the same `bench-ixvm` process after its execution: it extracts a one-constant env and splits it into two shards (setup, untimed; aggregation needs a join), proves both claims and joins them into a root on the in-process aggregate controller with no proof reused from the index or cache (`prove-time`, `prove-peak-rss`, `prove-proof-size`, and `prove-trace-shards`: the trace shards of the two claim proofs), checks the root proves the env's statement, and verifies it (`verify-time`) | `bench-ixvm --ixe <env>.ixe --const <name> --mode prove` |
| `ixvm compress` | constant | executes and proves the constant (as `ixvm prove`), then `ix compress` compresses the root to KZG with development parameters (`compress-time`, `compress-peak-rss`, `compress-proof-size`) and verifies it (`compress-verify-time`) | `ix compress <root> --dev-kzg-srs` |
| `ixvm-ooc` | constant | out-of-circuit Lean kernel (`IxC`) over each constant's full closure, user axioms admitted as the `ixvm` claim context admits them: `check-time` wraps only the check — the env loads once, outside every row's timed window, and the rows share that process, so they report no peak RSS of their own | `ix check-lean --anon --allow-user-axioms --consts-file` |
| `ixvm-ooc` | env | the same kernel over the whole env. An env with user axioms gets a `conditional` verdict (it holds only under the axioms listed); its row is measured and uploaded like an `ok` one | `ix check-lean --anon --allow-user-axioms --per-const` |
| `compile` | env | `ix compile <env>.lean → <env>.ixe`, the default certified compiler: compile-time, file-size, constants, throughput | `ix compile --json` |
| `decompile` | env | inverse of compile — `ix decompile <env>.ixe → Lean consts`: decompile-time, throughput, peak-rss, constants, file-size (input `.ixe`). Consumes the compile cell's `.ixe` rather than producing one; a malformed decompile reddens the cell. Deep roundtrip fidelity is gated by the canonical checks (`ix validate` / roundtrip tests), which need the original Lean env the `.ixe` can't supply | `ix decompile --json` |

The PR comment shows each backend's env and constant rows in one table
(see [The PR comment](#the-pr-comment)).

Proving applies to constant rows only: an env row stays execution-only
(whole-env proving is too slow for CI), and `ix bench run` says so when
both are selected. Each stage's measures are stage-qualified bencher
measures with their own plots, and the PR comment gives each stage its own
table. Locally, `ix bench run --backend ixvm --mode prove` and `--mode compress`
select the same stages as the PR subcommands. bench-main measures execution only.

The `compile` benchmark switches from the uncertified Rust compiler to the
certified default in this change. Certified uploads use the distinct
`ix-compile-certified` workload and testbeds. Historical Rust rows remain in
`ix-compile`, which the dashboard no longer plots.
PR comparisons across the switch include the cost of certification and remain
informational: the table displays the delta without failing on its size.
Compiler failures, missing rows and kernel rejections still fail their jobs.

The certified checker's environment check (`kernel-check-ixe`, the verified checker behind the Ixon
reader) is documented in [Benchmarks/Kernel/README.md](../Benchmarks/Kernel/README.md)
and [kernel.md](kernel.md). It is separate from the compiler and `ixvm-ooc` benchmarks above;
the former Lean4Lean replay backend has been retired.

Whole-environment GPU proving runs are benchmarked by
hand as described in
[aiur-gpu-proving.md](aiur-gpu-proving.md#6-benchmarking-a-multi-gpu-run).
`ix check` reads its compiled programs from `IX_AIUR_CACHE` (default
`~/.ix/cache/aiur`), which `lake build ix` fills. A program missing from the
cache is compiled inside the measured `ix check`, so warm the cache before
measuring.

All tools emit the same rows, and all the constant-driven ones take the same
`--consts`/`--consts-file` grammar. Constant rows use per-constant
**full-closure** scope.

The `ixvm` constant rows come from `bench-ixvm`, which writes them itself: it
reads its claim's `aiur/execute` span from its own texray sink, records a
failing claim that executed as a `rejected` row, and writes no row when the
check failed before executing the claim. Each later stage merges its fields
into the row as it completes. The env row reads the batch's wall clock from
`ix check --batch-time`.

## Memory: OOM rows

The tools set no memory limit of their own. CI runs every `ix bench run`
through `.github/scripts/memory-cap`: a `systemd-run --user --scope` with
cgroup-v2 `MemoryMax` at the runner's RAM minus 15 GiB and swap disabled.
At the cap the kernel OOM-kills the largest process in the scope, the
measured tool, with SIGKILL (exit 137), and `ix bench run` survives it. The
`ixvm` constant rows run one `bench-ixvm` per constant, with execution and
proving in that process, so a kill marks that constant's row `status: oom` and the loop
continues: one constant's death costs one constant. An `ixvm` env-row kill
marks the env row `oom`. The `ix check-lean` and `ix compile` backends run as
single processes that write their own rows, so a kill there means missing
rows and a red cell. Preparing a missing `.ixe` uses the default compiler,
outside the consumer's timed window. Wrap a local run in the same script to
get the same cap.
There are **no per-constant timeouts**; the job-level `timeout-minutes` is
the only clock.

## Registry and constant set

- **`Ix/BenchConstants.lean`** — the shared constant set: one
  `(name, env)` entry per benchmark constant, compiled into `ix`. Every
  backend with constant rows runs this same set: `Nat.add_comm`,
  `Array.extract_append`, `ByteArray.utf8DecodeChar?_utf8EncodeChar_append`
  and `Std.HashMap` in InitStd, and `Lean.Json` in ISLB. A constant whose
  run exceeds the host's RAM still runs; the row records the OOM.
- **The registry** (`envSpecs`/`backendSpecs` in `Ix/Cli/BenchCmd.lean`) —
  everything else: the envs (InitStd, ISLB, Mathlib) and their modules, and
  the backends (disabled reason, bencher testbed, the constant-row and
  env-row compare columns).
  Typed Lean data with one owner: the
  workflows never read it directly — `ix bench ci matrix` serves the job
  matrices and `ix bench ci parse` the `!benchmark` cells, both post-build.
  Runner provisioning lives in the workflows; `IX_BENCH_MACHINE`
  selects the matching Bencher testbed. Certified compilation can use
  substantially more RAM than the historical Rust compile series; the
  benchmark runners have 256 GiB, leaving about 240 GiB under
  `memory-cap`.

The other `Benchmarks/Compile` modules (e.g. `CompileLean`, `CompileFLT`,
`CompileAnthropicFLT`) remain for local use; `ix compile` builds them
directly, outside the registry.

## `!benchmark` grammar

```
!benchmark ([ixvm [execute|prove|compress]] [ixvm-ooc] [compile] [decompile] | all)
           [fresh] [KEY=VALUE …]
BENCH_CONSTANTS=all            # constant rows: all (default), none, or
                               # comma names; a shared constant runs in its
                               # own env, any other name needs a single-env
                               # BENCH_ENVS naming its env
BENCH_ENVS=InitStd,Mathlib     # env rows: all, none, or registry envs
                               # (case-insensitive; default InitStd)
RUST_LOG=info                  # passthrough env (allowlist:
                               # RUST_LOG, RUSTFLAGS, IX_COMPILE_DEMOTE)
```

The defaults apply only when neither key is set. Setting either one runs
exactly what it names, and the other selects nothing: `!benchmark ixvm
BENCH_CONSTANTS=Nat.add_comm` runs that constant without the InitStd env row,
and `!benchmark ixvm BENCH_ENVS=Mathlib` runs only the Mathlib env row.
`ixvm prove` and `ixvm compress` default to `Nat.add_comm` alone, since
proving the larger constants on CPU would outlast the 60-minute job timeout:
name other constants with `BENCH_CONSTANTS` to prove them.

`ixvm execute` measures execution, `ixvm prove` also proves and verifies each
constant, and `ixvm compress` additionally KZG-compresses and verifies the
root. Bare `ixvm` and `all` default to execution. A mode immediately follows
`ixvm`, so backends can be combined as `!benchmark ixvm compress ixvm-ooc`.
Prove and compress require constant rows; whole-env rows remain execution-only.

Add `fresh` to any request, for example `!benchmark ixvm compress fresh`, to
bypass Bencher baseline results and persistent benchmark-product caches.
Both revisions' binaries and `.ixe` files are built in this run, and every
measurement is rerun. A cached head `ix` may parse the command before the
measured binary is rebuilt. Cargo and package dependency caches remain
available; fresh results are passed between jobs as run-scoped artifacts.

### The PR comment

One comment per run. Its header line names the base and PR commits (linked),
the machine, where the base side came from (bencher at the base SHA, or a
base rerun), and the run's selection; the measuring hardware follows once,
both sides only when they differ. Then each backend's tables, one per row
kind: its env rows (`#### ixvm · envs`), then its constant rows (`#### ixvm ·
constants`), since the two kinds carry different measures (an env row has
`shards`, for one). In each table, every metric its rows carry
gets three columns, `<metric> (<base>)`,
`<metric> (PR)` and `Δ%`, with ⚠️ for a regression and 🟢 for an improvement past
±3%, and the change as a factor in the metric's terms (`1.07× slower`,
`1.20× larger`) once it reaches 1.05×. A run with
`ixvm prove` or `ixvm compress` names its stages in the header line
(`stages execute+prove+compress`) and adds one table per stage under the
constant table (`#### ixvm · prove`, `#### ixvm · compress`), with the
constant rows that ran it. `ix bench compare` renders a single cell with the
same tables.

```
## `!benchmark` — main [`1a2b3c4`](…) ← PR [`5d6e7f8`](…)

machine `r8i.8xlarge` · base: bencher @ 1a2b3c4 · backends `ixvm` · constants `all` · env rows `InitStd`

Hardware: CPU: `Intel Xeon 6975P-C` · vCPUs: `32` · RAM: `251.4 GiB`

### `ixvm`

_6 rows · 1 with regressions · 0 with improvements (|Δ| > 3.0% on any metric)._

#### `ixvm` · envs

| env | execute-time (main) | execute-time (PR) | Δ% | peak-ram (main) | peak-ram (PR) | Δ% | env-shards (main) | env-shards (PR) | Δ% |
|---|---|---|---|---|---|---|---|---|---|
| InitStd | 41.200 s | 43.900 s | +6.6% (1.07× slower) ⚠️ | 61.00 GiB | 61.20 GiB | +0.3% | 12 | 12 | +0.0% |

#### `ixvm` · constants

| constant | execute-time (main) | execute-time (PR) | Δ% | peak-ram (main) | peak-ram (PR) | Δ% |
|---|---|---|---|---|---|---|
| `Nat.add_comm` | 12.1 ms | 12.0 ms | -0.8% | 1.20 GiB | 1.20 GiB | +0.0% |
```

The `KEY=VALUE` config works both as lines below the command (the comment
form above) and inline on the command line, whitespace-separated — the
single-line form for `bench-pr.yml`'s manual workflow_dispatch, whose
input box can't hold newlines:
`!benchmark ixvm-ooc BENCH_ENVS=InitStd,Mathlib`.

The allowlisted `IX_COMPILE_DEMOTE` setting tunes the Rust compiler used by
older base checkouts; it does not tune the certified compiler. The `.ixe` and
compile-row caches are keyed by commit and env, so add `fresh` to remeasure
a compile setting on an already benchmarked commit.

Parsed by `ix bench ci parse` in the PR build job, right after the `ix`
binary exists — the registry lives in Lean, so nothing pre-build reads it. PR runs never upload to bencher, so the comparison
prints in the comment and the canonical baseline is untouched.

## CI shape

**bench-main.yml**: `build` (compile `ix` once, warm the compiled-program
cache, and cache both by SHA) → `plan` (`ix bench ci matrix` → job matrices) + `compile` (per env:
`ix bench run --backend compile`, cache the `.ixe`) →
one `benchmark` job per remaining cell — ixvm / ixvm-ooc / decompile, each
running all of the env's rows —
(each: restore caches, one `ix bench run … --ixe` under `memory-cap`,
`ix bench bmf`, upload via `.github/actions/bencher-track`). A kernel
rejection exits 3 and reddens the
run step while the clean rows still upload.

**Alerts**: none. Bencher uploads carry no regression thresholds, and
`bencher-track` passes `--thresholds-reset` so thresholds left from earlier
runs are removed. The PR comment still marks each Δ% past ±3% with ⚠️ or 🟢
(`ix bench compare --threshold`); that is display only.

**Dashboard plots**: `ix bench plots` pins one plot per (workload, measure)
to <https://bencher.dev/console/projects/ix/plots> — main-branch trend
lines on the current machine's native r8i testbed only, one line per
benchmark row, labelled with the constant or env name, plus the IxC
input-constants overlay over the `ixvm-ooc` constant rows. Each workload
is the current implementation's own series: `ix-compile-certified` (the
certified compiler), `ix-decompile-lean` (the Lean decompiler), `ixvm`
(formal IxVM execution) and `ixvm-ooc` (the IxC out-of-circuit check). No
plot draws a retired testbed (`ix-compile`, `ix-decompile`, `ooc-check`,
the legacy Aiur ones, or the historical Warp `<workload>-x64-32x`). Titles
name what is measured ("Certified Compile Time", "IxVM Execute Time",
"IxVM OOC (IxC) Check Time", …). Registry-derived like the job matrices (titles,
ordering, and skips live in `Ix/Cli/BenchPlots.lean`), so rerun the sync
after changing the registry or the constant set — either locally
(needs the bencher CLI and a user API key in `BENCHER_API_KEY`;
`--dry-run` previews) or via the `bencher-plots.yml` workflow_dispatch
(run it after bench-main has built the merged registry). Idempotent:
matching plots are kept, stale ones replaced, and every plot whose title
the registry no longer produces is deleted, so legacy plots go away on
the next sync.
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
base, whose `.ixe` can be restored from its earlier PR run), then publishes
the cell's rows and their sources as an artifact. `assemble` runs `ix bench
report` over every cell without write privileges, and `comment` replaces the initial comment. Only `announce`
and `comment` hold write tokens, and neither checks out or runs PR code. Runs
seed the run artifacts from persistent head/base-SHA caches when they hit.
`fresh` bypasses these caches and the Bencher baseline, rebuilding measured
products while retaining dependency caches.
An ixvm cell requesting prove or compress reruns its base measurements:
bench-main's execution-only results cannot supply those stages.
Every `ix bench run`, the base side's included, goes through the PR head's
`.github/scripts/memory-cap`.

**Compiled programs**: `ix check` loads the certified Aiur programs from
`IX_AIUR_CACHE`, which both workflows set to `<workspace>/.aiur-cache`. The
jobs that build `ix` fill it (`lake build ix`, then
`.github/scripts/warm-aiur-cache`, which runs `ix codegen --check --out` to
compile any program `lake build` skipped) and ship it beside the binaries:
bench-main as the `bench-aiur-<sha>` cache entry, bench-pr in the run's
`benchmark-binaries` artifact and the same cache entry for its head. The
compile and benchmark jobs restore it before `ix bench run`, so no measured
run compiles a program. The base side's programs join the same directory:
restored from the base SHA's `bench-aiur-<sha>` entry, compiled by a
from-source base build, or warmed with the base `ix`. Programs are keyed by
source and compiler, so both sides coexist. A base that predates the
in-process formal Aiur check fails its ixvm cells and reports no base
column.

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
include both, such as `ixvm-ooc-runs-on-r8i-8xlarge-native`, so old binaries
and timings from different hardware or compiler flags stay separate.
A hardware trial must change the runner labels, sticky cache lineages,
`IX_BENCH_MACHINE`, `BENCH_CACHE`, the Rust action's cache key, and the allowed
`benchmarkMachines` in `Ix/Cli/BenchCmd.lean` together.

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
