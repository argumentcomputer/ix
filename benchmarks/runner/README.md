# Benchmark runner

An optional Lake package that measures the [benchmark fixtures](../fixtures/README.md).
It is not a dependency of the compiler library or of the root flake's
checks; it needs no comparison toolchain beyond Lean and Clang. The
[benchmark design](../../docs/benchmark-plan.md) defines the rules it
implements.

## Rows

| Row | Build |
| --- | --- |
| `compilatrix` | The fixture's frozen Ixon closure (`fixtures/ixon-v3/bench-k1/<name>.ixe`, the closure of the same `entry`) through `compilatrix compile … --no-typecheck`, linked with the timing driver |
| `lean-clang` | The fixture's Lean source through `lean -c` and Lean's `leanc -O3 -DNDEBUG` (bundled clang and Lean runtime) |
| `clang-O2`, `clang-O3` | The fixture's natural C or C++ twin at `-O2` and `-O3` |
| `clang-tagged` | Diagnostic, entry profile only: the K1 algorithms on compilatrix's value representation (tagged words, carry-checked `+ 1`; [`../meas4/twins.c`](../meas4/twins.c) and [`entry/tagged.c`](entry/tagged.c)) at `-O2` |
| `lir-kernel` | Diagnostic, entry profile only: MEAS-4's hand-written Lir kernels (fib, sum-loop, gcd) through the current backend, from `backend-probe` |
| `compilatrix@NAME` | Diagnostic, entry profile only (`build --variant NAME=DIR`): objects `DIR/<fixture>.o` with the compilatrix row's interface (`cx_init`, `cx_entry`), such as another commit's compiler output (an A/B pair) or a hand-edited what-if; reports then add a ratio to `compilatrix` |

The `compilatrix` row exists where a frozen closure exists (the nine K1
fixtures: the original five and the MT.2 corpus four). A compiler decline or rejection is recorded in `build.json` with
its `stage: code: message`, and the row is left out. Diagnostic rows
attribute a gap; they are never real-program results.

## Profiles

- **Process** (`OUT/bin/<row>/<fixture>`): the fixture's own program, one
  run per process, whole-process wall time (startup included). The
  `compilatrix` binary is the driver built with `-DPROCESS`: it maps the
  region, calls `cx_init` and the entry once, and prints the result.
- **Entry** (`OUT/entry/<row>/<fixture>`): [`entry/driver.c`](entry/driver.c)
  with the row's adapter (`entry/row_<row>.c`) and code. One process
  initialises the row once (Lean's runtime; the compilatrix region and
  `cx_init`), makes `warmup` untimed calls and times `reps` calls of `entry`
  in one interval, so `tak` and `gcd` are no longer startup-dominated. The
  compilatrix adapter calls the root's SysV wrapper directly, so its
  argument checks, tagging and callee-saved saves are part of every call. The
  entry profile covers fixtures whose `entry` is `Nat → … → Nat`
  (the K1 rung). All its C (driver, adapters, twins) is compiled with `cc`
  and the same flags, without the nixpkgs wrapper's hardening and with frame
  pointers omitted (`build.json` records them).

## Commands

Run from this directory with Lean 4.34.0 (`lean`, `leanc`), `clang`/`clang++`,
`cc` and `objdump` on `PATH` (for example inside `nix develop ../..`), and
with the compiler built (`lake build compilatrix` at the repository root, or
pass `--compilatrix "nix run ../..#compilatrix --"`). `OUT` should be an
absolute path, conventionally under `plans/`.

```sh
lake build
./.lake/build/bin/runner build OUT --fixtures fib,sum-loop,ackermann,tak,gcd \
    [--compilatrix CMD] [--closures DIR] [--probe ../../.lake/build/bin/backend-probe] \
    [--variant base=DIR_A,next=DIR_B]
./.lake/build/bin/runner check OUT          # every binary against expected.txt and bench_expected
taskset -c 5 ./.lake/build/bin/runner calibrate OUT --cpu 2              # entry reps per row
taskset -c 5 ./.lake/build/bin/runner measure OUT --profile entry --cpu 2 --blocks 30 [--gate 1]
taskset -c 5 ./.lake/build/bin/runner measure OUT --profile process --cpu 2 --blocks 10
taskset -c 5 ./.lake/build/bin/runner perf OUT --cpu 2 [--perf PATH] [--runs 3] [--gate 1]
./.lake/build/bin/runner report OUT         # report.md and entry-report.md (with .json)
```

`build` also writes each row's disassembly (`OUT/asm/<row>/<fixture>.txt`),
compilatrix's IR at every level (`OUT/compilatrix/<fixture>.ir.txt`) and
`--stats` lines, and Lean's final IR (`OUT/ir/lean-clang/<fixture>.txt`), for
comparing IR against IR. `--probe` builds the `lir-kernel` row from
`backend-probe`'s objects (`lake build backend-probe` at the root).

`measure` pins each worker process to `--cpu`; on the development machine,
CPUs 0–3 are full Zen 5 cores (SMT siblings 12–15). It runs one untimed
warm-up process per row, then `--blocks` blocks. Each block runs every row
once in a shuffled order, a fresh process each, and fails if a row's result
differs (process profile: the rows' outputs; entry profile:
`bench_expected`). `calibrate` chooses `reps` per row and fixture in a pilot
so that a timed chunk lasts about `--target-ms` (default 250), and `warmup` as
a tenth of it. `calibrate`, `measure` and `perf` take `--rows` (names, or a
prefix ending in `*`, such as `compilatrix,compilatrix@*` for an A/B session).

On a shared machine, `--gate MAXBUSY` makes the entry profile's blocks
quiet: the runner reads per-CPU busy time from `/proc/stat` over each block,
and a block counts only if the worker's SMT siblings were at most 10% busy
and at most MAXBUSY other CPUs (not the controller's) were over half busy.
Before a block it waits for a quiet second (`--gate-wait`, default 1800 s); a
disturbed block is kept in the samples as invalid, with its reason, and run
again (`--gate-attempts`, default 5; the last attempt is accepted and
flagged). The report counts the disturbed attempts and the time spent
waiting. The gate measures busy time, not the package's power budget: busy
neighbours still lower the worker's clock, which paired ratios cancel and
absolute times do not. While builds run for hours the gate cannot be
satisfied; measure without it and label the result disturbed.

`perf` counts user-space instructions, cycles, branches and
branch misses per call (a run with `reps` calls minus a run with none, the
median of `--runs` pairs); an unavailable counter is recorded as unavailable.

`report` gives, per fixture and profile:
- the median time per row (entry: per call);
- the ratio of each row to `lean-clang` (entry: also to `clang-O2`,
  `clang-O3` and `clang-tagged`), paired per block, with a 95%
  percentile-bootstrap interval;
- in the entry profile, the counters and the bytes allocated per call where
  the row reports them.

Per rung it gives the geometric mean of those ratios; the entry report adds
a hierarchical-bootstrap interval, the largest per-fixture ratio and the
mean without it. `samples.json` and `entry-samples.json` record the host (CPU
model, worker core, its SMT siblings, maximum and current frequency,
governor, energy preference, platform profile, whether mains power is
online, boost, load at the start and end, kernel) and the load average per
block.

Code placement matters at this scale: in the first K1 session, moving the
unchanged compiled object by 8–56 bytes changed `ackermann` by up to 16% and
`tak` by up to 18%. An A/B or what-if comparison should compare the two
objects at several placements (for example a variant per start offset,
`.p2align 6` plus `.skip N`) and report the spread, not one link.

Local results guide development only. They set no thresholds and are not
reference results.
