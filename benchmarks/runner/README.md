# Benchmark runner

An optional Lake package that measures the [benchmark fixtures](../fixtures/README.md).
It is not a dependency of the compiler library or of the root flake's
checks. The [benchmark design](../../docs/benchmark-plan.md) defines the
rules it implements.

## Rows

| Row | Build |
| --- | --- |
| `lean-clang` | The fixture's Lean source through `lean -c` and Lean's `leanc -O3 -DNDEBUG` (bundled clang and Lean runtime) |
| `clang-O2`, `clang-O3` | The fixture's natural C or C++ twin at `-O2` and `-O3` |

Compilatrix rows join when the rebuilt pipeline compiles the fixtures.

## Commands

Run from this directory, with Lean 4.34.0 (`lean`, `leanc`) and `clang` /
`clang++` on `PATH` (for example inside `nix develop ../..`). `OUT` should be
an absolute path, conventionally under `plans/`:

```sh
lake build
./.lake/build/bin/runner build OUT     # every row of every fixture, once
./.lake/build/bin/runner check OUT     # every binary prints expected.txt at test arguments
taskset -c 5 ./.lake/build/bin/runner measure --cpu 2 --blocks 10 OUT
./.lake/build/bin/runner report OUT    # OUT/report.md and OUT/report.json
```

`measure` pins each worker process to `--cpu`; on the development machine,
CPUs 0–3 are full Zen 5 cores. It runs one untimed warm-up per row, then
`--blocks` blocks. Each block runs every row once in a shuffled order at the
benchmark arguments, and fails if the rows' outputs differ. Timing is
whole-process wall time and includes startup.

`report` gives, per fixture:
- the median time per row;
- the ratio of each row to `lean-clang`, with a 95% percentile-bootstrap
  interval over paired blocks.

Per rung, it gives the geometric mean of those ratios. `samples.json`
records the host (CPU model, worker core and its maximum frequency,
governor, boost, load, kernel).

Local results guide development only. They set no thresholds and are not
reference results.
