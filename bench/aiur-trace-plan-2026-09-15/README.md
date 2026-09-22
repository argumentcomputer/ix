# Static Aiur trace-plan validation

Validated the compiler foundation on 2026-09-15, using four Lean threads
restricted to CPUs 0–3 while the FLT build occupied the host. This measures
static planning and checks compiler behavior; it is not a GPU speedup benchmark.

This is the static-planner snapshot. Subsequent seed-packer and scalar-writer
implementation and validation are recorded in the
[2026-09-16 results](../aiur-trace-codegen-2026-09-16/README.md).

Base: `dcfa650564dc0d3193eda4719503771370eb7957`, plus the uncommitted
trace-plan implementation. Source hashes, exact commands and report hashes
are recorded in [metadata.json](metadata.json).

## Results

| Program | Library functions | Constrained functions planned | Function circuits | Groups | Primitive circuits |
| --- | ---: | ---: | ---: | ---: | ---: |
| IxVM | 798 | 757 | 185 | 82 | 20 |
| MultiStark | 296 | 223 | 105 | 20 | 13 |
| Aggregation | 313 | 240 | 88 | 21 | 13 |

All **1,220 constrained functions** passed the planner's operand, selector,
call/yield arity, per-branch reservation and whole-layout checks. Circuit
membership and merged widths also passed. These are planned functions;
CUDA writers have not been emitted.

- All **35 focused fixtures passed**, including nested early returns that
  bypass an enclosing continuation's read.
- Every changed Lean module, the test registry and `lakefile.lean` compiled.
- `codegen --check` reproduced all three checked-in Rust execution modules
  byte for byte. See [the output](rust-codegen-check.log).
- JSON inventory generation, including interpreter startup and source
  compilation, took 6.86 s for IxVM, 5.19 s for MultiStark and 4.75 s for
  aggregation. These are single observations under competing CPU load.

The four GPUs were visible and idle. No GPU kernel experiment was run:
this change implements the planner and inventory, with the generated packer,
scalar row oracle and CUDA emitter still pending.

## What the inventory says

The [function inventory](functions.csv) records all constrained functions,
their production groups, canonical seed sizes and static operation counts.
Ratios compare one real row with its full-width seed; they exclude padding,
repeated uploads and runtime row weights.

| IxVM function | Standalone row bytes | Production circuit row bytes | Canonical seed bytes | Standalone expansion | CPU seed arithmetic sites |
| --- | ---: | ---: | ---: | ---: | ---: |
| `blake3_compress` | 4,264 | 4,264 | 1,296 | 3.29× | 0 |
| `u64_mul` | 720 | 1,088 | 136 | 5.29× | 0 |
| `get_constant` | 1,120 | 1,392 | 728 | 1.54× | 0 |
| `verify_claim` | 80 | 80 | 72 | 1.11× | 0 |

The real BLAKE3 plan has 129 inputs, two selectors and 402 auxiliary
columns: **533 columns total**. It reserves 162 canonical seed words, with
one returned-call read. Normal preparation needs no arithmetic to form
that call's key. The guarded byte-size estimate is **176 bytes**, matching
the current handwritten provider's packed representation; its corresponding
expansion is 24.23×. The generic compact codec is not implemented yet.

`u64_mul` has 219 static operation sites, 98 needed by row generation, and
no external reads or CPU preparation arithmetic. Its seed contains only
the multiplicity and 16 inputs. This supports its position immediately
after BLAKE3 in the arithmetic coverage plan. Its six-member production
group adds unused columns to this member's rows, increasing the canonical
expansion to 8×; that extra expansion is padding within a group, not extra
arithmetic saved.

`get_constant` has nine external-read sites despite needing no arithmetic
for their keys. Those reads remain CPU work. `verify_claim` has almost no
expansion or arithmetic to remove. This illustrates why function count
alone cannot predict the benefit of full coverage.

All `guarded_u8_seed_bytes_estimate` values in the CSV are hypothetical
aligned sizes conditional on every payload value fitting in a byte.
Pointers and arbitrary fields may fail that guard. Multiplicity always
keeps eight bytes. Real row weights are deliberately blank: the older
Mathlib profiles predate the merged program and its circuit grouping.
There is no weighted wall-time or utilization prediction from this run.

## Reproduction

The experiment used the installed Lean 4.33.1 compiler, cached unchanged
dependencies from the original checkout, and private output artifacts.
No Lake or Cargo build was launched, and the original checkout's artifacts
were not modified. The private artifact directory and exact runner commands
are in `metadata.json`; full JSON reports remain there alongside stderr and
timing records.

For a configured checkout with the changed modules built, [Run.lean](Run.lean)
provides a small entry point that calls the same CLI handler and focused tests:

```sh
taskset -c 0-3 env LEAN_NUM_THREADS=4 RAYON_NUM_THREADS=4 CARGO_BUILD_JOBS=4 \
  lake env lean -j4 --run bench/aiur-trace-plan-2026-09-15/Run.lean test

taskset -c 0-3 env LEAN_NUM_THREADS=4 RAYON_NUM_THREADS=4 CARGO_BUILD_JOBS=4 \
  lake env lean -j4 --run bench/aiur-trace-plan-2026-09-15/Run.lean \
  --trace-report --target ixvm > /tmp/ixvm-trace-plan.json

taskset -c 0-3 env LEAN_NUM_THREADS=4 RAYON_NUM_THREADS=4 CARGO_BUILD_JOBS=4 \
  lake env lean -j4 --run bench/aiur-trace-plan-2026-09-15/Run.lean --check
```

Repeat the report command with `multi-stark` and `ix-aggr` for the other
programs. Report mode explicitly applies production grouping, independent
of `IX_NO_FUNCTION_GROUPS`. A rebuilt `ix codegen` accepts the same report
and check flags.
