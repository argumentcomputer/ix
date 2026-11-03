# Why the small claim and recursive verifier behave differently

Measured 2026-10-28 against `1a19788b`. The source programs and grouped circuits
are unchanged; the only runtime addition is optional phase instrumentation,
compiled out unless `aiur/trace-profile` is enabled.

The [ROM reuse follow-up](formal-aiur-rom-reuse.md) implements the proposed
optimization and measures the before/after results. This report preserves the
original phase measurements.

## The remembered Nat.add_comm result is correct

The small frontier-assumption claim is different from checking its entire
self-contained 342-constant environment. A fresh sweep of the small claim,
with the ordinary uninstrumented binaries, gives:

| Threads | Legacy trace + lookups (ms) | New Aiur trace + lookups (ms) |
|---:|---:|---:|
| 1 | 12.03 | 19.80 |
| 8 | 12.34 | 4.99 |
| 32 | 13.39 | 4.43 |
| 64 | 15.56 | 5.20 |

These are five-sample medians after two warmups, using a reused execution
record, CPU affinity, native release builds and disabled transparent huge
pages as in the [scaling comparison](formal-aiur-trace-scaling.md).

The workloads contain very different amounts of work in new Aiur:

| Workload | Recorded function queries | Blake3 compression queries |
|---|---:|---:|
| Small `Nat.add_comm` frontier claim | 15,788 | 488 |
| Self-contained environment | 951,532 | 21,280 |
| Real recursive verifier | 11,297,616 | 993,400 |

Compression accounts for about 38% of the environment's padded main cells and
56% of the recursive verifier's. These are cell proportions, not CPU-time
attributions. Both large workloads use the same inputs as the previous reports.

## Measured preparation costs at 64 threads

Three measured traces follow two warmups. The profiler times the actual
production generation path; each invocation creates fresh matrices, lookup
buffers, ROM index and row metadata.

| New-Aiur phase | Small claim (ms) | Environment (ms) | Recursive verifier (ms) |
|---|---:|---:|---:|
| Validate record and root | 0.48 | 2.84 | 23.12 |
| Rebuild ROM payload → address index | 0.18 | 6.17 | 232.56 |
| Copy/check auxiliary multiplicities | 0.31 | 1.23 | 24.40 |
| Partition ROM entries by width | 0.13 | 5.47 | 125.74 |
| Populate circuits and host lookups | 4.31 | 33.34 | 777.29 |
| Cleanup | 0.01 | 0.01 | 11.57 |
| Total | 5.43 | 48.94 | 1,197.59 |

Shape checking is below 0.01 ms. The independently computed phase medians need
not sum exactly to the median total. Logging happens after the total is taken.
Per-circuit spans are also recorded, but overlap under Rayon's nested work
stealing; they must not be added or interpreted as isolated CPU time.

The two ROM reconstruction passes take **358 ms**, roughly **30%** of the
recursive trace. They occur before the parallel population phase, so adding
row workers does not accelerate them. Query validation was a plausible
suspect from code inspection, but its measured 23 ms is not the main issue.

The implementations explain why this work is redundant:

- New Aiur's `Memory` already has width buckets, local addresses and stored
  multiplicities. `Rom::partition` traverses all entries again, looks up their
  types and creates another collection of width buckets.
- `Machine` builds a payload interning `HashTable` during execution, but that
  table is not retained in `Execution`. The trace generator reconstructs a
  payload-to-address `FxHashMap` from the complete memory record.
- Legacy retains a `QueryMap` for each memory width and directly reads those
  maps while producing its ROM rows. It does not need these reconstruction
  passes. It also parallelizes ROM row population, whereas new Aiur currently
  writes each width's main rows sequentially.

The concrete next optimization is to consume the existing width buckets and
multiplicities directly, and retain or reuse execution's payload index. This
changes host data handling, not Aiur semantics or circuit constraints. Retaining
the index trades some post-execution memory for avoiding a second index during
trace generation; the effect on peak memory should be measured.

Removing those passes would not establish parity by itself: parallel
population still takes about 777 ms, compared with legacy's previous measured
631 ms for its entire recursive trace. This profile does not separate that
remaining gap into compression arithmetic, hint replay and lookup emission.

## Why small claims favor new Aiur on multiple cores

The small claim pays only about 0.3 ms for the two ROM passes. Its new-Aiur
population phase is instead dominated by the fixed byte-pair table's span
(about 4.1 ms at 64 threads).

Legacy's `Bytes2::witness_data` constructs lookup messages for all 65,536 byte
pairs with a sequential loop, including the argument computations for unused
operations. New Aiur's auxiliary lookup writer uses parallel batches and skips
argument writes for zero multiplicities. This is a concrete implementation
reason the small claim can favor new Aiur while a huge, compression-heavy
recursive trace does not. The legacy table's exact isolated wall time was not
measured in this profile.

## Saved data and reproduction

[Phase summary](benchmarks/formal-aiur-trace-profile/phase-summary.csv),
[raw phase/circuit spans](benchmarks/formal-aiur-trace-profile/phases.jsonl),
[small-claim scaling](benchmarks/formal-aiur-trace-profile/nat-frontier.csv),
[raw small-claim samples](benchmarks/formal-aiur-trace-profile/nat-frontier-runs.json)
and [manifest](benchmarks/formal-aiur-trace-profile/manifest.json) preserve the
measurements. The host reports 32 cores and 64 logical CPUs; the runs use the
same CPU and input configuration as the scaling report.

```sh
cargo build --release --locked -p stark-verifier \
  --features parallel,aiur/trace-profile --example compare
RAYON_NUM_THREADS=64 IX_BENCH_NO_THP=1 IX_BENCH_REUSE_EXECUTION=1 \
  AIUR_TRACE_ONLY_LOOKUPS=0 taskset -c 0-63 target/release/examples/compare \
  .lake/formal-integration/recursion-tuned.json \
  .lake/formal-comparison/final/new-environment-grouped.json.inner/input.json \
  /tmp/recursion-profile.json 3 2>/tmp/recursion-phases.jsonl
```

Each successful generation emits an `aiur_trace_profile` JSON event on stderr.
Discard the first two warmups. Build without `aiur/trace-profile` for ordinary
timings; no timers, synchronization or logging compile into that path.
The instrumented grouped trace/proof test and a real `Nat.add_comm` proof pass;
Clippy also passes with warnings denied.
