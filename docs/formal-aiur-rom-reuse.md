# Reusing the execution record's ROM index and width buckets

Measured 2026-10-28 against `55022874`, following the
[trace phase profile](formal-aiur-trace-profile.md). The optimization removes
the two ROM reconstruction passes identified there. Aiur programs, certified
layouts, grouping, constraints, circuit heights, columns and FFT estimates
are unchanged.

## Trace results

Times include main matrices and host lookup buffers. These are medians of five
samples after two warmups, with one reused execution record; the single-thread
control uses seven samples. Both versions use native-CPU release bytecode builds.

| Workload | Threads | Before | After | Change |
|---|---:|---:|---:|---:|
| Real recursive verifier | 64 | 1,179.04 ms | 815.87 ms | -30.8% |
| Real recursive verifier | 8 | 3,746.71 ms | 3,346.34 ms | -10.7% |
| Self-contained 342-constant environment | 64 | 46.27 ms | 37.52 ms | -18.9% |
| Small `Nat.add_comm` frontier claim | 8 | 4.85 ms | 4.25 ms | -12.4% |
| Environment, single-thread control | 1 | 1,045.23 ms | 1,035.87 ms | -0.9% |

Small-claim and single-thread sample ranges overlap; their small differences
are not evidence of a reliable speedup. The recursive improvement is clear:
at 64 threads, the before samples range from 1.156 to 1.201 seconds and the
after samples from 0.775 to 0.835 seconds.

A separate instrumented run confirms the preparation passes are gone:

| Recursive phase at 64 threads | Before profile | After profile |
|---|---:|---:|
| Validate record and root | 23.12 ms | 23.02 ms |
| Rebuild ROM payload index | 232.56 ms | removed |
| Check/copy auxiliary counts | 24.40 ms | 8.88 ms |
| Repartition ROM rows | 125.74 ms | removed |
| Populate circuits and lookups | 777.29 ms | 781.55 ms |
| Cleanup | 11.57 ms | below 0.01 ms |

The before profile is from the preceding report; the after profile uses three
samples after two warmups. Population is approximately unchanged: the win
comes from removing preparation work. Circuit spans overlap under Rayon and
must not be interpreted as isolated CPU time.

A fresh legacy recursive run takes **687.25 ms** at 64 threads. New Aiur is now
**18.7% slower**, down from **71.6% slower** before this change. Legacy's
environment median is 43.63 ms; that smaller workload has substantial sample
variation, saved in the raw data. This change does not establish recursive
parity: row and lookup population remain the main work to investigate.

Peak process RSS for the 64-thread recursive replay falls from **31.63 GiB to
31.33 GiB**, about **299 MiB less**. Retaining the index extends its lifetime
after execution, but avoids allocating the temporary trace index and ROM row
collections. The RSS measurement includes the entire process and allocator
behavior, not just the record's size.

## Execution controls

These runs reexecute the bytecode on every iteration, with two warmups and
three measured recursive samples or seven environment samples. The before
control runs immediately before its after counterpart. Execution is sequential
even though the trace uses the specified Rayon pool.

| Workload | Trace threads | Execute before | Execute after | Change |
|---|---:|---:|---:|---:|
| Real recursive verifier | 64 | 7.977 s | 7.893 s | -1.0% |
| Environment | 8 | 336.54 ms | 350.29 ms | +4.1% |

There is still a small execution cost on the environment in this control;
this is a trace optimization, not a claim of universally faster execution.
The environment's trace in these same runs falls from 168.69 to 149.08 ms.
The final single-thread trace control is approximately unchanged.
The median of each sample's execution plus trace falls from 9.173 to 8.719 s
for recursion and from 506.62 to 499.05 ms for the environment.

An initial implementation accidentally outlined the extracted memory lookup
in both the interpreter and trace writer. The final version explicitly inlines
it, as the query-table lookup already does. It also compares the cached full
hash before accessing a candidate payload, while still requiring exact field
value equality. No hash is treated as a proof of equality.

## Implementation and invariants

- `Memory` owns the existing interning `HashTable` instead of `Machine`
  discarding it when execution returns. Entries contain cached hashes and
  stable record indices; no second payload copy or self-referential pointers
  are introduced. The index clones with the record and is not serialized.
- The private `intern` insertion path maintains uniqueness and consecutive
  width-local addresses. Execution and trace stores use the same field-value
  equality/hash contract, including equal noncanonical native representations.
- ROM witnesses read the existing width buckets, payloads and multiplicities
  directly. The copied memory-count array and `Rom::partition` are removed.
  The existing type, root, query and multiplicity checks still run.
- The optimized generic and STARK trace writers use the retained store index.
  The reference writer deliberately reconstructs its own map for differential
  testing. ROM main rows are still written sequentially within each width;
  this change does not add another parallel population algorithm.

## Correctness checks

All 82 Aiur tests pass both with serial STARK generation and with parallel,
instrumented generation. The added regression exercises retained indices
through growth and cloning, equal-width nominal aliases, zero-width payloads
and payloads that differ only by trailing zeros. ROM tests reconstruct rows
independently from the flat record, including counts and padding. Existing
tests cover native-field equality, reference population, grouped proofs,
sharding, invalid multiplicities and forged ROM providers.

The real `Nat.add_comm` frontier proof verifies and is **byte-identical** to
the baseline proof (5,478,175 bytes). A full outer proof of the real recursive
workload also verifies (3,168,863 bytes). Proof hashes are in the manifest.
These checks exercise the Rust implementation; no Lean definition, theorem,
certificate or exported circuit was changed. Formatting and Clippy pass,
including the default library build and profiled comparison build.

## Data and reproduction

[Summary](benchmarks/formal-aiur-rom-reuse/summary.csv),
[raw samples](benchmarks/formal-aiur-rom-reuse/runs.json),
[circuit shapes](benchmarks/formal-aiur-rom-reuse/circuits.json), and
[manifest](benchmarks/formal-aiur-rom-reuse/manifest.json) include both binaries'
hashes, source and input hashes, memory measurements and all selected controls.
[Phase medians](benchmarks/formal-aiur-rom-reuse/phase-summary.csv) and
[raw phase/circuit spans](benchmarks/formal-aiur-rom-reuse/phases.jsonl) preserve
the separate instrumented run.
All new-Aiur circuit statistics match before/after for each workload, including
the recursive verifier's 937,960,213 padded main cells.

The host and inputs are the same as the
[scaling report](formal-aiur-trace-scaling.md): 32 cores / 64 logical CPUs,
native CPU code generation for the Rust interpreter, no Aiur program codegen,
fixed affinity, and disabled transparent huge pages. Benchmark processes run
sequentially. Preparation and execution are outside the reused-record trace
timer; every trace call allocates and populates a fresh witness.

```sh
cargo build --release --locked -p stark-verifier \
  --features parallel --example compare
RAYON_NUM_THREADS=64 IX_BENCH_NO_THP=1 IX_BENCH_REUSE_EXECUTION=1 \
  AIUR_TRACE_ONLY_LOOKUPS=0 taskset -c 0-63 target/release/examples/compare \
  .lake/formal-integration/recursion-tuned.json \
  .lake/formal-comparison/final/new-environment-grouped.json.inner/input.json \
  /tmp/recursion-rom-reuse.json 5
```

Use `IX_BENCH_REUSE_EXECUTION=0` for the execution controls. The baseline binary
was built from `55022874` with the same features and flags. Legacy uses
`bench-compare-aiur recursion INPUT OUTPUT SAMPLES` under the same environment.
