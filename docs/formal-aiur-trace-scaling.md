# CPU scaling of trace generation

Historical record: measured 2026-10-28 against `5de73a23`, with the tuned
grouping from the [grouping tuning](formal-aiur-grouping-tuning.md). That
earlier measurement used eight Rayon threads only.

The [phase-profile follow-up](formal-aiur-trace-profile.md) also measures the
small `Nat.add_comm` frontier claim and identifies substantial ROM preparation
costs in the recursive trace. The subsequent
[ROM reuse optimization](formal-aiur-rom-reuse.md) removes those passes; the
timings and implementation discussion below describe the baseline.

## Measurements

All times include main trace generation and host lookup buffers. Each value is
the median of three samples after two warmups. Execution is bytecode and is
excluded from these timings.

| Threads | IxVM environment (ms) | Recursive verifier (s) |
|---:|---:|---:|
| 1 | 1,063.62 | 25.714 |
| 8 | 159.23 | 3.678 |
| 32 | 56.87 | 1.430 |
| 64 | 50.51 | 1.220 |

From one to 64 threads, both workloads speed up **21.1×**. Going from 32 to 64
threads (adding SMT siblings) gains 11% on IxVM and 15% on the recursive
verifier.

The host is a KVM machine reporting an Intel Xeon 6975P-C, 32 cores, 64 logical
CPUs and one NUMA node. At up to 32 threads, each worker has a distinct reported
core available; the 64-thread run also uses the SMT siblings. This measures
32 cores with SMT, not 64 physical cores. The session and parent cgroups have
no CPU quota. Processes run sequentially and are pinned to the selected CPUs.

## Effect of the grouping change at 64 threads

The tuning report's 6–8% trace regression referred to the tuned grouping versus
the previous grouping, at eight threads. A separate 64-thread check using the
same interpreter and trace generator gives:

| Workload | Previous grouping | Tuned grouping | Change |
|---|---:|---:|---:|
| IxVM environment | 46.13 ms | 50.51 ms | +9.5% |
| Real recursive verifier | 1.176 s | 1.220 s | +3.8% |

The grouping change's smaller matrices and FFT estimates therefore do not
remove its trace-time tradeoff at higher thread counts. These are three-sample
medians, not precise regression estimates; in particular the recursive
before/after sample ranges overlap. Raw minima, maxima and samples are saved.

## Interpretation

Trace generation parallelizes across circuits and within function circuits.
The row iterator uses batches of 32 with worker-local scratch storage.

At `5de73a23` the trace generator still had serial preparation work, including
the ROM payload index, memory multiplicity copying and ROM partitioning. Query
validation runs in parallel across functions but scans each function's rows
sequentially. ROM main rows are populated sequentially within each width.
These are possible scaling limits visible in the implementation; this benchmark
does not attribute the recursive runtime to individual phases.

The eight-thread grouping measurements should not be extrapolated to larger
machines: IxVM's trace time falls by a further 3.2× from 8 to 64 threads.

## Method and data

The workloads are the same self-contained 342-constant IxVM environment and
the same real 7,232,210-byte inner proof as the earlier measurements.
Artifacts, inputs and binaries are hashed in the
[manifest](benchmarks/formal-aiur-trace-scaling/manifest.json). The
[summary CSV](benchmarks/formal-aiur-trace-scaling/summary.csv) and
[raw samples](benchmarks/formal-aiur-trace-scaling/runs.json) include every run.
Circuit heights,
widths and cell counts were checked to be independent of the thread count for
each workload.

The binary uses release optimization, `-Ctarget-cpu=native`, the parallel
feature and `IX_BENCH_NO_THP=1`. The sweep uses thread counts in the order
8, 64, 1, 32. The saved ranges expose sample variability rather than treating
the medians as exact constants. No proving or GPU timing is included.

The `compare` example accepts `IX_BENCH_REUSE_EXECUTION=1`: execute once,
retain the immutable query record, and regenerate the complete witness on every
iteration. No trace matrices, lookup buffers, row indices or count preparation
are cached between trace samples. The initial execution time is reported
separately; repeated execution samples are `null`. Without it the benchmark
executes before every trace sample. Smoke proofs verify after repeated trace
generation and have the same circuit shapes as ordinary execution.

One point of the sweep, for the recursive verifier at 64 threads:

```sh
cargo build --release --locked -p stark-verifier --features parallel --example compare
RAYON_NUM_THREADS=64 IX_BENCH_NO_THP=1 IX_BENCH_REUSE_EXECUTION=1 \
  AIUR_TRACE_ONLY_LOOKUPS=0 taskset -c 0-63 target/release/examples/compare \
  .lake/formal-integration/recursion-tuned.json \
  .lake/formal-comparison/final/new-environment-grouped.json.inner/input.json \
  /tmp/recursion-scaling.json 3
```

The two `.lake` paths are locally exported artifacts and inputs, not checked-in
files. The manifest records every invocation of the original sweep, including
the two additional runs with the previous grouping artifacts.
