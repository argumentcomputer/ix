# CPU scaling of trace generation

Measured 2026-10-28 against `5de73a23`, with the tuned new-Aiur grouping and
legacy's existing grouping. The previous grouping comparison used eight Rayon
threads. It was not a scaling comparison.

**New Aiur scales better on the IxVM environment, but legacy scales better on
the real recursive verifier.** Legacy remains faster in absolute trace time
on both workloads at every measured thread count.

## Measurements

All times include main trace generation and host lookup buffers. Each value is
the median of three samples after two warmups. Execution is bytecode on both
backends and is excluded from these timings.

| Threads | IxVM legacy (ms) | IxVM new (ms) | Recursive legacy (s) | Recursive new (s) |
|---:|---:|---:|---:|---:|
| 1 | 571.59 | 1,063.62 | 16.716 | 25.714 |
| 8 | 82.46 | 159.23 | 2.173 | 3.678 |
| 32 | 46.86 | 56.87 | 0.690 | 1.430 |
| 64 | 42.94 | 50.51 | 0.631 | 1.220 |

From one to 64 threads:

- IxVM: **21.1×** speedup for new Aiur, **13.3×** for legacy. Between eight
  and 64 threads, new Aiur's time gap shrinks from 93% to 18%.
- Recursive verifier: **21.1×** for new Aiur, **26.5×** for legacy. New Aiur
  is still about 1.93 times legacy's elapsed time at 64 threads.

The host is a KVM machine reporting an Intel Xeon 6975P-C, 32 cores, 64 logical
CPUs and one NUMA node. At up to 32 threads, each worker has a distinct reported
core available; the 64-thread run also uses the SMT siblings. This measures
32 cores with SMT, not 64 physical cores. The session and parent cgroups have
no CPU quota. Processes run sequentially and are pinned to the selected CPUs.

## Effect of the grouping change at 64 threads

The earlier 6–8% trace regression referred to the tuned grouping versus the
previous **new-Aiur grouping**, at eight threads. A separate 64-thread check
using the same new interpreter and trace generator gives:

| Workload | Previous grouping | Tuned grouping | Change |
|---|---:|---:|---:|
| IxVM environment | 46.13 ms | 50.51 ms | +9.5% |
| Real recursive verifier | 1.176 s | 1.220 s | +3.8% |

The grouping change's smaller matrices and FFT estimates therefore do not
remove its trace-time tradeoff at higher thread counts. These are three-sample
medians, not precise regression estimates; in particular the recursive
before/after sample ranges overlap. Raw minima, maxima and samples are saved.

## Interpretation

Both implementations parallelize across circuits and within function circuits.
New Aiur's row iterator uses batches of 32 with worker-local scratch storage.
Legacy's iterator items are individual rows; Rayon also splits and batches
those items internally. Parallel row population is not unique to new Aiur.

New Aiur still has serial preparation work, including the ROM payload index,
auxiliary count accumulation and ROM partitioning. Query validation runs in
parallel across functions but scans each function's rows sequentially. ROM
main rows are populated sequentially within each width, whereas legacy also
parallelizes those rows. These are possible scaling limits visible in the
implementation; this benchmark does not attribute the remaining recursive
runtime to individual phases.

Better speedup does not establish lower absolute cost: new Aiur starts with
more single-threaded work on both workloads. The IxVM result shows why the
eight-thread comparison should not be extrapolated to larger machines, while
the recursive result shows why the scaling advantage is workload-dependent.

## Method, data and reproduction

The workloads are the same self-contained 342-constant IxVM environment and
the same real 7,232,210-byte inner proof as the earlier comparisons. Artifacts,
inputs and binaries are hashed in the
[manifest](benchmarks/formal-aiur-trace-scaling/manifest.json). The
[summary CSV](benchmarks/formal-aiur-trace-scaling/summary.csv) and
[raw samples](benchmarks/formal-aiur-trace-scaling/runs.json) include every run.
Circuit heights, widths and cell counts were checked to be independent of the
thread count for each backend/workload.

Both binaries use release optimization, `-Ctarget-cpu=native`, the parallel
feature and `IX_BENCH_NO_THP=1`. The sweep uses thread counts in the order
8, 64, 1, 32 and alternates the backend order. Larger legacy-thread samples
have some variability; the saved ranges expose it rather than treating the
medians as exact constants. No proving or GPU timing is included.

The benchmark harnesses now accept `IX_BENCH_REUSE_EXECUTION=1`: execute once,
retain the immutable query record (and legacy IO buffer), and regenerate the
complete witness on every iteration. No trace matrices, lookup buffers, row
indices or count preparation are cached between trace samples. The initial
execution time is reported separately; repeated execution samples are `null`.
The default benchmark behavior still executes before every trace sample.
Smoke proofs on both backends verify after repeated trace generation and have
the same circuit shapes as ordinary execution. The interpreter, trace
generation implementations and grouping policies were not changed for this
experiment.

With the existing exported artifacts and inputs:

```sh
lake build bench-compare-aiur
cargo build --release --locked -p stark-verifier --features parallel --example compare
python3 tools/ixvm/trace-scaling.py .lake/trace-scaling/sweep \
  --ixvm-artifact .lake/formal-integration/ixvm-tuned.json \
  --recursion-artifact .lake/formal-integration/recursion-tuned.json
```

Use `--inputs`, `--threads` and `--samples` to select another saved comparison
directory, CPU counts or sample count. The manifest records every invocation,
including the two additional runs with the previous grouping artifacts.
