# Shared execution and record-memory budget: Init validation

The `--lanes` driver has one CPU execution pool, one bounded queue of
prepared records, and one resident prover per GPU. Ready joins have
priority in both queues. Each record owns its memory charge through
proving. Executions wait for growth; mutual blocking cancels and requeues
the youngest waiting execution so one can finish.

## Validation

- Eight focused record-pool and allocation tests pass: retained storage
  ownership, cross-thread release, growth waiting, persistent priority,
  mutual blocking, whole-pool overflow, shutdown, recursive returns and
  BigUint insertion.
- Four queue and host-budget tests pass, including closing full/empty
  queues and respecting ancestor cgroup limits.
- A prepared record created with GPU 0's system was proved and verified
  on GPU 1. Its reservation remained charged through transfer and was
  released after proving. Planning accepted it independently of the old
  per-record host ceiling.
- A workspace regression check confirms that shape-only lookup metadata
  does not reserve the full host lookup payload.
- CUDA-enabled Rust integration check and the release CLI build pass.
  `ix codegen --check` confirms all three generated kernels match the Lean
  emitter. Cargo dependency versions remain unchanged; the build uses
  the existing local multi-stark changes through a temporary path override.

The full CLI build uses all 96 available cores. Runtime execution retains
`--exec-jobs 3` per GPU, giving twelve shared execution slots and four
prepared queue slots. The global Rayon pool can use all 96 cores.

## Init runs

**Both cuts verified their root and composed verdict from fresh caches.**
The automatic seed selected five claims. One four-claim follow-up used
**2.95% less wall time, 6.25% less CPU time and 8.02% less peak RSS**.

| Measurement | Automatic: 5 claims, 4 joins | Follow-up: 4 claims, 3 joins |
| --- | ---: | ---: |
| Prove-command wall time | 351.72 s | 341.35 s |
| Process CPU time | 4171.73 s | 3911.15 s |
| Peak RSS | 178.85 GiB | 164.50 GiB |
| Maximum sampled VRAM/device | 65.21 GiB | 65.32 GiB |
| Claim record mean / maximum | 17.71 / 19.58 GiB | 21.28 / 22.48 GiB |
| Last claim proved | +180 s | +186 s |
| Root dispatched | +265 s | +250 s |
| Tail after last claim | 169 s | 153 s |
| Growth waits / contention retries | 0 / 0 | 0 / 0 |
| LDE spills | Unavailable | 0 |

Wall time includes CLI setup and final verification, excluding partitioning
and the build. Internal event timestamps start at scheduler entry. Each
run used all four GPUs and completed three root wraps down to one trace
shard. The four-claim log confirms 90 commitments using generated traces.
Total planned trace shards, including joins and wraps, fell from 78 to 72.
See the [comparison](results/comparison.json),
[automatic run](results/automatic-corrected/result.json),
[four-claim run](results/four/result.json), and per-task timing
([five](results/automatic-corrected/tasks.csv), [four](results/four/tasks.csv)).

This is one trial per count; the small wall-time difference is provisional.
Both runs use the same binary and input. The four-claim run additionally
enables the debug module that reports generated commitments and LDE spills.
The earlier eight-claim GPU-trace comparison used a different scheduler,
execution concurrency and host cap. These runs do not isolate the shared
scheduler's speedup against that implementation.

The test uses automatic shard selection with
`--max-ram 230 --exec-jobs 3`, four GPUs,
GPU BLAKE3 trace generation, and the frozen Init input from
`target/tree-cache-bench/fixture/init.ixe`.

The preliminary run was stopped after its plans exposed an overestimate:
full host lookup payloads were charged even with
`AIUR_TRACE_ONLY_LOOKUPS=1`. It produced 31–35 trace shards per claim at
375 million cells. The corrected model omits those unallocated buffers;
a regression test covers both materialized and shape-only lookup modes.
The aborted run is retained under `target/shared-execution-init/automatic/`
and is not a completed performance measurement.

With the correction, the same five-shard manifest uses **8–10 trace
shards per claim at 1.5 billion cells**. The workspace correction preserves
the partition and proving settings. The initial runner's
logging filter did not enable the module that reports LDE spills, so its
spill count is recorded as unavailable. The follow-up enables that module
and also counts commitments using generated traces.

At these settings the process has a 920 GiB cgroup limit, 730.8 GiB record
capacity, 24.2 GiB workspace reserved per GPU, and 92 GiB headroom. Initial
admission credit is 36.5 GiB per execution; records may grow beyond it.

The five-claim result motivated the four-claim follow-up: one claim waited
26 seconds for a GPU, and the aggregation tree required three join levels.
Four claims fit one GPU wave and need two join levels. The larger claims
finished six seconds later overall, but removing a join let the root start
15 seconds sooner. Four is the fastest count tested in this pair; this is
not an optimum search. The longer CPU phase and serial aggregation tail
keep mean sampled GPU utilization low (14.6% for five, 13.5% for four).

The automatic seed remains the existing static-score heuristic. Its
printed 41.4 GiB calibration share is distinct from the shared driver's
36.5 GiB admission credit and is not an enforced record limit. The runtime
reports a p90-scaled candidate after measuring claim records; the
five-claim run suggests three by memory alone, below the four-GPU count.
That illustrates why memory sizing alone cannot choose the fastest cut.

The automatic formula is:

```text
seed_share_bytes = (RAM_per_GPU_bytes - 16 * trace_cells - 256 MiB) / (exec_jobs + 2)
seed_share_GiB   = seed_share_bytes converted to GiB, truncated to one decimal
shards          = round(128 * environment_score / 1.271e14 * 35.8 / seed_share_GiB)
```

The count is clamped between one and the number of atomic blocks. The
score sums size-based work estimates over blocks. The 128 shards and
35.8 GiB maximum come from the older Mathlib calibration. For this Init
input the score is `6.106e12`, giving about `5.32`, rounded to five.
`--parallelism 4` affects the profiled strategy and does not enter this
static seed. The new post-run diagnostic is
`ceil(measured_count * claim_p90 / initial_admission_credit)`; it does not
repartition automatically. The four-claim comparison uses `--shards 4`.

Init's records do not exhaust this machine's pool. The focused tests
exercise growth waits, mutual blocking, cancellation/requeue signaling
and release; this end-to-end run validates normal ownership transfer,
cross-device assignment, joins, root wrapping and proof verification.
Coarser Mathlib performance remains unmeasured on this implementation.

## Reproduce and inspect

The runner retains binary/input/manifest hashes, flags, GPU samples,
execution and proving timestamps keyed by task kind and ID, memory
measurements, proof verification and cache-reuse checks. Each output
directory must be new. Raw logs and proof caches remain under `target/`.
Compact records and compressed logs are archived under [results](results/).
GPU memory/utilization are sampled once per second. Peak grants include
unused admission credit; they are not RSS measurements.

`build.py` uses the normal release profile, all available cores and the
local backend checkout. It restores Cargo configuration and lockfile
after the temporary path override, and rejects unrelated dependency
resolution changes. The [build record](results/build/build.json), source
patches and extra source snapshots identify the measured binary:
`dba4f7f15beb44ada66c33942dd2e99a83b3d4ed78dc8f3bda486cebe738e57c`.

```sh
python3 bench/shared-execution-init-2026-09-15/build.py
systemd-run --user --scope -q -p MemoryMax=920G -p MemorySwapMax=0 -- \
  python3 bench/shared-execution-init-2026-09-15/run.py \
    --binary target/shared-execution-build/ix-shared-execution \
    --input target/tree-cache-bench/fixture/init.ixe \
    --output target/shared-execution-init/automatic-new
```

To reproduce the four-claim cut, add `--shards 4` and choose a new output
directory. The runner's default is automatic sharding. Runtime design and memory-model
limits are in [§3.6](../../docs/aiur-multi-gpu-design.md#36-shared-execution-and-memory-budget).
