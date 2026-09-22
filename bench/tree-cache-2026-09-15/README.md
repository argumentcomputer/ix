# Merkle retention performance comparison

**Result:** a 24 GiB allowance reused all 91 trees with no budget refusals,
workspace evictions or LDE spills. Retention works, but this one larger-budget
run did not improve end-to-end time.

| Fixed-backend tree budget per batch/GPU | Completed trials | Wall time | Trees reused per run | Budget refusals per run |
| --- | ---: | --- | ---: | ---: |
| 0 | 2 | 284.54 s median; 281.35–287.74 s | 0 | — |
| 512 MiB | 3 | 284.84 s median; 279.34–285.77 s | 15 | 76 |
| 24 GiB | 1 | 290.06 s | 91 | 0 |

The 24 GiB run used at most 21.06 GiB of queued checkpoints in one batch.
Its sampled peak VRAM was 81.78 GiB per device, compared with 65.35 GiB for
regeneration; peak process RSS was 198.29 GiB. Every completed trial verified
the same root and generated the same work. The old backend's regeneration
median was 285.31 s (three trials), versus 284.54 s for the fixed backend
(two trials); these small differences do not establish a throughput change.

The larger cap removes budget refusals on this fixture. Since it did not
improve time in the measured run, the tree-retention feature was removed
from ix and multi-stark. This directory preserves the experiment and its
frozen binaries; its cache controls do not apply to current source. No
more retention trials are scheduled. See [individual results](results/comparison/analysis.md)
for the full comparison and the explicitly excluded interrupted trial.

The fixed workload is the complete eight-claim Init environment, its seven
joins, and verified aggregate root. It was recreated from
`Benchmarks/Compile/CompileInit.lean` using Lean 4.33.1, then partitioned
once with `ix shard --shards 8`. Every trial uses the same hashed `.ixe`
and `.ixes` files and a new proof cache.

## Cases

| Case | Backend | Trace generation | Tree allowance |
| --- | --- | --- | --- |
| A: `old-regenerate` | Preserved instrumented build, before admission fixes | GPU BLAKE3 | 0 |
| B: `fixed-regenerate` | Admission fixes | GPU BLAKE3 | 0 |
| C: `fixed-trees` | Admission fixes | GPU BLAKE3 | 512 MiB per batch |
| D: `fixed-trees` | Admission fixes | GPU BLAKE3 | 24 GiB per batch |

A/B measures the code changes with retention disabled. B/C measures enabling
retention within the same fixed binary. D tests a larger allowance using
one additional trial. This comparison does not remeasure
CPU versus GPU trace generation.

All trials use four resident GPU workers, two executions ahead per worker,
200 GiB per-worker RAM budget, 1.5 billion committed cells per trace shard,
and maximum piece log height 24. Host worker counts use the backend defaults;
CPU affinity, GPU identities, driver, binary hashes and environment are
recorded. Each process has a 15-minute watchdog. The outer user scope caps
memory at 400 GiB and disables swapping.

The diagnostic pilot enables detailed admission events and is excluded
from timing comparisons. Repeated trials use only trace-provider and batch
summary events. The initial orders were **ABC**, **BCA**, **CAB**. Eight trials completed;
the final B trial was interrupted when the sweep was stopped at the user's
request. Its partial output is explicitly excluded. D ran once afterward.
Results are preserved after every trial; no further sweep is scheduled.

The diagnostic pilot completed in 283.09 seconds, verified the historical
root `6221602089142e7998ca8581617c70ae817e7bd68a8c0c510a67a1723a794024`,
and generated 110,892,480 rows across both rounds. All 15 admitted trees
were reused, with no evictions or LDE spills; 76 candidates exceeded the
remaining cache budget. All 17 completed batches supplied counters. This
pilot is a validation result, not a retention speedup measurement.

## Budget selection

512 MiB is the earlier experiment's setting, not a GPU limit. The detailed
pilot recorded 91 checkpoint candidates, including 32 with 4 GiB node
allocations. The largest batch totals about 21.1 GiB. Metadata also counts
against the cap, so a 4 GiB cap does not fit a 4 GiB node allocation.

The additional 24 GiB trial gives the largest observed batch enough room
under the byte cap. The allowance is per batch on its owning GPU; allocation
admission can still evict optional trees when the next proving phase needs
space. It is an experiment setting for this fixture and four 95.6 GiB GPUs.
The runner accepts an explicit `--tree-budget-mib` and records the exact byte
value with each result.

## Validation and measurements

A successful trial must exit zero, prove eight claims and seven joins from
a fresh proof cache, report GPU trace generation, and finish with the
expected verified root. Root identity and generated work must agree across
trials. Cache-enabled trials must have actual reuse hits.

The fixed backend's typed batch counters supply admissions, hits, refusals,
evictions and logical LDE spill bytes. Every completed batch must have an
empty checkpoint queue and account for every admission. Counters are read
from the current CLI's structured tracing fields; verification and workload
completion still use its text output. This fixture runner is separate from
the `ix bench` row interface; direct prover report integration remains a
follow-up. Raw output is retained for auditing.

Each trial records wall time, process user/system time, peak process RSS,
sampled per-device memory, and per-batch cache counters. GPU memory is
sampled once per second, so its maximum is not an exact allocation peak.
Logical LDE spill bytes and seed preparation bytes are not PCIe traffic.
Report all trials, median/range and within-block differences; do not infer
a small speedup from a single trial.

## Reproduce

The frozen binaries and build provenance are in `target/tree-cache-build/`.
Fixture construction commands, hashes and compile report are in
`target/tree-cache-bench/fixture/`. Keep that fixture unchanged between cases.

```sh
systemd-run --user --scope -q -p MemoryMax=400G -p MemorySwapMax=0 -- \
  python3 bench/tree-cache-2026-09-15/run.py \
    --old target/tree-cache-build/ix-instrumented-before-tree-fix \
    --fixed target/tree-cache-build/ix-tree-cache-fixed \
    --fixture target/tree-cache-bench/fixture \
    --output target/tree-cache-bench/budget-24g-new \
    --case fixed-trees --tree-budget-mib 24576 \
    --expected-root 6221602089142e7998ca8581617c70ae817e7bd68a8c0c510a67a1723a794024 \
    --expected-batches 17
```

This command runs one trial, approximately five minutes on all four GPUs.
Use `--case fixed-regenerate` for one zero-cache comparison. Output
directories must be new. The runner does not build, repartition the fixture,
or delete proof caches. Add `--diagnostics` only for a separate diagnostic
pilot; those timings are excluded from comparisons.

To summarize the completed trials, explicitly excluding the interrupted one:

```sh
python3 bench/tree-cache-2026-09-15/summarize.py target/tree-cache-bench/comparison \
  --allow-incomplete --include target/tree-cache-bench/budget-24g
```

This writes individual timings, median/range and paired differences to
`analysis.md` and `analysis.json`, plus aggregate rows in the standard
benchmark JSON shape. Cache outcomes remain available per trial and batch.

The [saved results](results/comparison/analysis.md) list every completed
trial and the excluded partial trial. Small metadata files, counters,
commands and compressed raw logs are archived in `results/`. Large fixture
files, binaries and proof caches remain under `target/`.
