# Generated traces on Mathlib, 78 shards, one GPU, 15-minute windows

**Result (2026-09-17):** on the same 78-shard Mathlib partition the
four-GPU bench used (`bench/mathlib-seed-2026-09-15`, run 3), one GPU
proved the same 11 claims and 6 joins in both trace modes inside a
15-minute window. Generated traces (`ix-new6`, 56 writers) finished the
last of those units 31 s earlier than CPU traces, cut host witness time
from 337 s to 136 s of union wall, and raised sampled GPU utilization
from 58% to 63%. On the same 11 claims the saving is 39 s of stage-one
commitment against 36 s more lookup construction, because the generated
path regenerates rows for the lookup kernel instead of keeping them. No
seed-preparation fallback occurred (1,034 generated spans). The windows were cut short deliberately, so there is no root and
no end-to-end time; the full one-GPU proof is on the order of three hours
per mode.

## Fixture and command

```sh
ix compile --no-build Benchmarks/Compile/CompileMathlib.lean --out mathlib.ixe   # 70 s, 20 GiB RSS
ix shard mathlib.ixe --shards 78 --out mathlib-78.ixes                            # 54 s
IXE=mathlib.ixe TIMEOUT=900 run.sh ix-new6 <label> <cpu|generated> mathlib-78.ixes \
  --exec-jobs 3 --max-ram 230 --no-index
```

`mathlib.ixe` sha256 `d84ece55…` and `mathlib-78.ixes` sha256 `29108219…`
are byte-identical to the inputs of the four-GPU run recorded in
`../mathlib-seed-2026-09-15/mathlib78-gpu-shared-meta.txt`.

### Why 78 shards

The count is not a seed; it is the calibrated candidate from the
four-GPU bench, and it is the partition to benchmark Mathlib on until a
run recalibrates it. The chain:

1. `ix shard mathlib.ixe --max-ram 230 --exec-jobs 3` seeded 111 shards
   on the four-GPU box (a 41.4 GiB record share). Run 2 there proved them
   with zero record-cap trips: claim records mean 21.3 GiB, p90 25.4 GiB,
   max 38.2 GiB, at a 36.5 GiB initial reservation.
2. The scheduler's calibration line rescales the count so the p90 claim
   record fits the initial reservation, `ceil(shards × p90 / reservation)`
   (`crates/ffi/src/aiur/aggregate/lanes.rs`, the `p90-scaled candidate`):
   `ceil(111 × 25.4 / 36.5) = 78`.
3. Run 3 proved `--shards 78` in 51:29 against 52:59 for 111, the best
   Mathlib result recorded, with records mean 29.3 GiB, p90 33.9 GiB, max
   44.9 GiB and no growth waits. Its own candidate is
   `ceil(78 × 33.9 / 36.5) = 73`, with diminishing returns and the pool
   at 691 of 731 GiB, so 78 stands.

On this box the seed does not reproduce those counts: the same binary
tree seeds 115 shards at `--max-ram 200 --exec-jobs 3` and 100 at
`--max-ram 230 --exec-jobs 3` from the identical `.ixe`, where the
four-GPU box's build seeded 111 at 230. Both cuts were made and discarded
here before the 78-shard manifest was recut with `--shards 78`. Pass the
explicit count; do not rely on the seed for Mathlib comparisons.

With one lane at `--max-ram 230 --exec-jobs 3` the budget line reads
182.7 GiB of shared records, five admission slots and the same 36.5 GiB
initial reservation as the four-GPU run, so record admission behaves the
same per lane. Peak RSS in the generated window was 156 GiB of the host's
249 GiB. The Mathlib
oleans came from `lake exe cache get` with `MATHLIB_CACHE_DIR` pointed at
a writable directory. `run.sh` is the Init bench script with the
environment path and a `timeout` wrapper parametrized; the same flags as
Init otherwise (`AIUR_TRACE_ONLY_LOOKUPS=1`, `AIUR_MAX_PIECE_LOG_HEIGHT=24`,
`AIUR_TRACE_SHARD_MAX_CELLS=1500000000`, fresh lanes cache, `AIUR_PROFILE`
spans, one-second `nvidia-smi` samples). Host: 32 cores, 249 GiB, one
RTX PRO 6000; binary `ix-new6` from the Init bench.

`spans.txt` was produced with the `spans.py` that accumulates completed
intervals across span-ID reuse (fixed 2026-09-17; the earlier version
undercounted device callbacks 5.7x and lookup construction 5.5x here).
Each directory holds `lanes.err` (the prover log without the per-span
debug lines), `units.txt` (per-unit execution, record and proof times,
from `units.py`), `spans.txt`, `gpu.csv` and, for the generated run,
`time.txt`. The CPU run was stopped by hand at its 15-minute mark and
GNU time's summary was lost with it, so its CPU time and peak RSS are not
recorded; `free` showed 138 GiB in use at the end.

## The same 17 units, CPU traces against generated traces

| Unit | Record | Exec s, cpu | Exec s, gen | Proof s, cpu | Proof s, gen |
| --- | ---: | ---: | ---: | ---: | ---: |
| claim 0 | 20.8 GiB | 105.8 | 106.4 | 43 | 43 |
| claim 1 | 23.7 | 133.4 | 131.2 | 49 | 48 |
| claim 2 | 26.6 | 146.3 | 143.8 | 57 | 56 |
| claim 3 | 22.3 | 144.8 | 132.0 | 48 | 46 |
| join 2 | 15.2 | 42.7 | 39.0 | 32 | 28 |
| claim 4 | 26.0 | 173.1 | 161.0 | 58 | 57 |
| claim 5 | 24.6 | 163.7 | 149.0 | 53 | 49 |
| join 4 | 15.6 | 45.7 | 43.2 | 30 | 27 |
| join 7 | 17.0 | 48.4 | 44.3 | 34 | 30 |
| claim 6 | 26.0 | 169.8 | 156.2 | 55 | 53 |
| claim 7 | 27.5 | 181.5 | 170.0 | 61 | 60 |
| join 9 | 15.1 | 43.8 | 38.6 | 30 | 26 |
| claim 8 | 27.7 | 177.6 | 167.2 | 62 | 62 |
| claim 9 | 28.2 | 180.3 | 167.9 | 60 | 60 |
| join 13 | 17.8 | 51.3 | 45.9 | 36 | 31 |
| join 10 / 15 | 13.2 / 16.9 | 40.8 | 45.9 | 26 | 29 |
| claim 10 | 25.4 | 168.5 | 155.2 | 56 | 53 |

The sixth join differs (join 10 under CPU traces, join 15 under generated)
because the generated run's earlier claim proofs changed which pair was
ready first; the other 16 units are the same in both runs.

| Total over the window | CPU traces | Generated |
| --- | ---: | ---: |
| Claims proven / joins proven | 11 / 6 | 11 / 6 |
| Claim proof mean | 54.7 s | 53.4 s |
| Join proof mean | 31.3 s | 28.5 s |
| Claim proof total | 602 s | 587 s |
| Join proof total | 188 s | 171 s |
| Last unit proven at | +897 s | +866 s |
| Claim execution mean | 158.6 s | 149.1 s |
| Proving union (`aiur/prove_planned`) | 787 s | 755 s |
| Stage-one commit union | 459 s | 393 s |
| Host witness union (`aiur/witness`) | 339 s | 200 s |
| CPU-built circuits (`aiur/cpu_witness`) | 337 s | 136 s |
| Lookup construction union | 113 s | 161 s |
| Quotient union / FRI open union | 108 s / 98 s | 109 s / 100 s |
| Seed packing (`aiur/codegen_seeds`) | | 165 s (1,034 spans) |
| Device callbacks (`aiur/codegen_device_rows`) | | 88.9 s (128,987 spans) |
| Execution union (`aiur/execute_ixvm`) | 915 s | 847 s |
| Mean sampled GPU utilization | 57.9% | 62.6% |
| Peak RSS | not recorded | 156 GiB |

## The same 11 claims, phase by phase

`matched.py` matches each `aiur/prove_planned` interval to the lanes
log's units in time order and clips every phase span to its proof's
interval (`matched.txt`). Over claims 0 to 10, which both runs proved:

| Phase, summed over the 11 claims | CPU traces | Generated | Change |
| --- | ---: | ---: | ---: |
| Proof | 599.8 s | 586.0 s | −13.8 s |
| Stage-one commit | 327.5 s | 288.1 s | −39.4 s |
| Lookup construction | 82.4 s | 118.2 s | +35.8 s |
| Quotient | 86.1 s | 85.8 s | −0.3 s |
| FRI open | 79.5 s | 80.2 s | +0.7 s |
| Host witness (`aiur/witness`) | 278.4 s | 160.1 s | −118.3 s |
| Seed packing | | 138.6 s | |
| Device callbacks | | 73.5 s | |

Over the five joins both runs proved: proof −20.8 s, stage-one commit
−26.9 s, lookup construction +7.3 s.

## What the numbers say

- **Lookup construction gives back most of the commitment saving.** The
  generated commit path (`multi-stark/src/cuda/witness.rs`, `release_trace`
  after the LDE) retains no copy of a generated trace, so the lookup-graph
  kernel regenerates every row tile through the callbacks; the CPU path
  keeps the host matrix. On the 11 claims that is +35.8 s of lookup
  construction against −39.4 s of stage-one commit, and the callbacks
  inside lookup construction are the cost. The Init runs show the same
  pattern at 38 s against 54 s. Bounded retention of expensive raw device
  traces while memory allows, or caching the compact device seeds so the
  regeneration skips the host copy, is the next trace-generation change,
  and it has a measured target.

- **Per-unit proving gains are 2 to 13%.** Claim proofs lost about 1 s
  each and joins about 4 s each. Generation replaces 118 s of host circuit
  building on the 11 claims with 139 s of seed packing and 74 s of device
  callbacks, of which about 102 s of the packing overlaps CPU circuit
  construction of other circuits rather than sitting alone on the path.
- **Seed packing is large but not yet profiled.** The 165 s union is one
  span per member run around live-query filtering, parallel row packing
  with record lookups, allocation, widening and the serial concatenation
  into the final span (`prepare` in `crates/aiur/src/trace_codegen/cuda.rs`).
  Circuit 12 alone packs 768 M rows in 32 s of union wall, circuit 170
  440 M rows in 16 s. Which of those steps dominates is not established
  by this profile; splitting the span is the prerequisite for deciding
  between writing straight into the final buffers, wider parallelism, and
  a device-side gather from uploaded record tables. The 88.9 s of device
  callbacks include allocation, the tile blank, DMA, kernels and the final
  stream wait, so they do not isolate copy time either.
- **The worker was busy throughout.** Unlike Init at four shards, the
  78-shard graph keeps the one worker proving from the first claim to the
  end of the window (proving union 755 to 787 s of the 900 s), so proving
  improvements reach the wall clock here. Claim executions ran faster on
  this box than on the four-GPU host (149 to 159 s mean against 247 s)
  because three executions share 32 cores rather than twelve sharing 96.
- **Reference.** The four-GPU run of the same partition with the
  handwritten BLAKE3 provider proved claims in 86 s mean and joins in 41 s
  mean; the wider records and the shared execution pool of that box make
  those numbers not directly comparable with one GPU's.
