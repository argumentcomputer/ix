# Mathlib on four GPUs at the seeded shard count

**Result (2026-09-15):** Mathlib proven end to end in **52:49** on four
RTX PRO 6000 Blackwell in one process (`ix prove --lanes 4`), from a
111-shard min-cut manifest seeded by `ix shard --max-ram 230 --exec-jobs 3`,
with GPU BLAKE3 trace generation on. Root
`feb2e6c687a010f915a01808f11806d37ddbd7b81a4694e2434a402eb0196b80`
verified, composed verdict over all 111 claims OK, zero record-cap trips.
One run; no CPU-trace pair on this box (the prior four-lane result was
1:06:12 with 128 shards, CPU traces and a different Mathlib compile, so
the two are not a controlled comparison).

| Quantity | Value |
|---|---:|
| Wall, `/usr/bin/time` | 52:49.04 (prover's own end to end 3164 s) |
| CPU time user + system | 114,965 s + 8,223 s |
| Peak process RSS | 522.4 GiB (four workers, `--max-ram 230` each, 920G scope) |
| Sampled peak device memory | 66.9–67.1 GB on each of the four GPUs |
| Mean sampled GPU utilization | 43% |
| Last claim proven | +2640 s (44:00) |
| Root dispatched / proven | +2997 s / +3164 s |
| Tail after the last claim | 524 s = 8.7 min, 16.5% of the run (357 s until root dispatch; 167 s for root preparation, proving and wrapping) |

Inputs: `mathlib.ixe` compiled on this box (sha256 `d84ece55…`, 679,499
constants, 3.1 GB), cut into `mathlib-seed-230.ixes` (sha256 `bee774da…`).
Binary: `target/gpu-trace-build/ix-no-tree-cache`, sha256 `9883ee50…`, ix
`d9cb6ad9` plus the working tree's record instrumentation and the tree-cache
removal, multi-stark `f54b44f` plus the uncommitted removal (both patches
saved beside the binary). Environment: `AIUR_GPU_TRACE=blake3`,
`AIUR_TRACE_ONLY_LOOKUPS=1`, `AIUR_MAX_PIECE_LOG_HEIGHT=24`,
`AIUR_TRACE_SHARD_MAX_CELLS=1500000000`, THP `always`/`defer+madvise`.
`RUST_LOG` was unset, so the per-shard "prepared GPU BLAKE3 trace" debug
lines are absent; the selector is recorded in `seed111-gpu-meta.txt` and
the binary's provider is the one the Init comparison exercised.

## Second run: the same manifest on the shared-execution scheduler

Same inputs, flags and GPU traces, binary
`target/shared-execution-build/ix-shared-execution` (sha256 `dba4f7f1…`):
one process-wide execution pool of twelve threads, a four-slot prepared
queue feeding the four GPU provers, joins prioritized in both queues, and
the shared record pool with pause-and-grow (docs/aiur-multi-gpu-design.md
§3.6). Same root, verified, composed verdict OK.

| Quantity | Per-worker scheduler (run 1) | Shared scheduler (run 2) |
|---|---:|---:|
| Wall | 52:49 | 52:59 |
| Prover end to end | 3164 s | 3174 s |
| Last claim proven | +2640 s | +2670 s |
| Tail after the last claim | 524 s | 504 s |
| Claim execution mean / max | 167 s / 364 s | 179 s / 395 s |
| Claim proof mean | 62 s (attributed) | 60 s (measured) |
| Join execution / proof mean | 44 s / 38 s | 46 s / 35 s |
| Claim wait in the prepared queue for a GPU | not logged | mean 98 s, max 249 s |
| GPU proving occupancy | 87% (attributed) | 82–86% (measured) |
| Mean sampled GPU utilization | 43% | 43% |
| Peak RSS | 522 GiB | 571 GiB |
| CPU time | 123,188 s | 122,971 s |
| Record pool | n/a | peak grant 627 of 731 GiB, 0 growth waits, 0 contention |
| GPU BLAKE3 dispatch lines | not logged | 2,536 |

Claim 70 (38.2 GiB) grew past its 36.5 GiB initial credit without waiting;
the pool had 300 GiB free. Its execution took 395 s against 364 s.

**Reading.** The two schedulers are within noise of each other because the
run is GPU-bound: a prepared claim waited 98 s on average for a free
prover, the provers were busy 82–86% of the wall, and executions were
never the limit (twelve in flight almost throughout). Prioritizing joins
built more of the tree early (14 joins done at +600 s against 7) but the
tail only shrank from 524 s to 504 s, because the chain from the last leaf
to the root is the same seven joins plus a 175 s root (74 s execution,
101 s wraps). So scheduling is exhausted at this shard count; the next
levers are the proof itself: the GPU is busy only about half the time
*inside* a proof (43% utilization against 84% occupancy), which is the
CPU half of each round, the regeneration and the barrier; two provers per
device to overlap those halves; and a cheaper join proof (36% of proving
time). The record pool is validated end to end but had nothing to
absorb here; a coarser cut is where it earns its keep.

The p90-scaled candidate at the 36.5 GiB initial reservation is 78
shards. Files: `seed111-gpu-shared-meta.txt`,
`seed111-gpu-shared-lanes-summary.txt`; raw logs and the run's proof
cache in `~/benchdata/mathlib-gpu/seed111-gpu-shared/`.

## Third run: 78 shards, the p90-scaled candidate, same binary

`ix shard mathlib.ixe --shards 78` (`mathlib-78.ixes`, sha256 `29108219…`),
everything else as run 2. Root
`ce5244b413a1d469d0fa72cf89ce3b35111ab85bb07ba49457faffc0ae1dcf17`,
verified, composed verdict OK.

| Quantity | 111 shards (run 2) | 78 shards (run 3) |
|---|---:|---:|
| Wall | 52:59 | **51:29** (−2.8%) |
| Prover end to end | 3174 s | 3084 s |
| Last claim proven | +2670 s | +2528 s |
| Tail after the last claim | 504 s | 556 s |
| Claim record mean / p90 / max | 21.3 / 25.4 / 38.2 GiB | 29.3 / 33.9 / 44.9 GiB (unit 49) |
| Claim execution mean / max | 179 s / 395 s | 247 s / 454 s |
| Claim proof mean / total | 60 s / 6,712 s | 86 s / 6,695 s |
| Join record mean / execution / proof | 13.6 GiB / 46 s / 35 s | 16.2 GiB / 54 s / 41 s |
| Join proof total | 3,855 s (109) | 3,143 s (76) |
| Prover work total, per GPU | 10,668 s, 2,667 s | 9,942 s, 2,486 s |
| GPU proving occupancy / sampled utilization | 84% / 43% | 81% / 41% |
| Claim wait in the prepared queue | mean 98 s | mean 123 s |
| Peak RSS | 571 GiB | 682 GiB |
| Record pool | peak grant 627 GiB, 0 waits | peak grant 691 of 731 GiB, 0 waits |
| CPU time | 122,971 s | 114,990 s (−6.5%) |

**Reading.** The proportional model held exactly: total claim proving was
unchanged (6,695 s against 6,712 s) while the mean claim proof rose from
60 s to 86 s with the 29 GiB mean record, and the saving came from the
33 joins removed, 712 s of prover time even though each join grew from
35 s to 41 s as the child proofs got wider. Per GPU that is 181 s of work
saved; 90 s of it reached the wall clock, because occupancy slipped from
84% to 81% (claims wait 123 s for a prover, so the GPUs were the limit
throughout, but the bigger units leave longer gaps between proofs) and
the tail grew by 52 s with the heavier joins. Memory is now nearly the
constraint: the pool peaked at 691 of 731 GiB and the largest record
was 44.9 GiB, 122% of the initial credit, granted without a wait. The
p90-scaled candidate from this run is 73; the returns are clearly
diminishing (−2.8% for −30% shards) and the next step down would run
the pool into growth waits at `--max-ram 230` on this box.

The 38.2 GiB block was not the only tail: at 78 shards a different
shard (49) reached 44.9 GiB, so the largest record does move with the
cut, just much less than the mean (max/mean 1.79 → 1.53).

Files: `mathlib78-gpu-shared-meta.txt`, `mathlib78-gpu-shared-lanes-summary.txt`;
raw logs and proof cache in `~/benchdata/mathlib-gpu/mathlib78-gpu-shared/`.

## Calibration: record sizes by the cap's own measure

The scheduler now logs every unit's execution time and retained record
bytes against its cap as it finishes, and a summary at the end
(`[lanes] calibration:` lines; `summarize.py` tabulates them). At a
41.4 GiB share (207.3 GiB record budget over `--exec-jobs 3` + 2):

| Unit | n | Record mean | p50 | p90 | Max | Execution mean / max |
|---|---:|---:|---:|---:|---:|---:|
| Claims | 111 | 21.4 GiB | 21.0 | 25.1 | **38.2 GiB, 92% of the share (claim 70)** | 167 s / 364 s |
| Joins | 109 | 13.5 GiB | 13.7 | 15.3 | 18.2 GiB, 44% | 44 s / 72 s |
| Root | 1 | 25.0 GiB | | | 60% | 67 s |

The seed re-anchored on this cut is **102 shards** at this share.

What the distribution says:

- **There is one record-size outlier.** The next-largest claim record is 28.4 GiB; the
  top ten are 26–28 GiB. Claim 70's 38.2 GiB stands alone, and it executed
  in 364 s against a 167 s mean. It was proven at +1762 s, mid-run, so it
  did not lengthen the tail this time; scheduled late it would have.
- **The mean roughly follows inverse shard count; the maximum needs more evidence.** The
  128-way cut's largest record was 35.8 GiB with a 18.95 GiB mean; this
  111-way cut's is 38.2 GiB with 21.4 GiB (128/111 × 18.95 = 21.9
  predicted). This supports trying a seed based on the body of the
  distribution. It is consistent with a persistent heavy block, but the
  compile also changed: compare the actual heavy shards before concluding
  that the maximum is indivisible or will remain near 38 GiB at coarser
  cuts. The current maximum-based seed (`gpu_seed_shards`, linear in
  max/share) is sensitive to this one outlier.
- **Joins used less record memory in this run.** Their records sit in a
  13–18 GiB band; the root is 25 GiB. This leaves room for a shared budget
  to charge completed records by their own sizes. Measure join growth
  again when changing the environment cut.

## What to do with it

1. Try seeding on the body of the distribution: p90 (25.1 GiB) against the
   share gives about 67 shards at 41.4 GiB, assuming inverse scaling.
   This is a candidate cut, not a measured optimum; the memory policy must
   accommodate records above that percentile.
2. That policy is the missing piece: an over-share execution today reruns
   alone on a drained worker, wasting a partial execution before the full
   re-execution. A shared record budget lets an execution grow into spare
   capacity or wait while prepared and proving records drain. Keep a
   discard-and-requeue fallback for mutually blocked executions. See the
   proposed [shared execution and memory budget](../../docs/aiur-multi-gpu-design.md#36-shared-execution-and-memory-budget).
3. The next cut to measure is ~90 shards under the current rerun policy
   (projected mean 26.4 GiB and p90 31.0 GiB, 21 fewer joins). This tests
   the scaling assumption on the same input and measures whether the
   outlier grows enough to trip.
4. The 8.7-minute tail starts with parallel work: 20 non-root joins finish
   after the last claim, initially across all four workers. The last
   non-GPU-0 completion is at +2808 s; root dispatch is +2997 s and root
   completion is +3164 s. The final 167 s include root execution, proving
   and wrapping. Prioritize ready joins and start expensive claims early
   where costs are known. A shared queue can reduce waiting for an assigned
   worker, but the final dependency chain still limits parallelism.

Files: `seed111-gpu-records.csv` (every unit: kind, id, worker, execution
seconds, record bytes, percent of cap, proven-at; completion lookup uses
both kind and ID because claim and join numbers overlap), `seed111-gpu-meta.txt`
(hashes, driver, THP, flags, environment, repo state), and
`seed111-gpu-lanes-summary.txt`. Raw `lanes.err`, `gpu.csv` and the run's
proof cache are in `~/benchdata/mathlib-gpu/seed111-gpu/`.

## Reproduce

```sh
cd ~/benchdata/mathlib-gpu
ix compile Benchmarks/Compile/CompileMathlib.lean --out mathlib.ixe      # 3:03, 22 GiB
AIUR_TRACE_SHARD_MAX_CELLS=1500000000 \
  ix shard mathlib.ixe --max-ram 230 --exec-jobs 3 --out mathlib-seed-230.ixes   # 111 shards, 73 s
AIUR_GPU_TRACE=blake3 IX=/path/to/ix IXE=mathlib.ixe IXES=mathlib-seed-230.ixes \
  sh ~/repos/ix/bench/mathlib-seed-2026-09-15/run.sh seed111-gpu
python3 ~/repos/ix/bench/mathlib-seed-2026-09-15/summarize.py seed111-gpu --csv records.csv
```

`run.sh` records the binary, input and manifest hashes, driver, THP state,
flags and environment, samples the GPUs once a second, and runs under a
920G user scope with a fresh `AIUR_LANES_CACHE_DIR` so nothing resumes.
Defaults: `--lanes 4 --exec-jobs 3 --max-ram 230`, CPU traces unless
`AIUR_GPU_TRACE` is set.
