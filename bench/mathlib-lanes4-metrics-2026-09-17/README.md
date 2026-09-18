# Mathlib on four GPUs with lightweight metrics: coset cache, resident seeds, four executions per lane, sppark

**Result (2026-09-17):** Mathlib proven end to end in **40:02 wall, 2,396 s
prover end to end**, on four RTX PRO 6000 Blackwell in one process
(`ix prove --lanes 4 --exec-jobs 3 --max-ram 230`), on the calibrated
78-shard manifest, with `AIUR_METRICS` on. Root
`026c8d3841c6e62a95e1fbc66264e95dc9c6bf636c654501604b51855df7cc3d`
verified, composed verdict OK, zero growth waits, zero contention retries.
Against run 3 of `../mathlib-seed-2026-09-15` (same manifest, 51:29 wall,
3,084 s prover, no metrics) that is 22% less prover time.

The first attempt aborted at +138 s with `cudaErrorInvalidResourceHandle`
from the generated-trace upload as the second GPU started proving: the
trace runtime's staging pool was process-wide and its events belonged to
the first device that used them. See [the lease bug](#the-staging-lease-bug).

| Quantity | Run 3 (2026-09-15) | This run |
|---|---:|---:|
| Wall, `/usr/bin/time` | 51:29 | **40:02** |
| Prover end to end | 3,084 s | **2,396 s** (−22%) |
| Last claim proven | +2,528 s | +1,938 s |
| Root dispatched / proven | +2,844 s / +3,084 s | +2,236 s / +2,396 s |
| Tail after the last claim | 556 s | 458 s |
| Claim record mean / p90 / max | 29.3 / 33.9 / 44.9 GiB | 28.4 / 32.9 / 44.0 GiB (unit 49) |
| Claim execution mean / max | 247 s / 454 s | 225 s / 414 s |
| Claim proof mean / total | 86 s / 6,695 s | **58.0 s / 4,524 s** |
| Join record mean / execution mean | 16.2 GiB / 54 s | 16.2 GiB / 52.7 s |
| Join proof mean / total | 41 s / 3,143 s (76) | **27.7 s / 2,214 s** (80 incl. root wraps) |
| Prover work total, per GPU | 9,942 s, 2,486 s | 6,738 s, 1,685 s |
| GPU proving occupancy | 81% | 70% |
| Mean sampled GPU utilization (whole wall) | 41% | 49 to 54% per device |
| Peak sampled device memory | 66.9 to 67.1 GB | 68.4 to 69.1 GiB |
| Peak process RSS | 682 GiB | 527 GiB |
| Record pool peak grant | 691 of 731 GiB | 650.5 of 731 GiB |
| p90-scaled candidate | 73 | 71 |

**Reading.** Proofs got a third cheaper: claim proofs from 86 s to 58 s
and joins from 41 s to 28 s, on records the same size as before, which is
the generated traces, the per-process FRI coset cache, the double-buffered
staged uploads and the device-resident round-two seeds together (the
metrics file attributes them). Execution barely moved (225 s against 247 s
per claim), so the run is now execution-bound: the provers were busy 70% of
the wall rather than 81%, and the claim phase ended at +1,938 s with 12
executions the supply. Raising `--exec-jobs` is the next lever, at the
cost of a smaller initial reservation (24 slots at 4, 30.5 GiB) against a
32.9 GiB claim p90. The tail also shrank, 458 s against 556 s, with the
cheaper joins. The calibration candidate is 71, as before within the
diminishing-returns band; 78 stands.

The metrics file (`metrics.jsonl`, 224 MB, 7,637 summary records) holds
per-piece summaries at witness, round, proof and lane-unit boundaries; the
proof durations above are its `aiur/prove_planned` boundaries. Its cost
was not measured separately here; the comparison above is against a run
without it, on a different tree.

## Second run: four executions per lane

Same inputs, binary and environment, `EXEC_JOBS=4 run-lanes4.sh`: 16
executions, 24 admission slots, a 30.4 GiB initial reservation. Same root,
verified, composed verdict OK.

| Quantity | `--exec-jobs 3` | `--exec-jobs 4` |
|---|---:|---:|
| Wall, `/usr/bin/time` | 40:02 | **37:59** |
| Prover end to end | 2,396 s | **2,274 s** (−5.1%) |
| Last claim proven | +1,938 s | +1,793 s |
| Root dispatched / proven | +2,236 s / +2,396 s | +2,115 s / +2,273 s |
| Claim execution mean / max | 225 s / 414 s | 235 s / 440 s |
| Claim proof mean / total | 58.0 s / 4,524 s | 59.3 s / 4,623 s |
| Join proof mean / total | 27.7 s / 2,214 s | 28.2 s / 2,253 s |
| Prover work per GPU, occupancy | 1,685 s, 70% | 1,719 s, 76% |
| Mean sampled GPU utilization | 49 to 54% | 53 to 57% |
| Peak process RSS | 527 GiB | 733 GiB |
| Record pool peak grant | 650.5 of 731 GiB | **726.8 of 731 GiB**, 0 waits |
| Initial reservation, largest claim | 36.5 GiB, 120% | 30.4 GiB, 144% |
| p90-scaled candidate | 71 | 85 |

**Reading.** A third more execution supply bought 7.5% on the claim phase
and 5% end to end, not the 12 to 15% the occupancy gap suggested: each
execution slowed by 4% with 16 of them sharing the cores with the
workers' host witness work, and the GPUs, at 76% occupancy, are closer
to their own limit. The cost is memory: the pool peaked at 726.8 of
730.8 GiB, four GiB from its first growth wait, and peak RSS rose 206 GiB.
This is the ceiling for `--exec-jobs` at 78 shards and `--max-ram 230` on
this box; going further needs smaller records, which means more shards,
as the candidate of 85 at the 30.4 GiB reservation also says. The proofs
themselves are unchanged (59 s claims, 28 s joins), so proof cost is
independent of execution concurrency at this level.

## Third run: transforms through sppark

Same inputs and flags as the second run, on the tree that adds the sppark
transform backend (ix `0746a259`: upstream `c8a5a7b2` merged, multi-stark
`b14e623d`, the sppark fork at `176af27`), built with `IX_CUDA_SPPARK=1`
and run with `MULTI_STARK_CUDA_NTT=sppark`, which routes transforms of
2^18 rows and up through sppark with the default 4 GiB panel budget.
Same root, verified, composed verdict OK.

| Quantity | first-party kernels | sppark |
|---|---:|---:|
| Wall, `/usr/bin/time` | 37:59 | **36:00** |
| Prover end to end | 2,274 s | **2,154 s** (−5.3%) |
| Last claim proven | +1,793 s | +1,696 s |
| Root dispatched / proven | +2,115 s / +2,273 s | +2,001 s / +2,154 s |
| Claim execution mean / max | 235 s / 440 s | 243 s / 454 s |
| Claim proof mean / max / total | 59.3 s / 95.9 s / 4,623 s | **54.5 s / 88.6 s / 4,249 s** (−8%) |
| Join proof mean / total | 28.2 s / 2,253 s | **25.5 s / 2,041 s** (−9%) |
| Prover work per GPU, occupancy | 1,719 s, 76% | 1,572 s, 73% |
| Mean sampled GPU utilization | 53 to 57% | 45 to 48% |
| Peak sampled device memory | 68.7 to 69.2 GiB | 71.5 to 71.9 GiB |
| Peak process RSS | 733 GiB | 697 GiB |
| Record pool peak grant | 726.8 of 731 GiB | 725.8 of 731 GiB, 0 waits |
| p90-scaled candidate | 85 | 85 |

**Reading.** Proofs got 8 to 9% cheaper on the same records, in line with
the Init measurements (the proving union 4 to 14% below first-party as
the milestones landed), and the whole run 5%, because execution still
sets the pace: the claim phase is execution-bound at 16 executions and
the mean claim execution rose 3% again with the busier host. The GPUs
now do 1,572 s of work each over a 2,154 s run and sample 45 to 48%
busy, so there is more GPU headroom than before; the next gains are on
the execution side, or from more shards to let more executions fit the
pool. sppark's panel scratch adds about 3 GiB of device memory at peak,
71.9 of 96 GiB. No sppark diagnostics or aborts appeared in a run whose
transforms cover every claim and join shape in Mathlib, which answers the
plan's open question for the default on a whole environment.

Against the 2026-09-15 reference on the same manifest the prover is now
30% faster (2,154 s against 3,084 s), from the generated traces, the
coset cache and upload ring, the resident seeds, the fourth execution
per lane and sppark together.

## Fourth run: five executions per lane, 102 shards, the whole box

The fifth execution per lane does not fit the 78-shard records in any
pool this host can offer (20 records in flight already peak at 726 GiB),
so the cut was reseeded for the new flags: `ix shard mathlib.ixe --max-ram
245 --exec-jobs 5` gives **102 shards** (14.4 MB per shard, `mathlib-seed-
245-5.ixes`, sha256 `b5433790…`), and the run used 245 GiB per lane under a
980 GiB scope, 98% of the host: a 784.8 GiB pool, 28 admission slots, a
28.0 GiB initial reservation, 20 executions. sppark on, as in the third
run. Root `b130434c…` (a different partition, so a different tree and
root), verified, composed verdict OK.

| Quantity | 78 shards, 4 per lane, 230 GiB | 102 shards, 5 per lane, 245 GiB |
|---|---:|---:|
| Wall, `/usr/bin/time` | 36:00 | 36:20 |
| Prover end to end | 2,154 s | 2,175 s (+1%) |
| Last claim proven | +1,696 s | +1,741 s |
| Root dispatched / proven | +2,001 s / +2,154 s | +2,023 s / +2,174 s |
| Claim record mean / p90 / max | 28.4 / 32.9 / 44.0 GiB | 22.4 / 26.9 / 38.6 GiB |
| Claim execution mean / total | 243 s / 18,950 s | 192 s / 19,570 s |
| Join execution mean / total | 55 s / 4,260 s | 49 s / 4,960 s |
| Claim proof mean / total | 54.5 s / 4,249 s | 43.2 s / 4,411 s |
| Join proof mean / total | 25.5 s / 2,041 s | 22.9 s / 2,380 s (104 incl. wraps) |
| Prover work per GPU, occupancy | 1,572 s, 73% | 1,698 s, 78% |
| Mean sampled GPU utilization | 45 to 48% | 48 to 53% |
| Peak process RSS | 697 GiB | 711 GiB |
| Record pool peak grant | 725.8 of 731 GiB | 741.9 of 785 GiB, 0 waits |
| p90-scaled candidate | 85 | 99 |

**Reading.** A wash: the two configurations are within 1% of each other.
The extra execution supply did arrive (execution thread time per unit of
supply fell from 1,450 s to 1,227 s) and the claim phase would have
ended earlier on execution alone, but the finer cut costs 3% more claim
execution, 16% more join execution, 4% more claim proving and 17% more
join proving, and the GPUs, at 78% occupancy, are the limit again. That
is the crossover the earlier runs pointed at: at 78 shards and four
executions the run was execution-bound with GPU headroom; at 102 and
five it is GPU-bound with execution headroom. Anything between lands in
the same 2,150 to 2,180 s band. The next gains are in the proofs
themselves, or in the per-shard overheads of execution and joins, not in
the schedule. Memory was never the limit at either setting; the fourth
run's pool peaked at 742 of 785 GiB and RSS at 711 of 999 GiB.

## Fifth run: the sppark-only backend

Same inputs and flags as the third run (78 shards, four executions per
lane, 230 GiB per lane), on the tree where sppark is the only CUDA
transform backend (ix `7bd17307`: upstream `2ba81a1b` merged, multi-stark
`59df87a4`, the first-party NTT removed, no selector or height threshold;
built with `IX_CUDA=1 IX_CUDA_TRACE_CODEGEN=1` alone). Same root, verified,
composed verdict OK, no growth waits.

| Quantity | sppark opt-in above 2^18 | sppark only |
|---|---:|---:|
| Wall, `/usr/bin/time` | 36:00 | **35:12** |
| Prover end to end | 2,154 s | **2,106 s** (−2.2%) |
| Last claim proven | +1,696 s | +1,639 s |
| Root dispatched / proven | +2,001 s / +2,154 s | +1,952 s / +2,105 s |
| Claim execution mean / max | 243 s / 454 s | 244 s / 459 s |
| Claim proof mean / max / total | 54.5 s / 88.6 s / 4,249 s | **52.4 s / 88.5 s / 4,087 s** (−4%) |
| Join proof mean / total | 25.5 s / 2,041 s | **24.4 s / 1,951 s** (−4%) |
| Prover work per GPU, occupancy | 1,572 s, 73% | 1,510 s, 72% |
| Mean sampled GPU utilization | 45 to 48% | 45 to 48% |
| Peak sampled device memory | 71.5 to 71.9 GiB | 68.1 to 68.6 GiB |
| Peak process RSS | 697 GiB | 641 GiB |
| Record pool peak grant | 725.8 of 731 GiB | 729.1 of 731 GiB |

**Reading.** Routing the transforms below 2^18 rows through sppark as
well takes another 4% off every proof, and the run 2%, with the claim
phase still execution-bound at 244 s per claim against 52 s of proof.
Device memory peaked 3.5 GiB lower than with both backends resident.
The proof side has now more than halved since the 2026-09-15 reference
(86 s to 52 s per claim, 41 s to 24 s per join) while execution has moved
from 247 s to 244 s; with four executions ahead of each prover the GPU
is fed only when execution averages under 4 × 52 = 208 s per claim, so
execution is the whole of the remaining gap. Against the reference the
prover is 32% faster: 2,106 s against 3,084 s.

## The staging lease bug

`crates/aiur/cuda/trace_runtime.cu` stages seed uploads through a ring of
pinned chunks with one CUDA event per chunk, held as a lease for one span.
The pool was four rings for the whole process, handed out first-free, with
each ring's events created on whichever device was current at its first
use. A CUDA event belongs to that device; recording it on another device's
stream fails with `cudaErrorInvalidResourceHandle` (400). Worker 0 filled
the pool's events on device 0, worker 1 took a free ring for device 1, and
the generated kernel returned 400, which multi-stark turned into
`CUDA generated trace LDE failed (999)` and an abort.

The pool arrived with the pipelined upload (`3e535f22`) and every run
since had been on one GPU; the four-GPU results predate it. The fix
(`c66ee1ca`) gives each device its own four rings, allocated on first use.
`concurrent_uploads_keep_frozen_seeds` with `AIUR_TEST_GPU_DEVICES=0,1,2,3`
fails with status 400 before the fix and passes after; the whole
`trace_codegen::tests::cuda` module passes across the four devices.

## Inputs, build and command

| Item | Value |
|---|---|
| `mathlib.ixe` | sha256 `d84ece55…`, byte-identical to the 2026-09-15 bench input |
| `mathlib-78.ixes` | sha256 `29108219…`, seeded by `ix shard --max-ram 230 --exec-jobs 3` (the byte-linear seed, `6377ece4`), byte-identical to the calibrated cut |
| ix | `c66ee1ca` (this branch merged with `origin/sb/aiur-trace-sharding-gpu` at `b274d86b`), multi-stark `f00b7a1`; features `parallel,cuda,cuda-trace-codegen,net`; host CUDA 13.3 nvcc, driver 595.91.07, Lean 4.33.1 from the Nix dev shell |
| Host | 4× RTX PRO 6000 Blackwell Server Edition, 96 CPUs, 999 GiB; THP `always` / `defer+madvise` |
| Environment | `AIUR_GPU_TRACE=generated AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24 AIUR_TRACE_SHARD_MAX_CELLS=1500000000 AIUR_METRICS=<run>/metrics.jsonl`, `LD_PRELOAD=libcuda.so.1` (the Nix-linked binary does not search the host library path), no `AIUR_PROFILE`, `RUST_LOG` or `--texray` |
| Command | `run-lanes4.sh <label>`: `systemd-run --user --scope -p MemoryMax=920G -- ix prove --ixe mathlib.ixe --ixes mathlib-78.ixes --trace-shards --lanes 4 --exec-jobs 3 --max-ram 230` |

Archived from the box: `logs/<run>/` holds each run's lanes stderr and
stdout, GPU samples and metadata, gzipped; `data/<run>-proofs.csv` every
unit's proof time from the metrics file; `proofs/` the verified root
proofs of the 78-shard runs (`026c8d38…`, identical across them) and the
102-shard run (`b130434c…`), 5.75 MiB each.

Files: `mathlib78-lanes4-meta.txt`, `mathlib78-lanes4-summary.txt`,
`mathlib78-lanes4-exec4-meta.txt`, `mathlib78-lanes4-exec4-summary.txt`,
`mathlib78-lanes4-exec4-sppark-meta.txt`,
`mathlib78-lanes4-exec4-sppark-summary.txt`,
`mathlib102-lanes4-exec5-sppark-meta.txt`,
`mathlib102-lanes4-exec5-sppark-summary.txt`,
`mathlib78-lanes4-exec4-sppark-only-meta.txt`,
`mathlib78-lanes4-exec4-sppark-only-summary.txt`, `run-lanes4.sh` (`EXEC_JOBS`, `MAX_RAM`, `MEM_MAX` and `IXES` select the
executions per lane, the per-lane budget, the scope cap and the manifest). Raw logs, the metrics file, the GPU samples and the
lanes cache are in `~/benchdata/mathlib/runs/mathlib78-lanes4-metrics-2/`
on the four-GPU box; the aborted first attempt is beside it without the
`-2`.
