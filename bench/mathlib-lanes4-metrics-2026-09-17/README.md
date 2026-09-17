# Mathlib on four GPUs with lightweight metrics, after the coset cache and resident seeds

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

Files: `mathlib78-lanes4-meta.txt`, `mathlib78-lanes4-summary.txt`,
`mathlib78-lanes4-exec4-meta.txt`, `mathlib78-lanes4-exec4-summary.txt`,
`run-lanes4.sh` (`EXEC_JOBS` selects the executions per lane). Raw logs, the metrics file, the GPU samples and the
lanes cache are in `~/benchdata/mathlib/runs/mathlib78-lanes4-metrics-2/`
on the four-GPU box; the aborted first attempt is beside it without the
`-2`.
