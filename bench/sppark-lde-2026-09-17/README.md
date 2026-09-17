# Resident coset LDE: first-party kernels against sppark, 2026-09-17

`multi-stark/examples/cuda_resident_lde_bench.rs` on one RTX PRO 6000
Blackwell, CUDA 13.3, `RAYON_NUM_THREADS=8`, five warm iterations per shape
after one cold, medians below. Same binary, multi-stark `sb/sppark-ntt` at
the milestone-2 baseline `89d3112` (sppark fork `dev` at `13b6226`, built
with `SPPARK_NO_CXX_RUNTIME`), the two runs differing only in
`MULTI_STARK_CUDA_NTT=sppark`. The sppark path is the unbatched baseline:
one upstream transform launch sequence per column, simple gather and
scatter kernels, panels of up to 4 GiB. `legacy.csv` and `sppark.csv` are
the raw rows. The stored words of both paths agree bit for bit in the
multi-stark tests over 168 shapes, raw representatives included.

| Shape (log height, width, blowup) | first-party ms | sppark ms | ratio |
| --- | ---: | ---: | ---: |
| 20, 1, 2 | 0.70 | 0.67 | 1.05 |
| 20, 2, 2 | 1.20 | 1.11 | 1.08 |
| 20, 8, 2 | 3.15 | 3.23 | 0.98 |
| 18, 40, 2 | 3.94 | 4.77 | 0.82 |
| 18, 128, 2 | 14.02 | 15.89 | 0.88 |
| 18, 129, 2 | 14.06 | 15.91 | 0.88 |
| 16, 925, 2 | 24.59 | 56.78 | 0.43 |
| 18, 40, 4 | 5.65 | 6.76 | 0.84 |
| 20, 533, 4, the BLAKE3 piece | 385.93 | 314.60 | 1.23 |
| 24, 6, 4, a narrow IxVM circuit at the height cap | 169.53 | 71.29 | 2.38 |
| 24, 17, 4 | 215.45 | 218.50 | 0.99 |
| 22, 2, 4, a quotient or lookup codeword | 9.70 | 4.51 | 2.15 |
| 20, 2, 4 | 1.43 | 1.22 | 1.17 |

The blowup column is the multiplier; the benchmark's `added_bits` is its
logarithm.

What it says:

- The tall narrow shapes, where the first-party path fell to radix-2
  stages, gain 2.2 to 2.4x. Those are 4.3 of the profiled claim's 4.8 s of
  radix-2 time.
- The tall wide BLAKE3 shape gains 1.23x already, with the gather, the
  shift pass and the scatter costing about three extra passes and every
  column launched on its own.
- Short matrices lose, worst at 2^16 x 925, where 925 columns each pay a
  launch sequence for a 2^16 transform: launch-bound, not bandwidth-bound.
  Column batching in the launch grid, milestone 4's first item, is what
  those shapes need; until then a height threshold keeps them on the
  first-party path.
- 2^24 x 17 is even: the panel traffic offsets the pass reduction at that
  width.

## Whole-unit replays at milestone 3

`docs/aiur-gpu-sppark-ntt-plan.md`, "Milestones 2 and 3", has the table:
claim 1 and join 5 of the Init proof replayed with the `ix` binary linked
against multi-stark `312cbbe`, once on the first-party kernels and once
with `MULTI_STARK_CUDA_NTT=sppark`, no CUPTI. `replay-join5.txt` and
`replay-claim1.txt` hold the runs' final metrics snapshots (dispatch counts
and transform shapes per backend) and timings.
