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

## Whole Init proof at milestone 3

`init-q4-compare.txt`: the four-shard Init proof (`run.sh`, generated
traces, `--exec-jobs 2 --max-ram 200`, one GPU) with the milestone-3 binary,
once on the first-party kernels and once with `MULTI_STARK_CUDA_NTT=sppark`,
against the recorded coset-cache run. Same root, same verdict.

| Quantity | coset run (before) | same binary, first-party | sppark above 2^20 |
| --- | ---: | ---: | ---: |
| Wall / end to end | 418.5 / 416 s | 418.3 / 415 s | 408.0 / 405 s |
| `aiur/prove_planned` union | 223.6 s | 223.0 s | 201.1 s |
| `stark/stage1_commit` union | 115.6 s | 115.0 s | 105.5 s |
| `stark/lookup_construction` union | 48.7 s | 48.7 s | 41.5 s |
| `stark/quotient` union | 35.3 s | 35.4 s | 30.0 s |
| `stark/fri_open` union | 16.4 s | 16.4 s | 16.4 s |
| GPU utilization | 43.6% | 44.5% | 37.9% |

The proving union falls 10 percent; the end-to-end time 2.4 percent, since
the one GPU worker waits on executions and joins for much of the run.

## Column batching (milestone 4, fork `8b624cd`)

Same benchmark, multi-stark with the batched adapter, nine iterations,
medians of the warm eight, `MULTI_STARK_SPPARK_MIN_LOG_HEIGHT=1` so every
shape takes the path. Four settings: `batching-legacy.csv` (first-party),
`batching-unbatched.csv` (`MULTI_STARK_SPPARK_BATCH_BYTES=0`, one launch
sequence per column), `batching-whole-panel.csv` (every column of a panel
in one sequence, an earlier build of the same change) and
`batching-grouped.csv` (the default: groups sized to the 128 MiB L2).

| Shape (log height, width, blowup) | first-party | one per column | whole panel | grouped |
| --- | ---: | ---: | ---: | ---: |
| 20, 1, 2 | 0.71 | 0.65 | 0.68 | 0.65 |
| 20, 8, 2 | 2.94 | 3.17 | 2.94 | 3.03 |
| 18, 40, 2 | 3.87 | 4.59 | 3.75 | 3.59 |
| 18, 128, 2 | 13.89 | 15.84 | 12.18 | 11.68 |
| 16, 925, 2 | 24.45 | 52.36 | 21.39 | 20.84 |
| 18, 40, 4 | 5.56 | 5.95 | 5.25 | 4.92 |
| 20, 533, 4 | 385.34 | 343.26 | 355.34 | 335.55 |
| 24, 6, 4 | 169.56 | 62.10 | 62.99 | 62.12 |
| 24, 17, 4 | 215.14 | 203.08 | 205.83 | 203.43 |
| 22, 2, 4 | 9.60 | 3.99 | 4.28 | 4.00 |
| 20, 2, 4 | 1.41 | 1.22 | 1.21 | 1.21 |

Whole-panel batching rescues the short wide shapes but costs the tall
ones 3 to 7 percent: with every column through one stage before the next,
a column that fits the L2 loses the reuse between stages the serial path
had. Groups sized to the L2 keep both, and every shape is now at or ahead
of the first-party kernels, so the height threshold can come down; that
is measured next.

## Panel glue and the fused expansion (milestone 4, multi-stark `8a1f9f9`)

`MULTI_STARK_SPPARK_STAGE_TIMING=1` splits every LDE into its five
stages (`stages-before.txt`, `stages-after.txt`, the last panel of the
last iteration). Before, on the BLAKE3 shape (2^20 x 533, blowup 4, six
panels): gather 24 ms, inverse 22, restore-and-shift 79, forward 100,
scatter 124, of 349 ms; the three glue passes were per-element kernels with
a 64-bit division each and strided accesses. After, with tiled transposes
and a one-column-per-grid-row expansion: gather 8, inverse 13, restore 15,
forward 58, scatter 63.

The plan's fused expansion (bit-reversed coefficients spread with the coset
powers straight into a forward RN transform, the row permutation folded
into the scatter) was implemented and measured against the restoring path
with the same glue (`expansion-restoring.csv`, `expansion-fused.csv`,
`MULTI_STARK_SPPARK_FUSED`): 284 against 289 ms on the BLAKE3 shape,
62 against 73 ms on 2^24 x 6, 202 against 238 ms on 2^24 x 17. The
reversing scatter costs what the restoring pass saves, so the restoring
path is the default and the fused one stays available as evidence.

Final medians (`glue-legacy.csv`, `glue-sppark.csv`; `glue-before-sppark.csv`
is the batched build before the glue rewrite), all shapes through sppark:

| Shape (log height, width, blowup) | first-party ms | sppark ms | ratio |
| --- | ---: | ---: | ---: |
| 16, 2, 4 | 0.148 | 0.209 | 0.71 |
| 17, 16, 4 | 0.953 | 1.106 | 0.86 |
| 18, 2, 4 | 0.474 | 0.443 | 1.07 |
| 18, 40, 4 | 5.58 | 4.92 | 1.13 |
| 18, 128, 2 | 13.95 | 11.40 | 1.22 |
| 19, 2, 4 | 0.757 | 0.679 | 1.11 |
| 19, 49, 4 | 14.82 | 13.70 | 1.08 |
| 20, 2, 4 | 1.40 | 1.19 | 1.18 |
| 20, 533, 4 | 385.5 | 284.1 | 1.36 |
| 22, 2, 4 | 9.51 | 4.28 | 2.22 |
| 24, 6, 4 | 169.1 | 62.5 | 2.71 |
| 24, 17, 4 | 215.3 | 201.1 | 1.07 |

Below 2^18 input rows the first-party kernels win (0.60 to 0.91x), which
sets the default `MULTI_STARK_SPPARK_MIN_LOG_HEIGHT` at 18.
