# Anthropic FLT shard count from the Mathlib calibration

**Result (2026-09-17):** the Anthropic FLT environment (1,330,204
constants, 30.1 GB `.ixe`) is cut into **572 shards** by scaling the
p90-calibrated Mathlib cut by serialized block bytes, without a seed run.
The trace-shard seed model would have cut 3,631; its per-block `size^1.5`
term is 93% of FLT's score and does not describe FLT's records. The
byte-balanced 572-way cut isolates each of the five oversized
single-constant blocks in a shard of its own, so no ceiling refinement is
expected at run time. The five outlier leaves were proven on one GPU
(below); the full 572-shard run has not been made.

## Formula

```text
C = 78 × B_FLT / B_Mathlib = 78 × 10.770 GB / 1.468 GB = 572
```

`B` is the sum of block `serialized_size` over an `.ixe`, read from
`ix shard graph`. 78 is Mathlib's calibrated count at
`--lanes 4 --exec-jobs 3 --max-ram 230` (`../mathlib-seed-2026-09-15`,
run 3): the p90-scaled candidate `ceil(shards × p90 / reservation)` of the
111-shard seed, confirmed by its own run. The formula reproduces Mathlib's
bytes per shard, 18.8 MB, and therefore its claim-record distribution
(mean 29.3 GiB, p90 33.9 GiB against the 36.5 GiB initial reservation,
pool peak 691 of 731 GiB).

### Why bytes

Every measured record agrees on about 1,700 bytes of retained record per
serialized byte, from Mathlib's ordinary shards to FLT's single-constant
outliers (`bench/record-ceiling-2026-09-15`, the FLT probe):

| Point | Serialized bytes | Record | Record bytes per byte |
| --- | ---: | ---: | ---: |
| Mathlib 78 shards, mean claim | 18.8 MB | 29.3 GiB | 1,672 |
| Mathlib 111 shards, mean claim | 13.2 MB | 21.3 GiB | 1,730 |
| FLT largest block, one constant | 58.5 MB | 89.5 GiB | 1,643 |
| FLT second block, one constant | 44.1 MB | 71.4 GiB | 1,740 |

The alternatives bracket the same number: Mathlib's own fixed-point
candidate of 73 gives 536, and the p90 rescale applied to the seed
model's linear term alone (`111 × 3.037e14 / 4.140e13 × 25.4 / 36.5`)
gives 570.

### Why not the score-based seed

The CUDA-build seed in `gpu_seed_shards` now implements the formula above
(reference 78 shards at 1,468,041,216 Mathlib bytes and a 41.4 GiB share),
so `ix shard --max-ram 230 --exec-jobs 3` seeds 78 for Mathlib and 572 for
FLT without a count on the command line. Before that change it seeded
`round(128 × (score / 1.271e14) × (35.8 GiB / 41.4 GiB))`
(`crates/kernel/src/shard.rs`, `gpu_seed_shards`), where
`score = Σ 28,201·s + 681.08·s^1.5` over block sizes. The score is fitted
on Init and validated on Std and Mathlib, whose largest block is 612 KB.
FLT has 489 blocks over 1 MB and 11 over 10 MB:

| Environment | Blocks | Σ bytes | Linear term | Superlinear term | Score | Seed |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Mathlib | 663,254 | 1.468 GB | 4.140e13 | 8.565e13 | 1.271e14 | 111 |
| Anthropic FLT | 1,310,054 | 10.770 GB | 3.037e14 | 3.865e15 | 4.169e15 | 3,631 |

Sixty percent of FLT's superlinear term comes from the 489 blocks over
1 MB (12% of the bytes), and 29% from the 11 over 10 MB. The record
ceiling probe measured those blocks' records at two orders of magnitude
below the static predictor, so the superlinear term over-counts exactly
the blocks that dominate it.

FLT block sizes by decade (share of the superlinear term):

| Size | Blocks | Bytes | Superlinear share |
| --- | ---: | ---: | ---: |
| 100 B to 1 KB | 362,848 | 0.21 GB | 0.1% |
| 1 KB to 10 KB | 765,520 | 2.63 GB | 3.1% |
| 10 KB to 100 KB | 163,479 | 4.17 GB | 13.7% |
| 100 KB to 1 MB | 11,299 | 2.44 GB | 22.9% |
| 1 MB to 10 MB | 478 | 1.05 GB | 31.6% |
| 10 MB to 100 MB | 11 | 0.28 GB | 28.6% |

Largest blocks, bytes: 58,490,064; 44,056,231; 40,021,911; 36,666,706;
28,065,203; 14,313,507; 13,630,009; 13,063,183; 10,982,286; 10,927,000;
10,245,181. Each is a single constant.

## The cut

`ix shard anthropic-flt.ixe --shards 572` (static strategy, min-cut
layout, balance ±5%): 170.8 s partition, 3:20 wall, 20 GiB peak RSS.

| Quantity | Value |
| --- | ---: |
| Bytes per shard min / mean / max | 2,730 / 18,828,273 / 58,490,064 |
| Byte imbalance max/mean | 3.11× (the largest atomic block) |
| Cross-shard ingress total / max per shard | 3.91 GB / 59.0 MB |
| Rebalance moves | 0 |
| Predicted FFT per shard mean / max | 7.548e12 / 3.063e14 |

The rebalance pass makes no moves because the hottest shard under the
static model is always an atomic single-constant leaf, which no move
improves. The partition is therefore the byte-balanced recursive min-cut,
with blocks at or above the ideal per-shard bytes (18.8 MB) capped at one
shard's balance weight.

Leaf shapes from `ix shard claims`:

| Blocks per leaf | Leaves |
| --- | ---: |
| 1 | 5 (leaves 357, 404, 528, 529, 560) |
| 2 to 10 | 7 |
| 11 to 100 | 27 |
| more than 100 | 533 |

The five single-block leaves are the five blocks above the cap. Their
predicted records at 1,700 bytes per byte are about 92, 70, 63, 58 and
45 GiB: over the 36.5 GiB reservation, under the 128 GiB per-record
ceiling, growing from the 731 GiB pool. A single constant is atomic, so
the ceiling refinement could not split them anyway. The 10 to 14 MB
blocks sit in leaves of 2 to 18 blocks, as the cap predicts, with records
in the 20 to 30 GiB range.

## The five outlier leaves, proven on one GPU

`ix prove --shards 357,404,528,529,560 --trace-shards --max-ram 230
--exec-jobs 1` on GPU 0 with generated traces: all five proven and
persisted in 34:07 wall (544 s of environment load and setup, then a
1,505 s prove-ahead pipeline), 163 GiB peak RSS, 6,431 s user CPU. Run
directory `~/benchdata/flt/runs/five-singletons-gpu0` (stdout with the
claim and proof addresses, stderr, `spans.jsonl`, `gpu.csv`).

| Leaf | Block | Record | Execution | Trace shards | Proof | Per trace shard | GPU util in proof | Device peak |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 357 | 58.5 MB | 89.46 GiB | 522.8 s | 56 | 179.6 s | 3.21 s | 65% | 64.6 GiB |
| 404 | 44.1 MB | 71.40 GiB | 394.3 s | 42 | 138.1 s | 3.29 s | 65% | 64.7 GiB |
| 528 | | 43.78 GiB | 209.4 s | 21 | 89.2 s | 4.25 s | 64% | 64.8 GiB |
| 529 | | 27.16 GiB | 97.1 s | 12 | 45.5 s | 3.79 s | 65% | 64.7 GiB |
| 560 | | 41.95 GiB | 196.2 s | 21 | 85.3 s | 4.06 s | 74% | 64.8 GiB |

Leaves 357 and 404 are the 58.5 and 44.1 MB blocks: their records
reproduce the record-ceiling probe's 89.5 and 71.4 GiB. The other three
hold the 40.0, 36.7 and 28.1 MB blocks in an order the run does not
print. Execution consumed record bytes at 184 to 300 MB/s, faster on the
smaller leaves. Every trace-shard batch regenerated stage one for round
two; the projected host peak of the heaviest trace shard was 186.7 GB
for leaf 357 and 114.8 to 165.8 GB for the others, against the 230 GiB
budget. No record approached the 128 GiB ceiling.

Phase unions inside each proof, seconds, from `spans.jsonl`
(`bench/aiur-trace-init-2026-09-16/spans.py`); phases overlap and do
not add to the proof time:

| Leaf | Round one | Round two | Stage-one commit | Host witness | Seed prep | Lookup construction | Quotient | FRI and open |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 357 | 42.2 | 135.2 | 82.2 | 47.3 | 32.8 | 36.3 | 25.4 | 32.3 |
| 404 | 31.9 | 104.6 | 61.1 | 30.8 | 29.2 | 29.2 | 19.5 | 24.2 |
| 528 | 22.8 | 66.0 | 44.4 | 22.5 | 11.7 | 17.7 | 12.7 | 13.0 |
| 529 | 11.7 | 33.5 | 21.3 | 8.3 | 7.5 | 9.0 | 5.8 | 7.4 |
| 560 | 21.7 | 63.2 | 42.3 | 22.5 | 11.2 | 16.7 | 12.4 | 12.5 |

Round two is about three quarters of every proof and stage-one commit
about 45%, the same shape as the Mathlib and FLT-join profiles. Proof
time is close to linear in the trace-shard count at 3.2 to 4.3 s per
trace shard, and execution is 2.1 to 2.9 times the proof for every leaf.

With one execution ahead of the prover the pipeline was execution-bound:
executions total 1,420 s against 538 s of proving, the GPU was busy 36%
of the pipeline, and it idled 215, 71, 8 and 151 s between proofs
waiting for the next execution. Inside the proofs sampled utilization
was 64 to 74% with 64.8 GiB peak device memory of 96. These leaves are
the worst case for the execution-to-proof ratio; the lanes run keeps
three executions ahead of each prover for exactly this reason.

### Byte model against the measured records

| Block | Predicted at 1,700 B/B | Measured |
| ---: | ---: | ---: |
| 58.5 MB | 92.6 GiB | 89.46 GiB |
| 44.1 MB | 69.8 GiB | 71.40 GiB |
| 40.0, 36.7, 28.1 MB together | 165.8 GiB | 112.9 GiB |

The two largest blocks fit the model within 4%; the three smaller
outliers came in at 795 to 1,605 bytes per byte, so the model
over-predicts the tail, in the conservative direction for the pool.
The shard count itself rests on the mean over ordinary shards, which
Mathlib pins at about 1,700; the first lanes run's calibration line will
say whether FLT's ordinary shards agree.

## Expected run

From a directory holding the inputs, as in the Mathlib runbook
(`docs/aiur-multi-gpu-design.md` §4):

```sh
export AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24
export AIUR_TRACE_SHARD_MAX_CELLS=1500000000 AIUR_GPU_TRACE=generated
systemd-run --user --scope -q -p MemoryMax=920G -- \
  ix prove --ixe anthropic-flt.ixe --ixes anthropic-flt-572.ixes \
    --trace-shards --lanes 4 --exec-jobs 3 --max-ram 230 > lanes.out 2> lanes.err
```

`--exec-jobs 3` stays: Mathlib claim execution ran about three times the
proof (179 s against 60 s at 111 shards, 247 s against 86 s at 78), so
three executions ahead of each prover is the minimum that keeps a GPU
busy; two would idle each GPU about a third of the time. The
`[lanes] calibration:` line at the end reports the measured claim p90 and
its own candidate count, which is the check on 572; a candidate near 572
with no growth waits confirms the byte model, and a resumed run does not
print one.

## Inputs and build

| Item | Value |
| --- | --- |
| `anthropic-flt.ixe` | sha256 `5251edf00c0050d766702cd32d777b30889c167f4e0021b5ba89496abbb2f4d8`, 30,113,168,066 bytes, 1,330,204 constants; `ix compile --no-build Benchmarks/Compile/CompileAnthropicFLT.lean`, 338 s (6:17 wall), 150 GiB peak RSS |
| `anthropic-flt-572.ixes` | sha256 `1207ceb0bddd165ac263f94e6e79dc3e7a8dfb04a1cf598da20e6c7be3ee2d6b`, 126,745,073 bytes |
| `anthropic-flt-seed.ixes` | sha256 `0e986e6c1d289ebf1ef58b60a0ef8424132645349594973dd43c2c834823aaf1`, the discarded 3,631-shard seed cut, 3:34 wall |
| `mathlib.ixe` | sha256 `d84ece558d434574f7d382d2a4c854a4a00d31958fdc08161f34d14ce5f6fde0`, byte-identical to the four-GPU bench's input; 60 s compile, 21 GiB peak RSS; its seed line reproduces score 1.271e14 and 111 shards |
| `ix` | sha256 `5941c403a299a52b8327e00f2a80a561ab118be8b9d0d44dee3e74886afda0ab`; ix `ec6cf69b`, multi-stark `d557aa7`; features `parallel,cuda,cuda-trace-codegen,net` |
| Build | `IX_CUDA=1 IX_CUDA_TRACE_CODEGEN=1 NVCC=/usr/local/cuda/bin/nvcc CUDA_HOME=/usr/local/cuda MULTI_STARK_CUDA_ARCHS=120 CFLAGS=-std=gnu17 lake build ix` in the repository's `nix develop` shell (Lean 4.33.1, rust 1.98.1, clang 21.1.2) with the host's CUDA 13.3 nvcc and driver 595.91.07 |
| Host | 4× RTX PRO 6000 Blackwell Server Edition, 96 CPUs, 999 GiB; THP `always`, defrag `defer+madvise` |
| FLT oleans | restored from the private S3 cache per `docs/anthropic-flt-lake-cache.md` |

The fixtures live in `~/benchdata/flt/` and `~/benchdata/mathlib/` on the
four-GPU box.

## Reproduce

```sh
ix compile --no-build Benchmarks/Compile/CompileAnthropicFLT.lean --out anthropic-flt.ixe
ix compile --no-build Benchmarks/Compile/CompileMathlib.lean --out mathlib.ixe
ix shard graph anthropic-flt.ixe --out anthropic-flt.graph
ix shard graph mathlib.ixe --out mathlib.graph
```

Byte totals and the score decomposition from a graph dump
(`block <hash> <bytes> <consts>` lines):

```sh
grep '^block ' anthropic-flt.graph | awk '{n++; s+=$3; sl+=$3*sqrt($3)}
  END {printf "blocks %d bytes %.4e linear %.4e superlinear %.4e score %.4e\n",
       n, s, 28201*s, 681.08*sl, 28201*s+681.08*sl}'
```

Then the cut and the leaf shapes:

```sh
AIUR_TRACE_SHARD_MAX_CELLS=1500000000 \
  ix shard anthropic-flt.ixe --max-ram 230 --exec-jobs 3 --out anthropic-flt-572.ixes   # seeds 572
ix shard claims anthropic-flt.ixe --ixes anthropic-flt-572.ixes | awk '$3==1'
```

`--shards 572` gives the same partition; the seed line prints the byte
total and the arithmetic.
