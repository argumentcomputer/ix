# Init trace-generation comparison

The fixture is the existing `~/benchdata/init-multigpu/init.ixe` and
`init-mincut-8.ixes`: eight claims, four resident GPU workers, two execution
jobs per worker, 200 GiB per worker, 1.5 billion trace cells and maximum
piece log height 24. Keep the supplied manifest unchanged.

The previous comparable runs are `resident2/lanes.err` and
`resident3/lanes.err` in that fixture directory:

| Run | Wall time | Proving pipeline | Peak RSS |
| --- | ---: | ---: | ---: |
| Resident workers, least-loaded dispatch | 297.96 s | 295 s | 192.74 GiB |
| Resident workers, concurrent verdict | 301.95 s | 299 s | 197.50 GiB |

Both produced verified root
`6221602089142e7998ca8581617c70ae817e7bd68a8c0c510a67a1723a794024`.

`run.py` uses one frozen CUDA binary for CPU generation, GPU generation with
regeneration, and GPU generation with a 512 MiB tree allowance per batch.
Each case has a new `AIUR_LANES_CACHE_DIR`, leaving existing proof indexes
available for other runs. Every case must report eight claims and seven
joins with no cache hits, complete verification, and the same root. GPU
cases must also report actual BLAKE3 dispatch.

The script records the binary and fixture hashes, command and selected
environment, GNU time output, a one-second GPU memory/utilization sample,
trace seed volumes, and tree checkpoint/reuse/eviction counts. RSS is the
process maximum; GPU memory includes reusable CUDA pool allocations. It
uses normal CPU worker counts and the existing two execution jobs per GPU.
Debug logging is restricted to generation and checkpoint events in all
three cases. Historical runs did not have this logging.

Run against an existing CUDA build:

```sh
python3 bench/gpu-trace-init-2026-09-15/run.py \
  --ix .lake/build/bin/ix \
  --fixture-dir /home/sam/benchdata/init-multigpu \
  --output-dir /tmp/ix-init-gpu-trace-2026-09-15/comparison
```

The script never builds. It rejects a binary without GPU trace support or
the cache-directory override. `--case cpu`, `--case gpu`, or
`--case gpu-trees` restricts it to one case; each case directory must be new.

## Measurements, 2026-09-15

One run per configuration, sequentially, on four RTX PRO 6000 Blackwell
Server GPUs and 96 available CPU threads, in a `MemoryMax=900G` scope.
The frozen binary SHA-256 is
`d75a19814e60aecb1b2c65b1407f38a0beafccd7a5069906d128a9108f47559b`.
All three runs proved all eight claims and seven joins from empty caches,
completed native verification, and produced the historical root above.

| Configuration | Wall time | Change versus fresh CPU | CPU time, user + system | Peak RSS | Maximum device memory |
| --- | ---: | ---: | ---: | ---: | ---: |
| CPU traces, regenerate | 298.17 s | — | 5,664.35 s | 194.00 GiB | 65.19 GiB |
| GPU BLAKE3 traces, regenerate | 286.27 s | 4.0% faster | 4,663.33 s | 190.24 GiB | 65.32 GiB |
| GPU BLAKE3 traces, 512 MiB tree cache | 285.64 s | 4.2% faster | 4,698.36 s | 192.15 GiB | 65.41 GiB |

GPU generation saved 11.90 seconds and 17.7% of CPU time in this comparison.
Both GPU runs reported 120 generated shard sources containing 110,892,480
real rows across both rounds and all claim/join/wrap tasks. They prepared
133.85 GiB of compact seeds for traces that would occupy 467.42 GiB as
padded host matrices. These are summed preparation volumes, not measured
PCIe traffic: lookup recovery can upload seeds again.

| Milestone from the prover's start | CPU | GPU | GPU + trees |
| --- | ---: | ---: | ---: |
| All eight claim proofs complete | 137 s | 135 s | 134 s |
| Final join/root task dispatched | 234 s | 225 s | 224 s |
| Root and composed verdict complete | 296 s | 284 s | 284 s |

The cache retained 21 trees and evicted all 21 before reuse; it had **zero
hits**. Its 0.63-second difference from GPU regeneration is not evidence of
a caching benefit. The current headroom rule reserves four times the total
main LDE size, the main traces, the minimum-free allowance, and 256 MiB.
With the default allowance, a single 2^20-row, 533-column BLAKE3 matrix at
blowup four already reserves about 94.94 GiB, before other circuits and
persistent allocations, on a 95.59 GiB device. That explains why small
trees are discarded before the large first shard of round two, despite
the measured device-memory peaks near 65 GiB. No CUDA allocation failed;
these were preemptive policy decisions.

For this workload, use GPU generation with `AIUR_TREE_CACHE_BYTES=0`.
The next cache experiment needs a workspace estimate based on the actual
main, lookup, quotient and FRI shapes; increasing the byte allowance alone
will not prevent these headroom evictions. Keep the existing proof workspace
admission checks. This experiment is deferred; its proposed accounting and
validation are recorded in the
[implementation notes](../../docs/aiur-gpu-trace-generation.md).
Single-GPU and Mathlib throughput remain unmeasured, and
one trial per configuration does not establish run-to-run variation.

Raw logs, one-second GPU samples, commands, hashes, tracked-source diffs and
machine-readable measurements are in [results/](results/). The initial
runner expected older cold-cache log wording; its parser was corrected and
the completed CPU baseline was validated from the log, without repeating
proving work. The `returncode` in each result is the prover's GNU-time
wrapper status, zero for all three cases.
