# GPU opportunities from SP1, sp1-cluster, Zisk, and proofman

## Conclusion

There is useful work to apply to both ix and multi-stark. The strongest
remaining candidates are smaller BLAKE3 seeds, persistent GPU constraint
programs, and memory admission based on actual live allocations. CUDA graph
replay, truncated Merkle storage, and generated constraint kernels are
subsequent experiments. Several recommendations in the September 11 audits
are already implemented.

These are source-based recommendations. No builds, tests, benchmarks, or GPU
jobs were run for this review. Measurements below come from existing tracked
benchmark reports; proposed improvements have no measured speedup yet.

## Source scope

Upstream `main` references were fetched without tags in all four research
repositories; the checked-out development branch was also fetched for Zisk
and proofman. The research checkouts already matched their selected upstream
heads. Their branches and source files were left unchanged. Zisk and
proofman's development branches are the basis of the recommendations; their
default-branch references were also checked.

| Repository | Reviewed branch | Revision |
| --- | --- | --- |
| ix | `sb/aiur-trace-sharding-gpu` | `d9cb6ad9b30932407a9ed64d21a69e4a25ffb8db` |
| multi-stark | `sb/trace-sharding-gpu` | `f54b44f4cc848eb37dc0a7a05010e5a4ef3c75dc` |
| sp1 | `main` | `9ce13607e9f464b9d5ccd8b4a6478de0e8f8bf1b` |
| sp1-cluster | `main` | `2d086092f07c08fc100c7978a824c369f0b69448` |
| zisk | `pre-develop-1.3.0-alpha` | `0f122e94d3b3010bbb414704e158f1564866deb3` |
| pil2-proofman | `pre-develop-1.3.0-alpha` | `286c57d9b08a0013a5be2a0d6c959d4515408676` |

ix's Cargo pin matches the reviewed multi-stark revision. sp1-cluster pins
the SP1 crate family to release 6.8.0; its runtime should not be assumed to
track every subsequent SP1 main-branch change.

| Repository | Most useful material | Applicability |
| --- | --- | --- |
| pil2-proofman | Goldilocks transforms, packed witnesses, generated CUDA expressions, graph replay, workspace sizing and buffer lifetimes | Closest arithmetic match; substantial implementation references, with protocol and licensing differences |
| sp1 | Cached constraint bytecode, bounded evaluation chunks, truncated Merkle trees, CPU/GPU trace pipeline | Compiler and memory-management techniques transfer; the proving backend has different fields and commitments |
| zisk | GPU sorting, scans, counting, and memory-operation planning | Techniques for regular record processing; its memory-operation encoding and planner are VM-specific |
| sp1-cluster | Resource-aware task assignment, retries, cancellation, artifact admission | Runtime hardening and future distributed operation; ix already has the main single-host scheduling ideas |

## What is already implemented

- **Short-row BLAKE3 dispatch.** multi-stark uses one thread per message up
  to 1,024 bytes, retaining the wide-row path. The recorded synthetic
  commitments improved by roughly 18–21% for several narrow shapes. This
  is already in `ff3237c`; it is not a new Init/Mathlib speedup estimate.
  [BLAKE3 measurements](../../multi-stark/docs/cuda-blake3-short-rows.md)
- **Fewer LDE passes and wider use of fused NTT stages.** `f15a6c4` removes
  redundant clearing/canonicalization and enables fused stages for short,
  wide matrices. A more aggressive fusion experiment was removed because
  complete commitments did not improve consistently. Another fusion proposal
  needs a different, measurable rationale.
  [LDE measurements](../../multi-stark/docs/cuda-lde-pass-reduction.md)
- **GPU BLAKE3 trace expansion.** ix uploads seeds and expands the 533-column
  trace on the device. One four-GPU Init trial measured 298.17 s with CPU
  traces and 286.27 s with GPU traces: 4.0% less wall time and 17.7% less CPU
  time. Repeated trials, single-GPU results, and Mathlib GPU-trace results
  remain unmeasured. [Init comparison](../bench/gpu-trace-init-2026-09-15/README.md)
- **Resident workers and ready joins.** ix already has one resident worker
  per GPU, bounded CPU preparation, least-loaded dispatch, ready-join
  priority, record caps, and overlapping claim/join work. multi-stark binds
  prover configurations and host pools to devices. These should be the
  baseline when evaluating upstream scheduling ideas.
  [Resident scheduler][ix-lanes]

## Recommended experiments

### 1. Pack the existing BLAKE3 seeds — ix

Proofman's packed representation supports bounded-width fields and shared
instruction-table entries. The immediate ix opportunity is smaller and
concrete: `gpu_trace::prepare` stores each seed as 162 `u64`s, or **1,296
bytes**. It already checks that the stage is at most seven and all 160
input/output bytes are at most 255; only the multiplicity needs a full
Goldilocks word. [Packed representation][packed], [ix seed producer][ix-seeds]

A representation containing 161 bytes plus an eight-byte multiplicity needs
169 payload bytes, or **176 bytes with ordinary eight-byte struct alignment**.
That is about **7.4 times smaller**, an 86.4% reduction in seed storage and
bytes per corresponding upload. This is a layout calculation, not a
wall-time prediction. The expanded trace and its LDE remain the same size.

Preserve the recorded recursive outputs and full-width multiplicity. Generate
the packed seeds directly; creating the existing wide seeds first would keep
much of their allocation and memory-traffic cost. Update the CPU reference
writer, device decoder, and `host_bytes()` accounting together.

After packing, consider reusable pinned seed buffers and completion events.
The current seed source is an ordinary `Vec`, and its CUDA wrapper synchronizes
after every tile. Proofman's host-buffer release waits only for upload
completion, allowing the device computation to continue. Adopting that requires
an ownership/API change: returning early from the current synchronous writer
would violate its cross-thread output contract. Retained seeds also serve
lookup recovery, so releasing an upload buffer does not necessarily release
the seed source. [Current CUDA writer][ix-writer], [upload completion][upload-event]

**Effort:** small to medium for packing; medium for asynchronous ownership.
Validate every expanded cell, padding, wrapped lookup halos, forced spills,
and complete CPU/GPU proof equality.

### 2. Cache constraint programs, then specialize hot graphs — multi-stark

SP1 compiles and uploads machine-stable constraint bytecode once when the
prover is constructed. It groups constraints by shared column inputs and
uses different lowerings for general expressions and suitable linear sums.
[SP1 construction][sp1-programs], [constraint lowering][sp1-lowering]

multi-stark already has liveness-based temporary-slot reuse, but its production
quotient and lookup paths still encode static graphs during proving and upload
their descriptors for individual jobs. Its quotient kernel interprets those
operations. [Graph encoding][ms-encoding], [quotient evaluator][ms-evaluator]

First cache the encoded nodes, roots, lookup descriptors, and device uploads
per immutable circuit and device. Keep proof-specific challenges, public
values, selectors, dimensions, and trace pointers dynamic. Reuse the same
compiled liveness information for workspace estimates.

Then benchmark bounded chunks or specialized linear sums. A larger follow-up
is proofman's approach: generate straight-line CUDA expressions, split them
to control register spills, and retain an interpreter fallback. Its code
generator emits per-AIR shared libraries and can autotune chunk sizes.
[Proofman code generation][codegen]

**Effort:** medium for caching; large for a generated backend. Preserve
constraint order/challenge weights and our quadratic extension arithmetic.
Include compilation, uploads, scratch allocation, and register spills in
evaluation. Caching alone does not accelerate the underlying field operations.

### 3. Make tree-cache admission reflect live workspace — multi-stark

This is an observed local limitation. The tracked Init tree-cache run
retained 21 trees and evicted all 21 before reuse: **zero hits**. Its 0.63 s
difference from GPU regeneration does not establish a cache benefit.
[Init comparison](../bench/gpu-trace-init-2026-09-15/README.md)

The current estimate reserves `4 × main LDE + main trace + minimum-free
allowance + 256 MiB`. With the default allowance, one representative BLAKE3
matrix already implies about 94.94 GiB on a 95.59 GiB device, although the
recorded device-memory peaks were around 65 GiB. Increasing the cache limit
alone does not resolve this. [Admission code][ms-headroom]

Reuse the existing main, lookup, quotient, and FRI workspace calculations at
their allocation boundaries, including overlapping lifetimes. Make optional
trees available for eviction before spilling required LDEs. Account for
existing allocations and reusable pools once: current free memory already
excludes retained trees, so comparing the whole cache with `free - workspace`
can evict unnecessarily. Proofman's per-AIR stream-size classes and explicit
arena planning are useful references, although their formulas do not apply
directly to our proof system. [Stream layout planning][stream-layout]

**Effort:** medium. Preserve workspace admission and eviction; compare predicted
and observed peaks, require actual cache hits, and exercise regeneration after
forced eviction. Keep the current Init cache allowance at zero until this is
implemented and measured.

### 4. Replay repeated kernel sequences with CUDA graphs — multi-stark

Proofman captures selected proof phases in a per-stream graph cache after a
warmup threshold. It excludes regions that stage changing host data in ways
that replay would skip. The reviewed multi-stark CUDA backend has no graph
capture/replay path. [Graph cache][graphs], [phase boundaries][graph-phases]

Candidate regions are repeated LDE/commit or constraint-evaluation sequences
with the same shape. Start with a single region after program caching and
stable workspace ownership. Changing pointers and launch parameters require
updates or recapture; transcript challenges must still be consumed at the
correct boundaries. [CUDA graph update semantics](https://docs.nvidia.com/cuda/cuda-programming-guide/04-special-topics/cuda-graphs.html#updating-instantiated-graphs)

**Effort:** medium to large. Measure launch/host overhead first. Graph replay
will have limited impact when arithmetic, memory bandwidth, or CPU execution
dominates, and short cold runs may not amortize capture costs.

## Larger or conditional opportunities

### Truncated Merkle storage and streamed commitments

SP1 retains only upper Merkle levels for sufficiently tall trees, dropping
eight bottom levels and reconstructing a 256-leaf subtree per query. This
reduces retained digest storage by approximately 256 times, not total prover
memory. It first constructs the full tree, so its implementation does not
remove the construction peak. [Storage policy][sp1-tree], [opening reconstruction][sp1-open]

multi-stark could independently implement this while preserving roots and
openings. Mixed-height commitments must reproduce every matrix injection;
queried leaf values must remain accessible or reproducible. Tree-cache
admission must be corrected first: shrinking tree buffers does not cure an
estimate that gives the cache zero headroom.

Proofman also computes first-round roots by streaming column groups through
LDE and hashing. multi-stark's `Retention::Regenerate` currently builds full
stage-one state and discards it after extracting the header. A commitment-only
API could reduce the first-round working set. However, proofman's reviewed
streaming path caps inputs at **64 columns**, while ix's BLAKE3 trace alone has
533 columns; adapting it is a substantial change. It does not remove
round-two workspace requirements. [Streaming implementation][stream-commit],
[batch first round][ms-batch]

Proofman's column-major, L2-sized NTT groups and virtual zero padding are also
worth a bounded comparison if transforms remain a bottleneck. Include the
cost of converting multi-stark's row-major, bit-reversed layout. The existing
failed fusion experiment rules out assuming a win from fewer launches alone.
[Proofman LDE][ntt]

### GPU record processing — ix, informed by Zisk

Zisk feeds memory-operation records through CUDA decode/count kernels, CUB
prefix scans, radix sort, run-length encoding, and per-address processing.
The GPU produces segment metadata; the CPU planner still owns the final plan.
[GPU processing][zisk-plan], [Rust wrapper][zisk-wrapper]

The transferable candidates are measured CPU bottlenecks involving flat
records: filtering/compaction, row offsets, byte/range-table histograms, and
lookup multiplicities. Each needs an Aiur-specific implementation and exact
ordering/count semantics. It is not a portable GPU implementation of Aiur's
recursive execution, memoization, or type checking.

Zisk pauses streaming commitments before its latency-sensitive final GPU
planning phase. This is useful evidence that more concurrent GPU work can
delay the critical path. Evaluate complete proof latency when adding such
overlap. [Planning coordination][zisk-pause]

### Scheduling and reliability — ix, informed by sp1-cluster/proofman

sp1-cluster chooses workers using capacity and predicted availability, budgets
worker RAM/shared memory, and has explicit task-attempt and artifact-publication
lifecycles. Its duration estimates are coarse constants. These are useful
references for measured-cost scheduling, cancellation/retry handling, and
budgeting queued artifact bytes. [Assignment][cluster-policy],
[worker admission][cluster-limiter], [artifact admission][cluster-artifacts]

ix already dispatches ready work dynamically and prioritizes joins. The next
scheduling experiment, if a profile shows a long tail, is cost/critical-path
priority within the existing scheduler. Proofman's resident-key affinity can
help only where there is a meaningful reload cost; ix already keeps its IxVM
and aggregation systems resident on each worker. [Affinity scheduler][affinity]

Retries and atomic publication primarily improve reliability. The cluster
service stack does not by itself accelerate a four-GPU local proof. Preserve
multi-stark's ordered all-header transcript barrier and the predetermined
aggregation tree under any scheduling changes.

## Reuse boundaries

- SP1 uses KoalaBear, a degree-four extension, Poseidon-based commitments,
  and Hypercube/jagged multilinear machinery. Its cuPQC adapter explicitly
  selects 32-bit KoalaBear. These are not direct replacements for
  multi-stark's Goldilocks/quadratic-extension/BLAKE3 backend.
  [SP1 field configuration][sp1-field], [cuPQC adapter][cupqc],
  [multi-stark configuration][ms-types]
- Proofman shares the Goldilocks base field, but its expression backend uses
  a cubic extension and its BLAKE3 digest packing reduces output words into
  Goldilocks elements. multi-stark must preserve raw BLAKE3 digest bytes,
  its extension field, transcript, layout, and verifier behavior.
  [Digest packing][digest-pack], [cubic extension][cubic]
- File-level provenance matters for copying code: proofman's root manifest
  declares MIT/Apache, while `pil2-stark` and its nested Goldilocks directory
  contain AGPL-3.0-or-later notices. Those notices need to be resolved for
  any direct kernel reuse. The recommendations above concern techniques
  that can be implemented in the existing backend.
  [CUDA subtree license][proofman-license], [Goldilocks license][goldilocks-license]

## Suggested order

1. Pack BLAKE3 seeds and retain the existing synchronous behavior initially.
2. Cache immutable constraint programs per circuit/device.
3. Correct tree-cache workspace estimates and measure real reuse.
4. Use a fresh profile to choose between generated constraints, graph replay,
   and additional GPU trace/record processing.
5. Pursue truncated trees, streaming commitments, or layout changes when
   retained memory or transfer volume is demonstrably limiting.

For every promoted change, require complete proof verification and the same
protocol outputs. Record cold/warm wall time, CPU time, host/VRAM peaks,
transfer bytes, and cache hit/eviction counts on the fixed Init fixture before
drawing conclusions about Mathlib.

[ix-lanes]: https://github.com/argumentcomputer/ix/blob/d9cb6ad9b30932407a9ed64d21a69e4a25ffb8db/crates/ffi/src/aiur/aggregate/lanes.rs#L739
[ix-seeds]: https://github.com/argumentcomputer/ix/blob/d9cb6ad9b30932407a9ed64d21a69e4a25ffb8db/crates/aiur/src/gpu_trace/mod.rs#L77
[ix-writer]: https://github.com/argumentcomputer/ix/blob/d9cb6ad9b30932407a9ed64d21a69e4a25ffb8db/crates/aiur/cuda/blake3_trace.cu#L97
[ms-encoding]: https://github.com/argumentcomputer/multi-stark/blob/f54b44f4cc848eb37dc0a7a05010e5a4ef3c75dc/src/cuda/mod.rs#L1216
[ms-evaluator]: https://github.com/argumentcomputer/multi-stark/blob/f54b44f4cc848eb37dc0a7a05010e5a4ef3c75dc/cuda/kernels.cu#L1358
[ms-headroom]: https://github.com/argumentcomputer/multi-stark/blob/f54b44f4cc848eb37dc0a7a05010e5a4ef3c75dc/src/cuda/witness.rs#L78
[ms-batch]: https://github.com/argumentcomputer/multi-stark/blob/f54b44f4cc848eb37dc0a7a05010e5a4ef3c75dc/src/batch.rs#L535
[ms-types]: https://github.com/argumentcomputer/multi-stark/blob/f54b44f4cc848eb37dc0a7a05010e5a4ef3c75dc/src/types.rs#L36
[packed]: https://github.com/0xPolygonHermez/pil2-proofman/blob/286c57d9b08a0013a5be2a0d6c959d4515408676/common/src/packed_info.rs#L22
[upload-event]: https://github.com/0xPolygonHermez/pil2-proofman/blob/286c57d9b08a0013a5be2a0d6c959d4515408676/pil2-stark/src/api/starks_api.cu#L123
[codegen]: https://github.com/0xPolygonHermez/pil2-proofman/blob/286c57d9b08a0013a5be2a0d6c959d4515408676/setup/exps-codegen/src/lib.rs#L1
[stream-layout]: https://github.com/0xPolygonHermez/pil2-proofman/blob/286c57d9b08a0013a5be2a0d6c959d4515408676/common/src/gpu_stream_layout.rs#L112
[graphs]: https://github.com/0xPolygonHermez/pil2-proofman/blob/286c57d9b08a0013a5be2a0d6c959d4515408676/pil2-stark/src/utils/cuda_graph_cache.cuh#L38
[graph-phases]: https://github.com/0xPolygonHermez/pil2-proofman/blob/286c57d9b08a0013a5be2a0d6c959d4515408676/pil2-stark/src/starkpil/gen_proof.cuh#L265
[stream-commit]: https://github.com/0xPolygonHermez/pil2-proofman/blob/286c57d9b08a0013a5be2a0d6c959d4515408676/pil2-stark/src/goldilocks/src/stream_commit.cu#L383
[ntt]: https://github.com/0xPolygonHermez/pil2-proofman/blob/286c57d9b08a0013a5be2a0d6c959d4515408676/pil2-stark/src/goldilocks/src/ntt_goldilocks.cu#L1453
[affinity]: https://github.com/0xPolygonHermez/pil2-proofman/blob/286c57d9b08a0013a5be2a0d6c959d4515408676/proofman/src/scheduler.rs#L1
[digest-pack]: https://github.com/0xPolygonHermez/pil2-proofman/blob/286c57d9b08a0013a5be2a0d6c959d4515408676/pil2-stark/src/goldilocks/src/blake3_core.hpp#L195
[cubic]: https://github.com/0xPolygonHermez/pil2-proofman/blob/286c57d9b08a0013a5be2a0d6c959d4515408676/pil2-stark/src/goldilocks/src/goldilocks_cubic_extension.cuh#L23
[proofman-license]: https://github.com/0xPolygonHermez/pil2-proofman/blob/286c57d9b08a0013a5be2a0d6c959d4515408676/pil2-stark/LICENSE
[goldilocks-license]: https://github.com/0xPolygonHermez/pil2-proofman/blob/286c57d9b08a0013a5be2a0d6c959d4515408676/pil2-stark/src/goldilocks/LICENSE
[sp1-programs]: https://github.com/succinctlabs/sp1/blob/9ce13607e9f464b9d5ccd8b4a6478de0e8f8bf1b/sp1-gpu/crates/shard_prover/src/prover.rs#L83
[sp1-lowering]: https://github.com/succinctlabs/sp1/blob/9ce13607e9f464b9d5ccd8b4a6478de0e8f8bf1b/sp1-gpu/crates/zerocheck/src/prover.rs#L92
[sp1-tree]: https://github.com/succinctlabs/sp1/blob/9ce13607e9f464b9d5ccd8b4a6478de0e8f8bf1b/sp1-gpu/crates/merkle_tree/src/tree.rs#L20
[sp1-open]: https://github.com/succinctlabs/sp1/blob/9ce13607e9f464b9d5ccd8b4a6478de0e8f8bf1b/sp1-gpu/crates/merkle_tree/src/single_layer.rs#L149
[sp1-field]: https://github.com/succinctlabs/sp1/blob/9ce13607e9f464b9d5ccd8b4a6478de0e8f8bf1b/crates/primitives/src/lib.rs#L28
[cupqc]: https://github.com/succinctlabs/sp1/blob/9ce13607e9f464b9d5ccd8b4a6478de0e8f8bf1b/sp1-gpu/crates/sys/include/ntt/nvidia.cuh#L12
[zisk-plan]: https://github.com/0xPolygonHermez/zisk/blob/0f122e94d3b3010bbb414704e158f1564866deb3/state-machines/mem-cpp/cu/count_and_plan.cu#L1434
[zisk-wrapper]: https://github.com/0xPolygonHermez/zisk/blob/0f122e94d3b3010bbb414704e158f1564866deb3/state-machines/mem-cpp/src/gpu_count_and_plan.rs#L23
[zisk-pause]: https://github.com/0xPolygonHermez/zisk/blob/0f122e94d3b3010bbb414704e158f1564866deb3/emulator-asm/asm-runner/src/asm_mo_runner.rs#L375
[cluster-policy]: https://github.com/succinctlabs/sp1-cluster/blob/2d086092f07c08fc100c7978a824c369f0b69448/bin/coordinator/src/policy/balanced.rs#L89
[cluster-limiter]: https://github.com/succinctlabs/sp1-cluster/blob/2d086092f07c08fc100c7978a824c369f0b69448/crates/worker/src/limiter.rs#L1
[cluster-artifacts]: https://github.com/succinctlabs/sp1-cluster/blob/2d086092f07c08fc100c7978a824c369f0b69448/crates/artifact/src/redis.rs#L147
