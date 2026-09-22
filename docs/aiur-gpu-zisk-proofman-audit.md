# Zisk and proofman GPU adoption audit

> **Status (2026-09-11, end of day):** still applicable, same caveat as the SP1 audit: reviewed at ix `3a673630` / multi-stark `ac144be2`; the surrounding pipeline is now env-shard claims (`docs/aiur-gpu-plan-status.md`), the per-proof recommendations stand.

2026-09-11. Source review of the requested `pre-develop-1.3.0-alpha`
branches, compared with the current Aiur GPU implementation. No builds,
tests, benchmarks, or GPU jobs were run for this audit. The recommendations
below are implementation opportunities, not measured speedups.

| Repository | Reviewed revision |
| --- | --- |
| ix, `sb/aiur-trace-sharding-gpu` | `3a67363049ceddfe797958e9f2fb2467e5ca79a4` |
| multi-stark, pinned by ix | [`ac144be2eb670aa081ec3800614454f3c036b7b5`][ms] |
| Zisk, `pre-develop-1.3.0-alpha` | [`77ed339416cb0a000a7c10fd4afa6a67b690da1e`][zisk] |
| pil2-proofman, `pre-develop-1.3.0-alpha` | [`d2f43760c3b89e264fdf5d0e3bd9419d5b564a3c`][proofman] |

**There are useful ideas to adopt. Start with BLAKE3 dispatch by row width
and LDE memory-traffic reductions.** Packed witnesses, generated CUDA
constraints, and streamed first-round commitments offer broader changes
with larger integration costs. These code experiments have a clearer
performance rationale than an Ubuntu, NVIDIA driver, or CUDA upgrade alone;
this audit does not establish toolchain compatibility or quantify either
kind of improvement.

The existing v2 round-one profile attributes 43.0% of accumulated kernel
time to BLAKE3 row hashing and 41.1% to radix-8 NTT stages. Those figures
motivate the first experiments; they are not a current whole-prover wall-time
breakdown. See the [earlier upstream review](aiur-gpu-upstream-review.md)
and [current GPU status](aiur-gpu-plan-status.md) for the measurement context.

1. **Fuse LDE operations and keep transform work in cache.**

   Proofman's production NTT uses column-major storage, processes column
   groups sized to fit approximately 60% of L2, and folds coset shifting
   and virtual zero padding into transform loads. Its shared-memory exchange
   also pads rows to reduce bank conflicts. The older tiled implementation
   in the same file is retained as a reference; it is not the production
   dispatch. [Upstream NTT implementation][ntt]

   Our [resident LDE path][ms-lde] explicitly clears the extended matrix,
   copies the input, and runs separate inverse-transform, bit-reversal/scale/
   shift, forward-transform, and canonicalization operations. Reducing those
   full-buffer passes is a concrete opportunity.

   Start at `multi_stark_cuda_coset_lde_create`, preserving its resident
   interface. Adopt fusion first, then compare column grouping including
   gather/scatter costs. Preserve normalized inverse transforms, the actual
   domain coset, canonical Goldilocks outputs, and our row-major,
   bit-reversed evaluation order. Expand to lookup, quotient, or FRI
   transforms only after validating this boundary.

2. **Dispatch BLAKE3 differently for short and wide rows.**

   Our [row-hashing kernel][ms-blake3] assigns a warp to each message, with
   one lane per 1-KiB chunk. A message of at most 1 KiB therefore uses only
   one lane for compression. Proofman assigns one thread per row and gathers
   inputs according to their layout. A specialized short-row kernel is a
   bounded experiment; retain parallel chunk processing for wide rows.
   [Upstream row hashing][blake3]

   Coalescing must be measured: proofman's column-major storage makes
   adjacent row threads read adjacent values, while our inputs have different
   layouts. We already specialize Merkle parent hashing, so that alone is
   not a new adoption opportunity.

   **Preserve our raw BLAKE3 digests.** Proofman's `pack4` reduces the four
   output words into Goldilocks elements; our commitments use the raw
   32-byte digest. Adapting its implementation requires preserving our
   serialization, parent hashing, mixed-height commitments, and transcript
   semantics. [Upstream digest conversion][blake3-pack]

3. **Produce compact witnesses directly into reusable pinned buffers.**

   Proofman combines long-lived pinned host pools with packed traces. Its
   indexed representation can reference a shared instruction table instead
   of repeating static fields in every row. Our [upload staging][ms-upload]
   already uses persistent pinned buffers, but still copies pageable traces
   into them before transfer. [Pinned pools][pinned], [packed representation][packed]

   The useful change is at witness production: generate compact data into
   reusable pinned buffers, transfer it, and unpack on the GPU. Packing
   after materializing the full trace retains much of the CPU and host-RAM
   cost. Narrow only fields with established value bounds; arbitrary
   Goldilocks elements still need their full representation.

   Buffer ownership must extend through upload completion, and registered
   buffers must not move or reallocate. Prioritize this when a fresh profile
   shows staging, transfer, or host-memory pressure limiting the pipeline.
   The existing per-upload waits do not imply that every GPU stream is idle.

4. **Compile stable constraint graphs into CUDA kernels.**

   Proofman generates straight-line GPU expressions, splits large expressions
   to control register pressure, and retains an interpreter fallback. Our
   production [quotient evaluator][ms-constraints] still interprets operations,
   but its [encoder][ms-constraint-encoding] already reuses temporary slots by
   liveness; lookup evaluation does likewise. Generated CUDA would target the
   remaining interpreter and memory overhead. [Upstream code generator][codegen]

   Our graph representation provides a starting point for generated quotient
   and lookup kernels. Cache compilation by graph, device architecture,
   toolchain, and layout; retain the generic evaluator for unsupported cases.
   Measure register spills and include compilation/setup cost in cold runs.
   This optimizes constraint evaluation, not the VM execution that produces
   its initial records.

   The [SP1 follow-up audit](aiur-gpu-sp1-audit.md) adds an intermediate option:
   cache GPU bytecode across shards, group constraints by shared inputs, and
   specialize suitable linear sums before adopting full CUDA code generation.

5. **Add a commitment-only first pass for `Retention::Regenerate`.**

   Our [batch first round][ms-batch] constructs full stage-one state, extracts
   the header, and then discards that state under regeneration. Proofman can
   stream column groups through LDE and hashing, returning a commitment root
   without retaining the complete LDE. [Streaming implementation][stream]

   A header-only path could reduce first-round VRAM pressure. It must still
   produce the same claims, metadata, and mixed-height commitment as the
   existing path. Round two already checks that regenerated headers match.

   Proofman's current streaming implementation limits traces to 64 columns.
   Its caller uses it selectively while Zisk's memory planner occupies the
   normal prover arena, then prefers the ordinary resident path once that
   arena is available. Adapting it to our wider traces requires additional
   work. It does not remove round-two workspace requirements or automatically
   permit larger shards. [Upstream selection policy][stream-policy]

6. **Move regular witness expansion and record processing onto the GPU.**

   Proofman uploads compact recursive witnesses and reconstructs derived
   BLAKE3/Poseidon trace columns on-device, ordered after the upload in the
   same stream. Zisk separately accelerates memory-operation processing with
   sorting, scans, and counting. [Recursive expansion][expansion],
   [compact witness widening][widen], [Zisk memory processing][mem-plan]

   These suggest selective GPU work on our hash gadgets, lookup
   multiplicities, and other flat record-processing steps. Each needs our
   own circuit-specific implementation. Preserve padding values and lookup
   counts, which participate in commitments and proof checks. This is a
   larger follow-on project and does not establish that arbitrary Aiur
   execution can move to the GPU.

**Scheduling should protect the critical path.** Zisk explicitly pauses
streaming commitments during latency-sensitive GPU memory planning because
concurrent commitment kernels delay that phase. The local branch already
implements Stage 2 lookahead in `prove_range_level`; adding lookahead is
therefore not a new recommendation from this audit. Further overlap should
be judged by complete proof latency and memory use. [Zisk coordination][coordination],
[local aggregation implementation](../crates/ffi/src/aiur/aggregate.rs)

**Validation and adoption order:**

- Begin with short-row BLAKE3 dispatch and fused LDE loads as separate,
  bounded comparisons against the existing backend.
- Check exact digest, LDE, commitment, and proof equality against the existing
  implementation, plus final verification. Include short and wide rows,
  chunk boundaries, field-reduction edge cases, different cosets/blowups,
  and mixed-height commitments as appropriate to the changed path.
- Measure representative complete proofs, including Stage 2 and final root,
  as well as kernel timings. Record cold setup time, host RAM, peak VRAM,
  transfers, and layout-conversion overhead. Keep the workload and toolchain
  fixed when comparing a kernel change.
- Promote compact witness production when transfer or memory measurements
  justify it; pursue compiled constraints when quotient/lookup evaluation
  is material. Treat streamed commitments primarily as a first-round memory
  optimization and GPU witness expansion as a larger project.

[ms]: https://github.com/argumentcomputer/multi-stark/tree/ac144be2eb670aa081ec3800614454f3c036b7b5
[zisk]: https://github.com/0xPolygonHermez/zisk/tree/77ed339416cb0a000a7c10fd4afa6a67b690da1e
[proofman]: https://github.com/0xPolygonHermez/pil2-proofman/tree/d2f43760c3b89e264fdf5d0e3bd9419d5b564a3c
[ntt]: https://github.com/0xPolygonHermez/pil2-proofman/blob/d2f43760c3b89e264fdf5d0e3bd9419d5b564a3c/pil2-stark/src/goldilocks/src/ntt_goldilocks.cu#L667
[ms-lde]: https://github.com/argumentcomputer/multi-stark/blob/ac144be2eb670aa081ec3800614454f3c036b7b5/cuda/kernels.cu#L2266
[ms-blake3]: https://github.com/argumentcomputer/multi-stark/blob/ac144be2eb670aa081ec3800614454f3c036b7b5/cuda/kernels.cu#L1800
[blake3]: https://github.com/0xPolygonHermez/pil2-proofman/blob/d2f43760c3b89e264fdf5d0e3bd9419d5b564a3c/pil2-stark/src/goldilocks/src/blake3_goldilocks.cu#L60
[blake3-pack]: https://github.com/0xPolygonHermez/pil2-proofman/blob/d2f43760c3b89e264fdf5d0e3bd9419d5b564a3c/pil2-stark/src/goldilocks/src/blake3_core.hpp#L195
[ms-upload]: https://github.com/argumentcomputer/multi-stark/blob/ac144be2eb670aa081ec3800614454f3c036b7b5/cuda/kernels.cu#L506
[pinned]: https://github.com/0xPolygonHermez/pil2-proofman/blob/d2f43760c3b89e264fdf5d0e3bd9419d5b564a3c/common/src/memory_handler.rs#L68
[packed]: https://github.com/0xPolygonHermez/pil2-proofman/blob/d2f43760c3b89e264fdf5d0e3bd9419d5b564a3c/common/src/packed_info.rs#L22
[ms-constraints]: https://github.com/argumentcomputer/multi-stark/blob/ac144be2eb670aa081ec3800614454f3c036b7b5/cuda/kernels.cu#L1324
[ms-constraint-encoding]: https://github.com/argumentcomputer/multi-stark/blob/ac144be2eb670aa081ec3800614454f3c036b7b5/src/cuda/mod.rs#L547
[codegen]: https://github.com/0xPolygonHermez/pil2-proofman/blob/d2f43760c3b89e264fdf5d0e3bd9419d5b564a3c/setup/exps-codegen/src/lib.rs#L1
[ms-batch]: https://github.com/argumentcomputer/multi-stark/blob/ac144be2eb670aa081ec3800614454f3c036b7b5/src/batch.rs#L534
[stream]: https://github.com/0xPolygonHermez/pil2-proofman/blob/d2f43760c3b89e264fdf5d0e3bd9419d5b564a3c/pil2-stark/src/goldilocks/src/stream_commit.cu#L374
[stream-policy]: https://github.com/0xPolygonHermez/pil2-proofman/blob/d2f43760c3b89e264fdf5d0e3bd9419d5b564a3c/proofman/src/proofman.rs#L5827
[expansion]: https://github.com/0xPolygonHermez/pil2-proofman/blob/d2f43760c3b89e264fdf5d0e3bd9419d5b564a3c/pil2-stark/src/starkpil/recursion_trace/gate_bands/gate_bands_gpu.cu#L35
[widen]: https://github.com/0xPolygonHermez/pil2-proofman/blob/d2f43760c3b89e264fdf5d0e3bd9419d5b564a3c/pil2-stark/src/starkpil/recursion_trace/witness_widen_gpu.cu#L1
[mem-plan]: https://github.com/0xPolygonHermez/zisk/blob/77ed339416cb0a000a7c10fd4afa6a67b690da1e/state-machines/mem-cpp/cu/count_and_plan.cu#L1443
[coordination]: https://github.com/0xPolygonHermez/zisk/blob/77ed339416cb0a000a7c10fd4afa6a67b690da1e/emulator-asm/asm-runner/src/asm_mo_runner.rs#L375
