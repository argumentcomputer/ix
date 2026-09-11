# Upstream GPU code review for Aiur trace sharding

2026-09-11. Source review only; no builds, tests, GPU jobs, or queue scripts
were run. This supplements [the GPU recommendations](aiur-gpu-performance-recommendations.md).
The local comparison is ix `d3b039ea293bfaa1460b2a7a9a56668d7f081359`
(the memory-budget execution scheduler) and multi-stark
`ac144be2eb670aa081ec3800614454f3c036b7b5`.

**Current priority, revised after reviewing the branch profiles:**

1. Finish the current scheduler's correctness and validation work. Use cold
   proving as the primary result, include any required preflight cost, and
   accurately distinguish admission accounting from an enforced memory limit.
2. Measure GPU Stage 2 through the complete range tree and final root, including
   native verification, final proof bytes, total wall time and host/VRAM peaks.
   This is still the largest gap in the end-to-end performance evidence.
3. Profile the resulting workload and prioritize local Blake3 optimization and
   execution-partition/trace-padding improvements. Compare total committed
   cells, duplicated query work, proof bytes and complete elapsed time, rather
   than optimizing shard count alone. Fewer execution chunks can also reduce
   CPU parallelism and increase the size of individual records.
4. Run the bounded sppark experiment below after those measurements, or when
   they identify NTTs as the best remaining target. Add no ICICLE dependency.

Upload overlap is conditional on a current timeline showing exposed transfer
or staging time. It is not the first task: the resident commit path already
processes matrices in parallel waves, each using its own per-thread CUDA
stream, so a wait in one upload does not imply a device-wide idle gap.
Likewise, multi-GPU device workers are a separate hardware-dependent task.

The v2 round-one kernel summary reports 43.0% Blake3 row hashing and 41.1%
radix-8 stages (with smaller additional NTT kernels). Those are accumulated
kernel times from that profile, not a current whole-prover wall-time breakdown.
Using the proposed estimate of 0.5–0.6 seconds of NTT work per main commitment,
a 2x improvement across 56 shards and two passes saves 28–34 seconds before
layout overhead, about 7–9% of a 6:18 prove. Only half of that saving belongs
to round two. The scoped first experiment does not replace lookup, quotient
or FRI transforms. These estimates are neither a guaranteed gain nor a hard
speedup ceiling.

The single-record versus eight-record comparison suggests roughly 100 seconds
of additional batch work. It does not show that all of that difference can be
removed while retaining parallel execution and the same memory bound. Measure
that tradeoff before treating it as an available saving.

Evidence: `~/benchdata/trace-shards-gpu/v2-r1_cuda_gpu_kern_sum.csv`,
`init-gpu-v3-single.log`, `init-gpu-v7-dist8-keep-ahead8.log`, and
`multi-stark/src/cuda/pcs.rs` around `CUDA_LDE_WAVE`.

**Deferred experiment: concrete handoff for the implementation agent.**

When scheduled, run one bounded sppark integration experiment on the
main-trace resident LDE path. Do not add an ICICLE/open-icicle dependency or port its
CUDA backend on this branch. Continue improving our own Blake3 implementation.
Keep the existing execution scheduler and record budget as the baseline.

The first deliverable is an optional `cuda-sppark` build feature in multi-stark,
depending on `cuda`, plus a measured keep/remove decision. It selects the
experimental main-trace path for comparison; there is no new runtime backend
selector, tile-size flag, autotuner, or scheduling policy. Existing CUDA
remains the default until the experiment demonstrates a repeatable benefit.

| Proposed change | Scope |
| --- | --- |
| `cuda/vendor/sppark/` | Pin `17278d74295392f9813f009300b257a688422b7a`; retain licenses and a record of local adaptations. Include the Goldilocks NTT dependencies only. |
| `cuda/sppark_ntt.cu` and a small private header | Device-buffer adapter, reusable scratch, layout conversion, explicit stream and per-device NTT parameters. |
| `build.rs`, `Cargo.toml` | Compile the adapter only under the experimental feature, using the existing compiler/architecture settings and static-link arrangement. |
| `cuda/kernels.cu` | Route `multi_stark_cuda_coset_lde_create` through the alternative LDE helper. Keep its existing resident handle, trace storage and error cleanup. |
| `src/cuda/mod.rs`, `src/cuda/pcs.rs` | Account for adapter scratch and parameters; avoid generating/uploading unused full inverse/forward twiddle tables for the selected path. Preserve shift powers needed by the chosen implementation. |
| Existing CUDA tests | Exercise the experimental resident path against CPU outputs and existing commitment/proof checks. |

`multi_stark_cuda_coset_lde_create` is the correct first boundary. A global
replacement of `launch_dif` would also alter lookup, quotient and FRI paths
with different layouts and normalization contracts. Expand to those only
after this experiment succeeds. The ordinary host-returning `CudaDft`
interface is also insufficient: the actual prover uses resident handles.

Use sppark's NTT arithmetic and kernels, with a narrow host adaptation to take
our explicit `cudaStream_t` and NTT parameter context. Keep kernel bodies as
close to upstream as possible initially. Do not bring in its complete GPU
runtime: upstream `stream_t` owns newly created streams, `all_gpus.cpp`
enumerates devices, and every `gpu_t` constructs a CPU thread pool. We need
none of that for an NTT inside an already scheduled shard. SP1's modified
sppark is a reference for accepting a caller's stream, not the source of a
new prover runtime. Initialize parameters lazily for the selected CUDA device
and make their readiness/lifetime explicit across callers.

The helper's contract should be:

- Input: an already resident, natural-order, row-major trace, its actual
  height/width/blowup/coset, the caller's stream, and accounted workspace.
- Output: our existing resident LDE allocation in **row-major, bit-reversed
  evaluation order**, with canonical Goldilocks values.
- Execution: enqueue work on the caller's stream. Preserve the current outer
  FFI completion boundary; avoid per-column host synchronization and all full
  host round trips.

A concrete first implementation uses one reusable column-tile buffer:

1. Gather a tile of trace columns into contiguous polynomial storage and
   canonicalize inputs. Each column has room for the extended height.
2. Run sppark's inverse NTT in `NR` order on each column's original height.
3. Restore natural coefficient order, apply the actual coset powers, and
   zero the extension. Combine these operations where straightforward.
4. Run the forward NTT in `NR` order at the extended height.
5. Scatter columns into the existing row-major LDE, preserving the resulting
   bit-reversed row order and canonicalizing stored field values.

This keeps the inverse and forward transforms in the same scratch layout,
requiring one gather and one scatter for the whole LDE operation instead of
transposing around each transform separately. The input trace stays resident
for lookup construction, just as it does today.

Scratch for `tile_columns` requires
`8 * extended_height * tile_columns` bytes, plus parameter/kernel workspace.
Derive the tile width from the available, explicitly reserved workspace and
matrix width. Include that reservation in PCS placement/admission; do not
choose it from a raw free-memory snapshot that ignores the rest of the shard.
If even one column cannot fit, keep the original CUDA implementation for that
shape and report the fallback. Do not make the comparison silently use host
spill. Record the tile width and scratch bytes in the experiment results.

Three compatibility requirements are already established by reading source:

- **Inverse normalization:** sppark's inverse kernels apply `1/N`. Our current
  inverse `launch_dif` does not; `bit_reverse_scale_and_shift` applies it later.
  In the sppark path, that later operation must use a scale of one. Applying
  both scalings produces the wrong LDE.
- **Root convention:** sppark's default Goldilocks forward-root table matches
  the table in our pinned Plonky3 revision `3152b14`. Do not define
  `GOLDILOCKS_PLONKY2`, which selects a different table. Test arbitrary cosets,
  not only the multiplicative generator seven.
- **Representation and limits:** start with canonical Goldilocks arithmetic;
  leave the optional partial-reduction modes disabled. Validate dimensions
  before launch, including the compiled maximum domain. Derive that maximum
  from Goldilocks' two-adicity (32) rather than the current Init piece cap.
  Treat height-one transforms as no-ops before entering upstream kernels.

For an ix comparison build, forward the optional feature through
`crates/aiur/Cargo.toml` and `crates/ffi/Cargo.toml` as needed. The normal
`IX_CUDA=1` build currently enables `cuda` via `lakefile.lean`; do not assume
adding a feature in multi-stark automatically enables it in the measured ix
binary. Use a clearly identified experimental build and record its features.

**Keep/remove criterion.** First extend the existing
`resident_coset_lde_matches_cpu_storage` and
`resident_ldes_feed_mixed_merkle_without_host_round_trip` coverage. Include
non-generator cosets, padding, field edge values, tile remainders and heights
that exercise the large mixed-radix kernels. Ensure these calls actually take
the sppark path; a CPU/original-CUDA fallback is not validation of the adapter.
Then run the existing batch/native-verification checks for the changed path.

Measure the actual matrix shapes and frequencies in the current Init plan:
NTT time, gather/scatter time, complete main commitment time, scratch/VRAM peak,
and whole `ix prove` wall time. Use the same shard plan, host budget and
execution settings; separate cold initialization from steady-state timings.
The latest budget scheduler is the baseline, not an older queue's differently
configured result. Document whether any paths fell back to existing CUDA.

Keep the feature only if complete commitments and the proving workload show
a repeatable improvement without a residency regression. An isolated NTT win
is insufficient. If transposes dominate, retain the evidence and consider a
separate row-major mixed-radix kernel change; do not immediately launch an
ICICLE port or add shape thresholds to rescue the experiment.

For **ICICLE**, the integration recommendation is **none at present**. Its
stream/residency API and open-icicle's column-batched kernels remain design
references. Independently implementing event-based pinned-upload overlap is a
separate, small change in our backend; it needs neither ICICLE nor sppark and
should be measured separately so the NTT result is attributable.

**Implementation policy remains unchanged:** do not copy, translate, vendor,
or depend on pil2-stark implementation code. Use it only as a conceptual
reference and independently implement worthwhile ideas. No pil2-stark code
was used in this review.

**Sources inspected.** The three accessible repositories were cloned into
`/tmp/ix-gpu-review-20260911-*`. Both older URLs failed to fetch; existing local
repositories supplied the historical code. The exact retained `sp1` tree was
also extracted into a temporary directory without changing its checkout.

| Repository | Reviewed revision | Assessment |
| --- | --- | --- |
| [icicle][icicle] | `625532a624e5aaa6e9d31a1c92587f1fcc30dc76` | Useful device, stream, batch-layout and residency APIs. General CUDA backend is distributed separately. |
| [open-icicle][open] | `a1f8a74b4c604367b9e1eae41aca4d02687e96fc` | CUDA NTT source is present. Supported distribution targets BN254 and BLS12-381, not our Goldilocks configuration. |
| [sppark][sppark] | `17278d74295392f9813f009300b257a688422b7a` | Strongest direct reuse candidate: Goldilocks arithmetic and device-resident NTT/LDE. |
| argumentcomputer/plonky3-accelerate, retained `origin/sp1` | `04d4c6e15a0296798331db82e696d29c455bafe1` | This April 2024 tree has no CUDA integration. The later local `main`, `3fe8e97f3c27ca5ac35e1633b3d757314dd110eb`, contains the GPU code reviewed below. |
| supranational/Plonky3-sp1, local GPU branch | `d4f8a9ecf451a8b145880caa250d00be6de7655a` | Useful integrated commitment example. PR #1 metadata was unavailable, so this is not confirmed as that PR's exact head. |
| Modern SP1 comparison | `a3f98a36431af2d5c0789702b3b6510565a4f391` | Its default NTT path uses sppark; the optional `nvidia-ntt` feature selects NVIDIA cuPQC. |

The SP1 relationship is explicit in its [README][sp1-readme] and
[device-pointer adapter][sp1-ntt]. sppark is therefore relevant to the modern
implementation as well as the older forks. SP1's field and trace layouts still
differ from ours; its speedup numbers do not establish an Aiur speedup.

**Conditional improvement: upload staging, if exposed on the critical path.**

Our `multi-stark/cuda/kernels.cu:506-564` already stages pageable witnesses
through persistent pinned buffers. However, one call leases one buffer and
waits for its transfer after every 64 MiB chunk. Four available slots permit
concurrent callers; they do not pipeline the chunks within one call.

Use a small rotating pair of pinned buffers with completion events. The CPU
can fill the next buffer while DMA reads the previous one, waiting only before
reusing a buffer still in flight. A compute stream should wait on the event
for the data it actually consumes. This is a bounded ownership change inside
the CUDA backend, not a new execution-window flag.

Overlapping upload of the next matrix or shard with current GPU computation
additionally requires destination VRAM and an asynchronous caller interface.
Charge that storage to the existing memory model; do not assume two complete
shards fit. Start with overlap inside an upload, then allow further overlap
only when measured memory headroom permits it. Transfers and kernels may
compete for device memory bandwidth, so measure the complete commitment.

ICICLE's [NTT configuration][icicle-ntt] makes stream, input/output residency,
ordering, and column batching explicit. sppark's [resource types][sppark-gpu]
provide device-associated streams and events. Those are useful models for a
small local interface. ICICLE's [three-stream example][icicle-example] itself
still waits inside its transfer loop and uses ordinary host allocations; it
should not be copied as a finished overlap implementation.

**Deferred experiment: compare sppark against the complete resident LDE path.**

The promising code is [NTT dispatch and device entry points][sppark-ntt],
[mixed-radix kernels][sppark-kernels], [twiddle construction][sppark-twiddles],
and [Goldilocks arithmetic][sppark-field]. These files carry Apache-2.0
licensing notices.

Our tall, wide NTT path already fuses three radix-2 stages per radix-8 kernel.
For a single polynomial at log size 24–26, sppark schedules three larger
transform steps, versus roughly eight or nine stages of our radix-8 dispatch.
The opportunity is fewer full-data passes and different register/shared-memory
usage. This is not a whole-batch kernel-count comparison: our kernel processes
all row-major columns together, whereas sppark's adapter, including SP1's,
loops over contiguous polynomials. Transposes, extra scratch space, and many
per-column launches can erase the advantage.

Use `NTT::Base_dev_ptr` and the device LDE operations. The convenience `Base`
and `LDE_aux` entry points return data to the host and synchronize; they are
not the appropriate integration boundary for our resident prover. Preserve
our field, coset, evaluation ordering and Blake3 commitment bytes.

Two additional ideas deserve measurement:

- Windowed twiddle and coset-power construction trades extra arithmetic for
  smaller tables. At sppark's default Goldilocks maximum log size of 28, the
  parameter allocations total about 232 KiB for forward plus inverse tables
  per device, excluding workspaces. Our full forward-twiddle table alone at
  LDE height 2^26 occupies 256 MiB. Both implementations cache their tables;
  this is a storage and access tradeoff, not a claim of repeated upload savings.
- sppark has carry-aware PTX arithmetic and an optional partially reduced
  Goldilocks representation. Evaluate this separately if arithmetic profiles
  justify it. Canonical field bytes must be restored at hash/serialization
  boundaries, and redundant zero representations need correct handling.

If the adapter loses on wide matrices, use the fused-stage and twiddle ideas
inside our existing row-major kernels. Keep the change local. Our current
backend already combines inverse scaling, coset multiplication and bit
reversal, so that fusion is not a new recommendation.

**What open-icicle contributes.**

Its [mixed-radix implementation][open-mixed] supports strided column batches
directly and combines some reorder/normalization work. This is relevant to
our row-major matrices and may be a better layout reference than the older
transpose-per-call wrappers. Its [dispatch][open-ntt] includes measured
size/batch thresholds and explicitly acknowledges dependence on field,
ordering and GPU. Those constants are not validated for our Goldilocks
workload or Blackwell hardware.

The [declared distribution scope][open] and [build feature list][open-features]
currently support BN254/BLS12-381. Leftover Goldilocks headers do not establish
a supported Goldilocks CUDA build. There is also a source-packaging ambiguity:
the repository has an MIT license file, while the README says non-CPU backends
have separate terms. Treat this CUDA code as a conceptual reference until
reuse terms are clear. A wholesale ICICLE runtime dependency is not needed
for the proposed changes.

**What the older SP1 forks contribute.**

In the local `plonky3-accelerate` main tree,
`cuda/gpu/gpu_api.cu:53-93` uploads the input, transposes it, runs an NTT per
column, transposes back, downloads the result and synchronizes. It is a small
integration reference, but introduces transfers our resident backend avoids.
Its GPU hashes are Poseidon-family implementations, not a replacement for
our Blake3 commitment.

The retained `Plonky3-sp1` GPU tree is more integrated:
`gpu/gpu/gpu_api.cu:584-835` groups matrices, packs a commitment workspace,
alternates streams/buffers and uses events around Merkle work. Its tiled
layout conversions and workspace lifetime are worth reading. However, it
also downloads full LDEs and Merkle layers. The commit entry holds a global
mutex, and `fri/src/two_adic_pcs_gpu.rs:149` selects device zero. Copying that
orchestration would create obstacles to our intended multi-GPU operation.

No directly usable Blake3 CUDA replacement or Aiur record-execution
accelerator was found in these reviewed implementations. MSM/elliptic-curve
acceleration does not address this prover's present workload.

**Hardware-dependent work: one independent resident shard per GPU.**

Follow the simple device-server model in [ICICLE's multi-device guide][multi]:
one CPU worker owns each selected GPU, its streams, allocations, twiddles
and completion events. Discover the selected devices at runtime. The host
record scheduler retains one `--max-ram` budget and accounts for the prover
workspace required by every active GPU, rather than reserving only one.

Dispatch independent trace shards to available device workers. Preserve the
canonical shard indices and assemble round-one headers in protocol order;
derive the shared challenges only after all required headers are available.
Then dispatch round-two shard proofs independently and return them in the
required order. GPU completion order need not define transcript order.

Each shard fits on one device, so this design does not require splitting
individual NTTs across devices or adding GPU-to-GPU collectives. CPU execution
and witness production must still supply enough work. Faster kernels reduce
the time available to hide that CPU work; these libraries do not remove it.

**Acceptance criteria for future experiments; none were run here.**

Compare actual Init and representative Mathlib height/width distributions,
including both wide main traces and narrow lookup/quotient/FRI shapes. Measure
inverse transform, coset expansion, forward transform, layout conversion,
hashing, transfers, synchronization and peak memory together. Separate cold
initialization from steady-state throughput. Reject a faster isolated NTT if
it increases whole-commit time or forces a formerly resident shard to spill.

For any implementation change, compare field edge cases and transform
ordering against the CPU reference, then compare commitment roots and native
proof verification. Validate event lifetimes and multi-device ownership under
concurrency. Report GPU idle time alongside execution/witness throughput and
complete `ix prove` wall time. Stage 2 aggregation needs its own measurement.

Follow the revised priority at the top of this document. The integration
handoff remains available for the deferred sppark experiment; it is not the
next task ahead of scheduler validation and GPU Stage 2 measurement.

[icicle]: https://github.com/ingonyama-zk/icicle/tree/625532a624e5aaa6e9d31a1c92587f1fcc30dc76
[open]: https://github.com/ingonyama-zk/open-icicle/tree/a1f8a74b4c604367b9e1eae41aca4d02687e96fc
[sppark]: https://github.com/supranational/sppark/tree/17278d74295392f9813f009300b257a688422b7a
[sp1-readme]: https://github.com/succinctlabs/sp1/blob/a3f98a36431af2d5c0789702b3b6510565a4f391/sp1-gpu/README.md
[sp1-ntt]: https://github.com/succinctlabs/sp1/blob/a3f98a36431af2d5c0789702b3b6510565a4f391/sp1-gpu/crates/sys/include/ntt/sppark.cuh
[icicle-ntt]: https://github.com/ingonyama-zk/icicle/blob/625532a624e5aaa6e9d31a1c92587f1fcc30dc76/icicle/include/icicle/ntt.h
[icicle-example]: https://github.com/ingonyama-zk/icicle/blob/625532a624e5aaa6e9d31a1c92587f1fcc30dc76/examples/c%2B%2B/best-practice-ntt/example.cpp
[multi]: https://github.com/ingonyama-zk/icicle/blob/625532a624e5aaa6e9d31a1c92587f1fcc30dc76/docs/docs/start/architecture/multi-device.md
[sppark-ntt]: https://github.com/supranational/sppark/blob/17278d74295392f9813f009300b257a688422b7a/ntt/ntt.cuh
[sppark-kernels]: https://github.com/supranational/sppark/tree/17278d74295392f9813f009300b257a688422b7a/ntt/kernels
[sppark-twiddles]: https://github.com/supranational/sppark/blob/17278d74295392f9813f009300b257a688422b7a/ntt/parameters.cuh
[sppark-field]: https://github.com/supranational/sppark/blob/17278d74295392f9813f009300b257a688422b7a/ff/gl64_t.cuh
[sppark-gpu]: https://github.com/supranational/sppark/blob/17278d74295392f9813f009300b257a688422b7a/util/gpu_t.cuh
[open-mixed]: https://github.com/ingonyama-zk/open-icicle/blob/a1f8a74b4c604367b9e1eae41aca4d02687e96fc/icicle/backend/cuda/src/ntt/mixed_radix_ntt.cu
[open-ntt]: https://github.com/ingonyama-zk/open-icicle/blob/a1f8a74b4c604367b9e1eae41aca4d02687e96fc/icicle/backend/cuda/include/ntt/ntt.cuh
[open-features]: https://github.com/ingonyama-zk/open-icicle/blob/a1f8a74b4c604367b9e1eae41aca4d02687e96fc/icicle/cmake/features.cmake
