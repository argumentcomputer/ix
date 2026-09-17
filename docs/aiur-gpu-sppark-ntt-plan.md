# Sppark NTT/LDE integration plan

2026-09-17. Proposed for review. This document specifies implementation and
validation work; it does not report an implemented backend or new benchmarks.
It supersedes the NTT implementation guidance in the
[upstream review](aiur-gpu-upstream-review.md) and develops K1 of the
[kernel plan](aiur-gpu-kernel-plan.md).

## Objective and decisions

Speed up the recurring NTT/LDE work in both claim and join proofs, across
wide trace matrices and narrow codewords. The completed project covers main
commitments in both rounds, lookup LDEs, quotient transforms and the general
DFT interfaces used by the prover. A main-trace-only integration is an
intermediate milestone.

Use sppark's complete Goldilocks NTT stack through a **direct Cargo dependency**
pinned to `17278d74295392f9813f009300b257a688422b7a`. Reuse its field arithmetic,
roots, twiddle generation, transform scheduling, kernels and permutations
together. Keep matrix integration in multi-stark. If measured performance
requires changes inside sppark, use a pinned Git dependency on a fork with a
small, reviewable patch set. Do not vendor a source copy into ix or multi-stark.

Upstream sppark is [Apache-2.0][sppark-license]. Proofman's implementation is
not a dependency or a source of copied/translated code. Its batching,
memory-layout and LDE-fusion ideas may inform independently written changes.

The target is approximately **2x faster workload-weighted complete NTT/LDE
operations**, including layout conversion, auxiliary kernels and synchronization,
with a material reduction in both claim and join proving time. This is a target
to test, not an established speedup. Near-best performance requires comparative
measurements on our GPU and matrix shapes.

The proposed rollout floor is **10% lower median proving time on each of the
representative claim and join**, with the difference exceeding run-to-run
variation. This keeps acceptance tied to a meaningful proof improvement even
if the complete-operation target needs further work.

## Evidence and expected opportunity

The [September 17 Init profile][profile] used one RTX PRO 6000, 24 CPU cores,
resident seeds, a 1.5e9-cell piece budget and a maximum trace log-height of 24.
It was built from ix `5beba0d4` plus the packing spans committed in `aa85fe39`,
against multi-stark `c26dbba5908efc526ad5554d04211ab85fe3b2b0`.

| Quantity | Claim 1: 11 pieces | Join 5: 8 pieces |
| --- | ---: | ---: |
| Proof, both rounds | 44.89 s | 24.02 s |
| Radix-2/4/8 stage kernel time | 13.43 s | 7.31 s |
| Those stages as a fraction of proof time | 29.9% | 30.4% |
| Modeled proof time with those stages halved | 38.17 s | 20.37 s |

The last row holds every other cost constant and assumes the saved kernel time
is on the critical path. It is not a forecast for the first adapter. The stage
totals exclude permutation/shift kernels, the fused tail and conversion costs;
the new complete-operation measurements must include all of them.

Our wide radix-8 kernel fuses three radix-2 stages per global-memory pass.
sppark's [scheduler][sppark-ntt] uses three larger steps at log-heights 24–26.
The data-pass counts below exclude permutations, padding and layout conversion;
they are per column, not total launches across a matrix.

| Transform length | Current width >=8 | Current width 3–7 | Current width 1–2 | sppark |
| --- | ---: | ---: | ---: | ---: |
| 2^24 | 8 | 24 | 17 | 3 |
| 2^26 | 9 | 26 | 19 | 3 |

The width-1/2 count already includes our fused tail. Radix-2 launch counts alone
do not identify narrow transforms: wide transforms also use remainder stages.
Collect actual height, width and caller frequencies before attributing savings.

## Dependency and build integration

Add an optional dependency and comparison feature to multi-stark:

```toml
[dependencies.sppark]
git = "https://github.com/supranational/sppark"
rev = "17278d74295392f9813f009300b257a688422b7a"
optional = true
features = ["cuda"]

[features]
cuda-sppark = ["cuda", "dep:sppark"]
```

Use the header directory exported as `DEP_SPPARK_ROOT` by sppark's
[build script][sppark-build] to compile a multi-stark-owned CUDA adapter with
`FEATURE_GOLDILOCKS`. This is the supported header integration boundary; do not
locate or modify Cargo's checkout by guessing its filesystem path.

Keep multi-stark's explicit architecture selection, static CUDA runtime linkage
and existing host-toolchain compatibility flags for the adapter. There is no
need to enable sppark's Rust `build` helper feature on the normal dependency:
at this revision that feature makes its own build script a no-op. Verify the
upstream native archive's linkage and compiler compatibility as part of the
first focused target, including the Lean/Rust static-library boundary.

Forward `cuda-sppark` through aiur and ix-ffi. Add an explicit experimental
selection in Lake's `cargoArgs` so comparison binaries can enable it without
manually replacing archives; record the selected features in the existing
build trace. A proposed `IX_CUDA_SPPARK=1` enables the feature and implies CUDA.
The existing CUDA build remains the control until acceptance. CPU-only builds
must not build sppark, invoke nvcc or acquire a CUDA dependency.

Update lockfiles only for the new dependency and required transitive entries.
The ix manifest currently pins an older multi-stark revision than the profile's
backend; record the actual backend source used by every comparison build.
Local path overrides can support development. The final ix pin follows the
user's push of the reviewed multi-stark commit.

## Device execution and ownership

Use the device-pointer NTT interface, `NTT::Base_dev_ptr`. The high-level
`Base` and `LDE_aux` entry points allocate buffers and move full inputs/results
between host and device, which does not fit the resident prover.

Unmodified sppark's [runtime][sppark-runtime] owns its streams. The initial
direct-dependency adapter will therefore lease a reusable execution context
with an upstream `stream_t`, two CUDA events and accounted scratch:

1. Record input readiness on the caller's stream.
2. Make the leased sppark stream wait for that event, then enqueue the entire
   matrix operation, including our gather/shift/scatter kernels.
3. Record completion on the sppark stream and make the caller's stream wait
   before consuming or freeing the result.

Hold exclusive ownership of the context and buffers through GPU completion.
Reuse is event-driven, with no host synchronization between columns. Preserve
each existing FFI call's completion contract; asynchronous and partitioned
operations must keep their context lease alive until their actual completion.
Failure cleanup must drain outstanding references before releasing buffers.

Pool contexts under the existing device-workspace budget. Do not serialize all
concurrent callers onto one shared upstream stream. Conversely, do not create
an unbounded context per request. Record context contention and event overhead.

sppark's logical device indices can differ from CUDA ordinals after filtering.
Resolve and check the mapping against the caller's selected CUDA device,
including `CUDA_VISIBLE_DEVICES` remapping. Initialize parameters once before
timed work, establish readiness for every worker stream, and preserve the
caller's selected device. Upstream initializes tables for its visible devices
and constructs CPU thread pools; account for that cold-start behavior and
measure its thread/memory footprint. The adapter does not submit executor work
to those pools.

If measurements show that this runtime integration adds material overhead, a
dependency fork can expose borrowed streams and explicitly owned per-device
parameters. That is a localized upstream API change, not a reason to copy the
NTT implementation into multi-stark.

## Matrix and LDE adapter

The resident LDE contract is a natural-order, row-major input trace and a
row-major output with bit-reversed evaluation rows and canonical Goldilocks
bytes. The input trace and resident seed-cache lifetimes remain controlled by
their current owners. Accept the actual coset and blowup from the caller.

For the first implementation, process a memory-budgeted panel of C columns in
one reusable column-major scratch allocation. With N input rows and
M = N * 2^added_bits output rows:

1. Gather and canonicalize the panel into the first N positions of each
   M-element column.
2. Run normalized inverse NTTs in NR order: natural evaluations to bit-reversed
   coefficients. Keep sppark's transform scheduling and kernels unchanged.
3. Combine restoration of natural coefficient order with multiplication by
   the caller's coset powers. Zero the remaining M-N positions. No additional
   inverse-size factor is applied.
4. Run forward NTTs in NR order, producing bit-reversed evaluations.
5. Scatter to the existing row-major output allocation, preserving that order
   and canonical bytes.

This requires one gather and one scatter for the complete inverse/forward pair.
The initial implementation may loop over columns on the host without waiting
between them. That is a correctness baseline; measure its launch overhead
before deciding the final batching implementation.

Base panel storage is `8 * M * C` bytes, plus parameters, events and auxiliary
workspace. Reserve it before admission; choose C from that reservation and
the matrix width. Concurrent operations must not each claim the same free
memory. Reused allocations remain accounted while cached, and are evictable
when idle. A later fused-load path may need an additional compact input panel
of `8 * N * C` bytes; that also belongs in admission.

At M=2^26, each scratch column costs 512 MiB. No full second copy of every LDE
is required. An allocation-free small-transform path or the existing CUDA
path may be preferable for particular shapes; report dispatches and their
reasons. An unreported fallback or additional host spill cannot count as a
successful sppark comparison.

## Required coverage and numerical contracts

Audit each call site's direction, input/output order, scaling, source lifetime
and completion boundary before changing it. Share the adapter and context
management across these paths:

| Path in `multi-stark/cuda/kernels.cu` | Work to cover |
| --- | --- |
| `coset_lde_create` and resident wrappers | Main/preprocessed LDEs, host-uploaded and generated inputs, both rounds |
| `multi_stark_cuda_lookup_graph_lde`, `multi_stark_cuda_lookup_lde`, `multi_stark_cuda_lookup_lde_finish_partitioned` | Lookup trace inverse/forward transforms, including partitioned construction |
| `multi_stark_cuda_quotient_lde` and `_mixed` | Width-2 quotient transforms, slicing/scaling, and committed quotient LDEs |
| `multi_stark_cuda_dft_batch`, `multi_stark_cuda_coset_lde_batch` | General DFT/LDE users, including codeword/polynomial work reached through these interfaces |

Inventory any additional transform entry points added since the profiled
revision. FRI folding and interpolation kernels are not automatically NTTs;
identify actual transform work rather than attributing the entire FRI phase
to this backend.

- **Roots:** all 33 default [sppark Goldilocks roots][sppark-roots] match our
  [pinned Plonky3 table][p3-field]. Do not select `GOLDILOCKS_PLONKY2`, whose
  convention differs.
- **Scaling:** sppark inverse transforms normalize by 1/N. Existing main and
  lookup LDEs currently normalize afterward. Remove that duplicate factor
  only on the new path. The current quotient path supplies *forward* twiddles
  and handles its coefficient interpretation in subsequent slicing; do not
  turn it into an inverse transform merely because it precedes an LDE.
- **Representatives:** raw inputs may include lazy representatives. Start with
  canonical arithmetic, leave `GL64_PARTIALLY_REDUCED` and
  `GL64_NO_REDUCTION_KLUDGE` disabled, and verify raw output words before
  hashing, not only field equality.
- **Dimensions:** handle empty widths, height one and zero added bits outside
  upstream routines that assume a nontrivial transform/expansion. Check shape
  arithmetic and compiled-domain limits before allocation or launch.
- **Domain limit:** validate against Goldilocks' two-adicity of 32. Initially
  compile sppark with its reviewed default maximum log-domain of 28, covering
  the current trace cap and 4x LDEs. Explicitly dispatch larger supported
  requests to the existing backend until a larger sppark limit is validated;
  the cryptographic field limit alone does not validate its indexing at 2^32.
- **Constants:** bypass construction/upload of the old full NTT tables for
  converted paths. Retain constants still needed by other operations. Cache
  any adapter coset tables by the actual shift as well as dimension/device.

## Complete the performance work

The following adaptations are in scope after the unchanged-engine baseline.
Each must be assessed with complete-operation timings on the frequent shapes.
If an adaptation is unnecessary to reach the target, retain the evidence for
that decision. An isolated polynomial benchmark is insufficient.

**Batch columns in the launch grid.** Add column count/stride to the upstream
launcher and kernels in a dependency fork if separate launches are material.
Use independent columns in a grid dimension while sharing immutable parameters.
Measure tall/narrow and short/wide matrices; do not assume the same batch size
works for both.

**Fuse the LDE expansion.** Independently implement a first-forward-pass load
that reads compact bit-reversed coefficients, multiplies by coset powers and
supplies virtual zeros. Pair inverse NR with forward RN so the intermediate
bit reversal disappears. Forward RN returns natural-order evaluations; fold
the required output row permutation into the final matrix scatter. Prove
source/output non-overlap or stage the compact input explicitly before using
this path. Test blowup 1, 2, 4 and 8 separately.

**Tune the actual hardware bottleneck.** Compare the upstream stage splits and
butterflies per thread with a small number of variants. Inspect register spills,
global-memory traffic and shared-memory bank conflicts. Use the actual
Goldilocks kernels and matrix costs; SP1's KoalaBear results do not establish
our performance. Proofman's L2 column-chunking idea applies only when a column
fits: 2^24 and 2^26 Goldilocks columns are already 128 and 512 MiB respectively.

Keep custom upstream changes together in a pinned fork, with attribution and
a concise patch record. Matrix batching, fused input loads and a borrowed
stream API are explicit candidates; do not rewrite the arithmetic or import
Proofman's implementation as part of those changes.

## Implementation milestones

| Milestone | Deliverable and exit evidence |
| --- | --- |
| 1. Dependency and operation inventory | Optional pinned dependency, adapter compilation/linkage, numerical/stream contracts for all call sites, shape-frequency recording and a focused device-pointer transform check |
| 2. Resident main LDE baseline | Complete gather/inverse/shift/forward/scatter operation using unchanged sppark kernels; canonical bytes, roots, stream lifetimes and workspace accounting verified |
| 3. All prover transforms | Lookup, quotient and general DFT/LDE paths use the shared integration; direction/scaling contracts verified; backend/fallback counts available for both representative proofs |
| 4. Matrix and LDE optimization | Batching, expansion fusion and bounded tuning evaluated; measured changes retained in a pinned dependency fork where needed |
| 5. Proof comparison and rollout | Controlled claim/join results, native verification, proof-byte checks, cold/steady-state costs and peak-memory evidence; default-backend decision based on those results |

Milestones 1–2 establish correctness and a reference implementation. They do
not satisfy the complete performance objective by themselves. If later work
misses the target, report the remaining bottleneck and measured result rather
than labeling the backend near-best.

## Validation and acceptance

Extend the existing focused tests in `multi-stark/src/cuda/mod.rs`, including
`batched_dft_matches_cpu`, `coset_lde_matches_cpu_including_storage_layout`,
`resident_coset_lde_padding_and_raw_representatives`,
`resident_coset_lde_matches_cpu_storage` and
`resident_ldes_feed_mixed_merkle_without_host_round_trip`.

Cover widths 1, 2, 3–7, 8 and representative wide/non-panel-multiple matrices;
height-one and stage-split boundaries; the production blowup and alternative
blowups; cosets 1, 7 and 11; and representatives 0, 1, p-1, p, p+1 and
`u64::MAX`. Check both logical results and stored canonical bytes. Exercise
generated inputs and all lookup/quotient variants. Use bounded large-domain
checks to exercise the production kernels without a full CPU oracle at every
large matrix size.

Add meaningful ownership checks for concurrent callers, input/output event
dependencies, scratch reuse, cleanup after failure, tight workspace budgets
and remapped devices. CPU builds remain a separate feature-isolation check.

Record operation kind, height, width, blowup, backend, panel width, scratch
bytes and fallback reason at the operation boundary. Measure gather/scatter,
NTT, shift/padding and stream-wait costs separately, plus complete-operation
time. Concurrent elapsed intervals must not be summed and presented as proof
wall time. Remove unused legacy twiddle generation from the measured new path.

Use the existing [Init profile runner][profile-runner] and cached inputs for
claim 1 and join slot 5, with independently identified control and sppark
binaries. Preserve generated inputs, resident seeds, piece plan, CPU affinity,
execution settings and cache conditions. Re-establish the control on the same
implementation base; the historical profile is the sizing evidence, not a
substitute for that control. Keep output artifacts separate and retain proofs
for byte comparison and native verification.

Start with one correctness replay of each unit. For performance acceptance,
use paired runs in alternating order, initially three pairs per unit, with
cold initialization reported separately. Increase repetitions only if the
observed variance prevents a conclusion. Propose the CPU/GPU allocation and
expected runtime before scheduling these machine-intensive runs; writing this
plan does not start them or authorize broad benchmark sweeps.

Accept the backend when:

1. The converted paths agree with their reference numerical/storage contracts,
   and deterministic proof bytes, commitments and native verification match.
2. Both claim and join meet the proposed 10% proof-time reduction floor beyond
   observed variation. Evaluate the approximately 2x complete-operation target
   and approximately 15% proof-time opportunity explicitly, including any miss
   and its cause. Results below the floor remain experimental.
3. Results cover the materially frequent wide and narrow shapes and report
   remaining existing-backend dispatches; gains do not depend solely on a
   boundary shard or a favorable isolated transform.
4. Additional scratch, cached contexts and parameters are admitted and measured.
   The same execution/piece budget remains viable, without additional host
   round trips or spill hiding the GPU memory cost.

Once accepted, make the selected backend part of the normal CUDA feature path
and retire the temporary comparison switch or retain it only for a documented
fallback. The user performs remote pushes; subsequent ix dependency-pin and
lockfile changes remain scoped to the reviewed commits.

## Expected file changes

| Repository | Files | Purpose |
| --- | --- | --- |
| multi-stark | `Cargo.toml`, `Cargo.lock`, `build.rs` | Direct dependency, feature isolation, exported headers and native linkage |
| multi-stark | `cuda/sppark_ntt.cu`, `cuda/sppark_ntt.h` | Matrix/stream adapter, scratch ownership and operation contracts |
| multi-stark | `cuda/kernels.cu`, `src/cuda/mod.rs`, `src/cuda/pcs.rs` | Route each transform family, adjust normalization/constants, account for workspace and add operation diagnostics/tests |
| ix | `Cargo.toml`, `Cargo.lock`, `crates/aiur/Cargo.toml`, `crates/ffi/Cargo.toml`, `lakefile.lean` | Reviewed multi-stark pin and explicit feature propagation into comparison binaries |
| ix | `bench/prover-profile-init-2026-09-17/` or a dated follow-up directory | Reproducible comparison commands, correctness artifacts and timing/memory report |
| sppark fork, if needed | NTT launch/load interfaces and runtime ownership APIs | Measured batching, LDE fusion or stream integration changes, consumed as a pinned Git dependency |

## Sources

The reviewed sources are pinned; no assumption about a moving branch is needed
to implement this plan. [SP1's adapter][sp1-adapter] at
`9ce13607e9f464b9d5ccd8b4a6478de0e8f8bf1b` is an integration reference.
[Proofman's requested branch][proofman-ntt] was reviewed at
`20f09bff71e5454d8314feae8316fdaf0be84014` for ideas only.

[profile]: ../bench/prover-profile-init-2026-09-17/README.md
[profile-runner]: ../bench/prover-profile-init-2026-09-17/profile.sh
[sppark-license]: https://github.com/supranational/sppark/blob/17278d74295392f9813f009300b257a688422b7a/LICENSE
[sppark-build]: https://github.com/supranational/sppark/blob/17278d74295392f9813f009300b257a688422b7a/rust/build.rs
[sppark-ntt]: https://github.com/supranational/sppark/blob/17278d74295392f9813f009300b257a688422b7a/ntt/ntt.cuh
[sppark-runtime]: https://github.com/supranational/sppark/blob/17278d74295392f9813f009300b257a688422b7a/util/gpu_t.cuh
[sppark-roots]: https://github.com/supranational/sppark/blob/17278d74295392f9813f009300b257a688422b7a/ntt/parameters/goldilocks.h
[p3-field]: https://github.com/Plonky3/Plonky3/blob/3152b14a89067c83775a8076cc262ffc48a1fd7c/goldilocks/src/goldilocks.rs
[sp1-adapter]: https://github.com/succinctlabs/sp1/blob/9ce13607e9f464b9d5ccd8b4a6478de0e8f8bf1b/sp1-gpu/crates/sys/include/ntt/sppark.cuh
[proofman-ntt]: https://github.com/0xPolygonHermez/pil2-proofman/blob/20f09bff71e5454d8314feae8316fdaf0be84014/pil2-stark/src/goldilocks/src/ntt_goldilocks.cu

## Milestone 1 inventory (2026-09-17)

Every transform the prover runs goes through `launch_dif` in
`multi-stark/cuda/kernels.cu`; `launch_dif` is a decimation-in-frequency
transform that takes natural-order rows and leaves bit-reversed rows, and
the callers pair it with `bit_reverse_scale_and_shift`, which restores
natural order, multiplies by the inverse size and by the coset shift powers
in one pass. All matrices are row-major with the transform along the
column: element `(r, c)` is at `r * width + c`. Twiddle tables come from
`cached_device_constants`, one device copy per size. Line numbers are
multi-stark `dedfb5e`.

| Entry point | Sequence | Direction, order, scaling | Source and completion |
| --- | --- | --- | --- |
| `multi_stark_cuda_dft_batch` (2230), the general `dft_batch` | upload; `launch_dif` with forward twiddles; download | forward, natural in, bit-reversed out, unscaled; the Rust caller wraps the result as a bit-reversed view | host matrix in and out; synchronous |
| `multi_stark_cuda_coset_lde_batch` (2259), the general host `coset_lde_batch` | upload into the zeroed extended buffer; inverse `launch_dif`; `bit_reverse_scale_and_shift`; forward `launch_dif` at the extended height; download | inverse then forward; natural in, bit-reversed evaluations out; 1/N and shift powers applied between the two | host in and out; synchronous |
| `coset_lde_create` (2330) behind `multi_stark_cuda_coset_lde_create` and the generated variant: every main and preprocessed trace, both rounds | trace uploaded or generated into `trace_values`, copied into the extended buffer whose tail is zeroed; inverse `launch_dif`; `bit_reverse_scale_and_shift`; forward `launch_dif`; canonicalize | as above; output rows bit-reversed, canonical words | resident; the host trace or the generator stays attached until `release_trace`; `cudaStreamSynchronize(cudaStreamPerThread)` before return |
| `multi_stark_cuda_quotient_lde` (2807) and `_mixed` (2925): the quotient | `launch_dif(quotient, quotient_size, 2, quotient_twiddles)` on the width-2 evaluations; `gather_shifted_quotient_slices` into the zeroed committed matrix; `launch_dif(lde, lde_height, width, lde_twiddles)` | both calls take the twiddle table the Rust side supplies for the size, forward tables today; the slicing step interprets the first result's coefficients and applies the shift itself; no 1/N pass here, the Rust side folds normalization into the slice weights | resident; the mixed variant double-buffers staged inputs on two streams and synchronizes them before the transforms; `cudaStreamSynchronize(0)` at the end |
| `multi_stark_cuda_lookup_graph_lde` (3337) and `multi_stark_cuda_lookup_lde` (3430): stage-two lookup traces | deltas scanned into the width `2 * groups` buffer; inverse `launch_dif`; `bit_reverse_scale_and_shift`; forward `launch_dif` at the extended height; canonicalize | as the main LDE | resident; `cudaStreamSynchronize(0)` at the end |
| `multi_stark_cuda_lookup_lde_finish_partitioned` (3639): the cooperative lookup path | same inverse, shift, forward, canonicalize sequence on the pending buffer | as the main LDE | resident; synchronizes the per-thread stream |
| FRI folding, interpolation, reduction and Merkle hashing | no `launch_dif` | not transforms | out of scope for this backend |

Contracts an sppark path must keep at each site:

- The evaluation output order is bit-reversed rows and the committed words
  are canonical; hashing reads the raw words.
- The inverse-then-forward pair applies exactly one 1/N and the coset shift
  between the transforms; sppark normalizes its inverse internally, so the
  scale in `bit_reverse_scale_and_shift` must go when the inverse goes.
- The quotient path supplies forward tables for both of its calls and
  handles its scaling in the slice step; it is not an inverse-forward pair
  and must not be converted into one.
- Upstream takes canonical words only. The contract test that fed raw
  representatives at and above the modulus, which the first-party kernels
  reduce lazily, got different outputs, so every converted path reduces its
  input before the transform (a pass the gather into the column panel can
  absorb) and the `GL64_PARTIALLY_REDUCED` mode stays off.
- Widths seen in the profiled proofs: main traces 6, 7, 10 to 49 and 533;
  quotient 2; lookups 2 to 16; heights 2^19 to 2^24 with 4x expansion,
  so 2^26 output rows. Narrow widths, under 8, take the radix-2 path today
  and are 4.3 s of the profiled claim's 4.8 s of radix-2 time.

Delivered in this milestone: the optional pinned dependency and the
`cuda-sppark` feature in multi-stark, compiled in their own nvcc step
because the upstream runtime needs libstdc++'s `<mutex>`; the adapter
`cuda/sppark_ntt.cu` with device-pointer and host-pointer entries fenced
to the caller's stream by events; `src/cuda/sppark.rs` with the contract
tests (natural forward against the CPU DFT, reversed orders as the
bit-reversal, upstream inverse normalization and the round trip, the coset
by the field generator, canonical extremes in and canonical words out, and
the domain limit covering 2^26); and the `cuda-sppark` feature through aiur,
ix-ffi and `IX_CUDA_SPPARK=1` in Lake.

### Linkage at the Lean boundary

The sppark archive links into the Rust static library and the multi-stark
tests without trouble. The `ix` executable does not link as is: sppark's
GPU runtime (`util/all_gpus.cpp`, `gpu_t.cuh`'s thread pool and the
exception type) needs libstdc++'s `std::thread`, `std::string`,
`std::runtime_error` and `std::condition_variable`, sixteen symbols in all,
while Lake's response file links Lean's libc++ and libc++abi. A static
libstdc++ collides with libc++abi on `std::exception`. What links, and
runs, is the shared libstdc++ with the sysroot check relaxed:

```
clang -o ix @ix.rsp -L<gcc-14.3.0-lib>/lib -lstdc++ -Wl,--allow-shlib-undefined
```

The relaxation is needed because the response file links Lean's bundled
older glibc for portability, whose symbol versions predate what the shared
libstdc++ references, whereas at run time the binary already loads under
the Nix glibc 2.40 loader with that gcc library directory on
`LD_LIBRARY_PATH`, exactly as the bench runners set it. `ldd` on the relinked
binary resolves `libstdc++.so.6` there and `ix --help` runs
(`bench/prover-profile-init-2026-09-17/README.md` has the environment).
Open item for milestone 2: carry those three arguments into Lake's link of
`ix` when `IX_CUDA_SPPARK=1`, with the library directory supplied by the
environment rather than hard-coded, or drop the runtime dependency in the
dependency fork by replacing the thread pool and exceptions in the paths
the adapter uses.
