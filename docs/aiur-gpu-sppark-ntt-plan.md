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
Resolved by the dependency fork instead: `argumentcomputer/sppark`, whose `dev`
branch is where its changes land, adds a `SPPARK_NO_CXX_RUNTIME` build mode in
which `CUDA_OK` ends the process with the expression, location and CUDA
error instead of throwing, `gpu_t` carries no thread pool, and the three
container error hooks libstdc++'s headers call are defined weakly to
abort. Recording the failure and continuing was tried first and rejected
in review: upstream's code after a `CUDA_OK` assumes success, so a failed
stream creation or table upload would have left a bad handle in use or
cached. Stopping matches the Rust side, whose `check_cuda` panics on any
status. The adapter resolves the caller's CUDA ordinal to upstream's
logical index, since upstream lists only the devices it supports, and
keeps its private stream until the caller's stream waits on the
transform, draining it if that wait cannot be installed. With it the
archive references nothing from libstdc++: `ix` relinks with Lake's
unchanged response file, no added flags, starts, and `ldd` shows no
libstdc++ at all. The contract tests and the full suite pass against the
fork. What remains is administrative: push the fork branch and pin its
revision in multi-stark's `Cargo.toml` and lockfile, which today name the
fork's main at the upstream revision with a local path override.

## Milestones 2 and 3 (2026-09-17)

Milestone 2, the resident main LDE baseline, is multi-stark `89d3112` and
`06043c6` on `sb/sppark-ntt`: `coset_lde_create` hands the whole
gather, inverse, un-bit-reverse and shift, forward, scatter sequence to
`multi_stark_sppark_coset_lde` in `cuda/sppark_ntt.cu`, which works on
column panels of up to `MULTI_STARK_SPPARK_PANEL_BYTES` (4 GiB) and runs
upstream's transform once per column on a private stream fenced to the
caller's. The commit loop's admission adds the panel scratch to a source's
need. `MULTI_STARK_CUDA_NTT=sppark` selects the path for inputs of at least
`MULTI_STARK_SPPARK_MIN_LOG_HEIGHT` (20) rows, where the unbatched baseline
already wins; below it the first-party kernels stay, since one upstream
launch sequence per short column is launch-bound (0.43 to 0.88x on the
2^16 to 2^18 shapes). The metrics snapshot counts taken and declined
dispatches and keeps transform shapes per backend. Exit evidence:
`bench/sppark-lde-2026-09-17/README.md` (2.15 to 2.38x on the tall narrow
shapes, 1.23x on the BLAKE3 piece, 168 shapes bit for bit against the
first-party kernels, raw representatives included).

Milestone 3, every prover transform, is multi-stark `2a8acb5` and
`312cbbe`. The lookup LDEs (graph, direct and the partitioned finish), the
quotient's two forward transforms, the general `dft_batch` and the host
`coset_lde_batch` dispatch through two helpers in `kernels.cu`,
`coset_lde_in_place` and `forward_in_place`, so the backend rule lives in
one place; the adapter gained `multi_stark_sppark_forward` (gather, forward
per column, scatter) for the quotient and the general DFT, and an ungated
transform counter. The quotient keeps its two forward transforms with
forward tables and its scaling in the slice step, as the inventory
required. Evidence:

- multi-stark tests: the general DFT and the host coset LDE agree bit for
  bit with the first-party kernels over their shapes; a batch proof over
  the u32-add system produces identical bytes on the first-party kernels
  and on sppark at every height, with the adapter counter proving the
  transforms went through sppark; `examples/proof_compatibility` writes
  digest `25564a01d1d352b1…` on all three settings; 87 tests pass with
  `parallel,cuda,cuda-sppark`, clippy clean with and without the feature.
- Replays of the two representative units on one RTX PRO 6000, the
  `ix` binary relinked against the milestone-3 archive (fork `dev` at
  `13b6226`, no libstdc++), same environment as
  `bench/prover-profile-init-2026-09-17`, no CUPTI (the join once each way,
  the claim four times each way):

  | Unit | first-party | sppark above 2^20 | dispatch counts (sppark run) |
  | --- | ---: | ---: | --- |
  | join 5, execute+prove | 50.80 s | 49.41 s | 163 taken, 371 declined |
  | join 5, end to end | 51.69 s | 50.30 s | proof hash identical both ways |
  | claim 1, wall clock | 2:23.6 to 2:23.8 (4 runs) | 2:18.8 to 2:19.0 (4 runs) | 379 taken, 723 declined |
  | claim 1, batch round one | 11 s | 10 s | |
  | claim 1, batch round two | 28 s | 24 s | |

  The join's declined transforms are the short shapes (heights 2^1 to
  2^19, most of them in the aggregation circuits' many small tables); the
  taken ones are every shape from 2^20 up, main traces, lookups and
  quotients alike. The `[aggregate] replay slot 5` proof hash is the same
  on both runs, so the whole join proof, not only the multi-stark test
  systems, is byte-identical through sppark.

What the numbers say: the resident baseline converts the tall transforms
and the proof stays identical, but the end-to-end gain is 3 to 4 percent,
not the 2x the tall narrow microbenchmarks show, because the transforms
are a minority of each unit (the claim's round two is dominated by trace
regeneration and lookup construction, round one by uploads and Merkle
hashing) and because the per-column baseline gives back part of the
kernel win on the wide shapes. Milestone 4's column batching and fused
expansion are where the transform share itself shrinks; milestone 5's
decision needs those numbers, not these.

Administrative, still open: push the fork's `dev` and pin `13b6226` in
multi-stark's `Cargo.toml` and lockfile in place of the upstream revision
and the local path override; push multi-stark `sb/sppark-ntt`; bump the
ix pin. The `ix` prove entry now initializes the tracing subscriber like
the aggregate entries do, so `RUST_LOG=prover_metrics=info AIUR_METRICS=1`
prints the backend counters for a claim as well as a join; `--texray`
installs its own subscriber first and silences them, so a counted claim
runs without it.

## Milestone 4, column batching (2026-09-17)

The whole Init proof through milestone 3, same binary both ways, one GPU:
415 s to 405 s end to end, the proving union 223 s to 201 s, same root
(`bench/sppark-lde-2026-09-17/init-q4-compare.txt`). Against the recorded
coset-cache run the first-party numbers reproduce within a second.

An audit of milestones 2 and 3 found six things, fixed in multi-stark
`d870622`: the dispatch rule now takes the whole shape (tall enough,
extended height within upstream's compiled domain of 2^28, one column's
scratch within the panel budget) and declines otherwise instead of failing
after allocation; lookup and quotient admission add the sppark panels; the
converted paths skip the first-party twiddle tables (prewarm, lookup and
quotient sites); the backend selector is an atomic with one publication of
the environment setting; the comparison tests serialize on a lock; the
LDE, lookup and quotient spans label the backend they ran on.

Column batching is the fork's `8b624cd` (`NTT::Base_dev_ptr_batch`: the
mixed-radix kernels take the vector from the grid's second dimension, the
permutation and coset passes loop) and multi-stark `fccfb20`. The adapter
transforms a panel's columns in groups sized to the device's L2
(`MULTI_STARK_SPPARK_BATCH_BYTES`, 0 for one column per launch sequence).
Whole-panel batching was measured first: it rescued the short wide shapes
(2^16 x 925: 52 to 21 ms) but cost the tall ones 3 to 7 percent, because a
column that fits the L2 lost the reuse between stages the serial path had.
L2-sized groups keep both (`bench/sppark-lde-2026-09-17/README.md`, the
batching table): every benchmarked shape is at or ahead of the first-party
kernels, 1.05 to 1.19x on the 2^16 to 2^18 shapes that were 0.43 to 0.88x
unbatched, 2.4 to 2.7x on the tall narrow ones, 1.15x on the BLAKE3 piece.
The coefficient panel is compact, so an LDE's scratch is (N + M) words per
column. A batch of vectors is checked against the vectors one by one for
every order, direction and coset setting, and the unbatched setting
against the first-party kernels.

Fork patch record (`argumentcomputer/sppark`, branch `dev`, from upstream
`17278d7`): `6c5d826` and `13b6226` the `SPPARK_NO_CXX_RUNTIME` build mode,
`8b624cd` the batched entry, `176af27` the record of both in its README. Attribution: the batched entry adds a grid
dimension and a stride to upstream's kernels and launchers, arithmetic
unchanged.

Open in this milestone: the height threshold, which the batching results
say can come down, measured on the short shapes the proofs actually commit;
the fused expansion (`LDE_expand`, inverse NR paired with forward RN); and
the paired claim/join replays with the batched build. Still administrative:
push the fork's `dev` and pin `8b624cd` in multi-stark's manifest and
lockfile in place of the upstream revision and the local path override.

### Panel glue, the fused expansion and the threshold (2026-09-17, later)

multi-stark `0ca9402` lowers the height threshold to 2^18 on the batched
measurements, and `8a1f9f9` rewrites the panel glue: the gather and scatter
are tiled transposes (row-per-thread kernels for matrices narrower than
eight columns) and the restoring expansion runs one column per grid row;
the per-element kernels with a 64-bit division each had taken two thirds
of the BLAKE3 shape's LDE. The ordering half of the fused expansion, the
bit-reversed feed with the row permutation in the scatter, was implemented
behind `MULTI_STARK_SPPARK_FUSED` and measured: equal on the wide shape,
15 to 18 percent behind on the tall ones, so the restoring path is the
default and the evidence is in `bench/sppark-lde-2026-09-17/README.md`.
The full fusion, the expansion inside the transform's first pass, is not
implemented; the stage split bounds what it could still save at about 5
percent of the wide shape's LDE and 15 percent of a tall narrow one's,
against a change to upstream's first-stage kernels. Final resident LDE
ratios against the first-party kernels: 1.36x on the BLAKE3 shape, 2.7x
and 2.2x on the tall narrow ones, 1.07 to 1.22x from 2^18 up with one
shape, 2^20 x 8, at 0.95x; every proof shape from 2^18 rows takes sppark.

Whole units and the whole proof with this build
(`bench/sppark-lde-2026-09-17/README.md`, milestone 4 section): claim 1
2:21.8 to 2:18.9, join 5 51.5 to 48.8 s, Init 415 to 402 s end to end with
the proving union 223 to 192 s, same proof hash and root. Milestone 4's
adaptations, batching, the glue rewrite and the threshold, took the
transforms from 1.2x to 1.4x on the wide shapes and to 2.2 to 2.7x on
the tall narrow ones, and the proving union another 4 percent below
milestone 3; the units move little more because transforms are now a
small share of them. Milestone 5's decision rests on this: the backend
is byte-identical and never slower on a proof shape, so the remaining
questions are the default (opt-in until the Mathlib measurement, since
upstream's fail-fast mode aborts on a CUDA error where the Rust side
panics) and the pins. Fork tip to pin: `176af27` (the patch record in its
README on top of `8b624cd`).

### Second audit (2026-09-17, later)

A second audit of the batched build found the batched host entry's
unchecked word count and stride narrowing, the reversed-powers buffer
outside the panel budget, host twiddle tables still built for transforms
that go through sppark and uploaded by the generic entries, the generic
entries' spans, and that the expansion measured above is the ordering
half of the plan's fusion, not the in-pass one. Fixed in multi-stark
`b14e623`: the Rust side decides a transform's backend once and builds the
first-party tables only for the first-party path, the kernels take sppark
exactly when no table was handed to them (which also closes the race a
backend switch could open between the two sides), the generic entries
label their backend, the batch entry checks its arithmetic and the adapter
its stride, and the reversed powers exist only for the bit-reversed feed
and count against the budget. The record above states the fusion's status
and bound. The change is dispatch plumbing; the milestone-4 replays and
Init run stand as measured with the previous build, and the
compatibility digest and the resident LDE timings reproduce on it.

### The collector crash (2026-09-17, later)

Investigated from a minimal transform up: the host-buffer transforms ran
under the CUPTI collector, every resident panel LDE did not, at any size,
and a collector variant with a fault handler placed the crash inside
CUPTI's hook of `cuMemFreeAsync`. A standalone program
(`bench/sppark-lde-2026-09-17/cupti-freeasync-repro.cu`) isolates it:
CUPTI 2026.2.1 faults when its `MEMORY2` activity kind is on and an async
free is given memory from `cudaMalloc` instead of a pool. The adapter's
scratch now comes from the stream's pool, which is also a device
synchronization fewer per LDE; the collector records the sppark path, and
its first kernel split names the tiled scatter as the next kernel to tune
(60 of 157 ms on the BLAKE3 shape). The adapter's stage timer stays for
quick reads; whole-proof profiles go through the collector again.

## Removing the first-party NTT (map, 2026-09-17)

The question is whether the first-party CUDA transform is still needed
anywhere once sppark is the production NTT. Two measurements answer it.

- Per-shape transform time in the profiled units (the CUPTI attribution in
  `bench/prover-profile-init-2026-09-17`, first-party build): the claim
  spends 9.47 s in first-party transform kernels: 5.52 s on LDEs at
  heights of 2^18 and up, 3.95 s in the quotient's transforms (attributed
  without a shape; they run at 2^22 to 2^26 rows), and no measurable time
  below 2^18; the join 6.55 s, 4.72 s, 1.83 s and none. Every shape in
  the first two groups is faster through sppark (1.07x to 2.7x); the
  third group, where sppark is 0.6 to 0.9x, is a share that rounds to
  zero. The height threshold and the two-backend dispatch exist for it.
- sppark's own limits never bite the prover: the compiled domain is 2^28
  and the largest extended height 2^26; one column pair at 2^26 is 640 MB
  against the 4 GiB panel budget; heights of one are an identity the
  component can answer itself; width zero is handled in Rust.

So no first-party fallback is required for correctness or for speed, and
the design becomes one transform component with assertions where the
second backend used to be. What that removes, by place:

- `multi-stark/cuda/kernels.cu`: the radix-2, -4 and -8 DIF stages and
  tails, `launch_dif`, `bit_reverse_scale_and_shift`, the twiddle kinds
  of the constant cache and the twiddle halves of the constant prewarm,
  the first-party branches of the three dispatch helpers and of
  `coset_lde_create`, the canonicalization passes after first-party
  transforms (sppark's output is canonical), the per-backend metrics. About
  a hundred references to twiddles go with them.
- `multi-stark/src/cuda/mod.rs`: the host twiddle cache and its lock, the
  optional-table helpers, the table parameters on ten FFI entries (23
  parameters), the three backend-label helpers, the `height_inverse`
  arguments (sppark normalizes; the quotient's slice weights keep their
  own factor, which is arithmetic rather than transform plumbing).
- `multi-stark/src/cuda/sppark.rs`: the `Backend` selector, the test lock,
  the height threshold and the three `takes` predicates, replaced by the
  component's single plan; the comparison tests move to the CPU reference
  and the proof digests, which the existing CPU-against-CUDA tests already
  provide once the CUDA side is sppark.
- Features: `cuda-sppark` folds into `cuda` in multi-stark, aiur and
  ix-ffi, and `IX_CUDA_SPPARK` goes from Lake; the fork becomes a hard
  dependency of every CUDA build (the extra nvcc step is about 20 s, and
  CI fetches the fork's pinned revision).
- Settings and docs: `MULTI_STARK_CUDA_NTT` and `_MIN_LOG_HEIGHT` go;
  `_PANEL_BYTES`, `_BATCH_BYTES` and `_STAGE_TIMING` stay; the resident
  bench's first-party mode goes and the recorded CSVs become the baseline.

What is built in the same pass:

1. One immutable transform plan, owned by the component: for a shape
   (height, width, blowup, direction) it fixes the scratch bytes, the panel
   columns and batch groups, and the only constant a coset transform needs,
   the shift powers. Commit, lookup and quotient admission consume the
   plan's scratch figure instead of computing panels separately, and the
   kernels consume the plan instead of reading table pointers. That is the
   audit-prone area, and it collapses to one function.
2. A borrowed-stream entry in the fork: a `stream_t` over the caller's
   `cudaStream_t`, non-owning. The adapter then runs upstream's launches on
   the caller's stream, and the per-batch stream, the two events, the wait
   and the failure-path drain go away; scratch, transforms and the free
   follow one stream's order.
3. The expansion-order experiment deleted: `MULTI_STARK_SPPARK_FUSED`, the
   reversed-powers scratch, the spread kernel and the reversing-scatter
   branches. The measurements stay in the bench directory and the code in
   history. First-stage fusion remains a separate, optional fork change.
4. Metrics with one backend: transform shapes per device stay, the
   taken/declined counters go.

Order: the fork's borrowed stream first (small, independently testable
through the existing adapter tests); then multi-stark in one branch, the
plan type before the deletions so every entry converts against it; then
aiur, ix-ffi and Lake drop the feature forwarding and bump the pin. The
acceptance evidence is the existing CPU-reference and proof-digest tests,
the resident bench against the recorded first-party CSVs, and the claim,
join and Init replays. Expected size: about 600 lines out of `kernels.cu`,
200 out of `mod.rs`, 150 out of `sppark.rs`, and about 150 in for the plan.

Two things this does not remove. The CPU DFT for the generic entries'
tiny matrices (under 2^15 cells) is the right tool there and stays. And
the fork's fail-fast runtime mode becomes the only path on a CUDA error,
an abort where the Rust side panics; converting `CUDA_OK` to returned
status in the fork is possible but is a larger upstream divergence, and
the recommendation is to accept the abort for the prover and record it.
