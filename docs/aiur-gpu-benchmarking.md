# Benchmarking GPU traces and Merkle retention

Status: historical record of the Merkle-retention investigation. The
allocation-admission fixes below enabled successful reuse, but the 24 GiB
trial showed no speedup and used more device memory. The cache policy,
checkpoint/restore APIs, cache statistics and budget selector have now been
removed. GPU trace generation and per-phase memory admission remain.

See the [retention measurements](../bench/tree-cache-2026-09-15/README.md)
for the removal decision and the
[current implementation notes](aiur-gpu-trace-generation.md) for supported
behavior. The descriptions below document the tested cache implementation,
not the current runtime API. The separate
[CPU/GPU trace comparison](../bench/gpu-trace-regenerate-2026-09-15/README.md)
uses the implementation after removal.

## What the existing experiment establishes

The three cases used the same CUDA binary, eight-claim Init manifest, four
resident GPU workers, two execution jobs per worker, and empty proof caches.
CPU traces took 298.17 seconds; GPU BLAKE3 traces with regeneration took
286.27 seconds; GPU traces with a 512 MiB tree allowance took 285.64 seconds.
All produced the same verified root. Each configuration ran once.

GPU generation therefore has a promising end-to-end result to repeat.
The retention case had 21 admissions, 21 reported evictions, and zero hits.
Its 0.63-second difference from regeneration does not measure tree reuse.

The GPU provider checks the compiled BLAKE3 body and prepares immutable seeds
on the host; the proving consumer expands each 176-byte seed into 533
main-trace columns. The measurements above predate packing and used 162
64-bit seed words. Round two rebuilds these seeds
and LDEs. A tree checkpoint owns Merkle nodes and matrix dimensions only.
Successful reuse skips hashing the regenerated LDEs; it does not skip trace
generation or the transforms.

## Problems in the previous implementation

### The early reservation is unrelated to the next allocation

The former `multi-stark/src/cuda/witness.rs::cache_headroom` reserved:

```text
4 × total main LDE bytes + total main trace bytes
  + minimum-free allowance + 256 MiB
```

For a single 2^20-row, 533-column matrix at blowup four, the main trace is
4.164 GiB and its LDE is 16.656 GiB. With a 25% allowance on a 95.59 GiB
device, the reservation is 94.937 GiB before any other circuit. This
explains zero headroom without an allocation failure. The historical
approximately 65 GiB device peak is a sampled observation, not a safe
replacement reservation.

Both batch rounds applied this rule, although round one only commits the
main traces. Lookup, quotient, and FRI already calculate their own workspace
requirements in `src/types.rs`, `src/cuda/mod.rs`, and `src/cuda/pcs.rs`.
Duplicating those calculations in a second whole-proof estimator would
create another policy to keep synchronized with the kernels.

### Existing cache memory is counted twice near the limit

Let `F` be currently available device memory, `C` the device bytes occupied
by optional trees, and `W` the incoming additional allocation requirement.
The previous code computed `F - W` and then trimmed the existing cache to that
size. But `F` already excludes live tree allocations.

When `F >= W`, no eviction is necessary. Otherwise, the required release is
`W - F`; drop optional trees until a fresh memory reading satisfies `W` or
no optional trees remain. Keep host metadata in the explicit cache budget,
but do not count it as reclaimed device memory.

`cuda/kernels.cu::multi_stark_cuda_memory_info` already adds unused default
pool capacity to driver-free memory. Report the components separately and
count reusable capacity once. Persistent allocations are already reflected
in free memory; they must not be charged again as new workspace.

### Later admission cannot evict the remaining optional trees

`batch_round_two` checked the cache before rebuilding stage one. The later
lookup, quotient, and FRI admission calls could evict active LDEs but could
not access the other shards' optional checkpoints. Relaxing the early rule
alone can therefore preserve trees while increasing LDE spill and reload
work.

The batch's optional checkpoints now participate in the existing admission
path. At each allocation boundary:

1. Calculate the upcoming workspace using the allocator's existing shape
   calculations, including simultaneously live outputs and scratch.
2. Read available memory. If it suffices, preserve the cache.
3. Evict optional trees in reverse next-use order, rereading availability
   after release. A selected checkpoint remains optional until restoration;
   the restored tree becomes required data for the active proof.
4. Apply the existing LDE spill/fallback policy if optional eviction is
   insufficient, and retain the existing allocation failure checks.

Cache access is scoped to the owning batch, proving consumer thread and
device. A GPU worker's other systems and another device's batches are not
eviction candidates. The explicit per-batch byte cap still applies.

### The previous diagnostics missed cache outcomes

The batch logged explicit trimming, but the prepared commitment silently
dropped a selected checkpoint under construction pressure. Budget refusal
and restoration incompatibility also lacked distinct outcome reports.
Counting three English log messages could not reconcile every entry.

## Implemented behavior and validation

The whole-proof reservation is removed. Prepared main commitment admits
each trace/LDE construction separately, releases raw traces, then admits
Merkle hashing if no checkpoint was restored. A restored tree does not
reserve space for another tree. Existing lookup, quotient and FRI
allocation checks release optional trees before spilling required LDEs.

`BatchBarrier::tree_cache_monitor()` returns a statistics handle that can
outlive round two without owning any GPU allocations. `snapshot()` returns
a serializable `TreeCacheStats` value containing admissions, reuse hits,
budget/backend/incompatibility refusals, workspace/explicit evictions,
discarded entries, current and peak queued bytes, and LDE spill counts and
bytes. Budget bytes include declared metadata; device bytes count node
allocations only. LDE spill bytes describe logical payload released, not
measured PCIe traffic. A selected tree leaves the queue before restoration;
its final reuse or rejection still updates the same monitor.

Debug events in `multi_stark::tree_cache` include the phase, owning device,
shard, admission requirement and measured memory before/after eviction.
The same requirement drives admission and logging. CUDA witness events
report main commitment path and selected-checkpoint outcomes; batch events
emit the final counters. Enable these with:

```sh
export RUST_LOG=info,aiur::gpu_trace=debug,multi_stark::cuda::witness=debug,multi_stark::tree_cache=debug,multi_stark::batch=debug
```

Focused validation on the four-GPU host:

- Five cache accounting tests cover double charging, minimal deficit
  eviction, metadata, device isolation, explicit budgets and ownership.
- A complete CUDA batch asserts two actual reuse hits and identical,
  verified proof bytes after forced admission eviction. Zero budget is
  checked separately.
- A real GPU pressure fixture checks both individual and batch admission:
  optional trees are released while active LDEs and their openings survive.
- Scope isolation across threads, devices and unwinding, plus existing
  hybrid-opening spill regression tests, pass.
- Aiur's BLAKE3 batch fixture passes normally and with forced LDE spills
  and three-row recovery tiles. Its partial-budget, corruption and
  source-lifetime checks remain intact.
- The four GPU trace fixtures pass, including concurrent source generation
  and checkpoint restoration on devices 0–3. CPU cache tests and the CPU
  regenerated-batch proof regression also pass.

Builds use two Cargo jobs and `MULTI_STARK_CUDA_ARCHS=120`; tests use two
Rayon/stage-one/lookup host workers and one test thread. These are correctness
checks on small fixtures. The separate Init runner records complete-run
timings and structured cache counters. Direct integration with `ix bench`
and detailed phase/transfer timers remain follow-up work.

### Local CLI build, 2026-09-15

The CUDA CLI includes the existing execution/resident-worker instrumentation
and the local backend fixes. The build used Rust 1.98.1, Lean 4.33.1,
CUDA 13.3, two Cargo jobs and the normal release profile. Both executables
are preserved under `target/tree-cache-build/`:

| Artifact | SHA-256 |
| --- | --- |
| `ix-tree-cache-fixed` | `46cc3a1d1051901bf330f5b4f68a705b33133d9a532f95de7c2ef38b29f70da0` |
| `ix-instrumented-before-tree-fix` | `1484d73bb849301570d5780e482cae590ebff322c7a0b917ded40f0f503dddf6` |

`build.json`, `build.log`, source patches, the new `tree_cache.rs`, resolved
lockfile and Cargo configuration are beside the executables. The build
changed only multi-stark's resolution to the local path; all other locked
packages stayed identical. The tracked lockfile and Cargo configuration
were restored afterward. `.lake/build/bin/ix` currently contains the fixed
build too, but a subsequent ordinary rebuild will use the tracked backend
pin. The recorded trials use the saved executables. CLI startup passes.

## Planned benchmark interface

Extend the existing `ix bench` machinery with a fixture mode for the
resident prover. The unit of measurement is the complete `.ixe`/`.ixes`
pair, with its hashes and protocol parameters recorded. Reuse the
[benchmark row contract](benchmarking.md#the-row-contract), watchdog, and
comparison/reporting code.

The prover should emit results directly. Use a companion structured report
for verification/root identity, cache outcomes, per-device detail, and
configuration; keep numeric benchmark measures in the standard rows.
Missing reports and failed processes are failed trials. Require explicit
verified completion and the expected claim/join counts, with no reused
proofs. A verified zero-hit cache trial remains useful policy evidence,
but cannot satisfy the gate for measuring a reuse benefit.

Record at least:

| Layer | Measurements |
| --- | --- |
| Complete run | wall time, CPU time, peak RSS, verified root, completed/reused work counts |
| Batch and shard | main preparation, main commit, lookup, quotient, FRI, verification times |
| Main commitment | generated rows, seed preparation bytes, generation/transform/hash times, actual backend path |
| Retention | admissions, hits, refused entries, evictions by reason, peak retained bytes |
| Device memory | driver-free bytes, pool reserved/used bytes, admission target, LDE spill bytes, sampled VRAM/utilization |

Seed preparation volume is not PCIe traffic: lookup recovery can upload
seeds again. Phase timers must include completion of the work they name;
submission time alone is insufficient. Overlapping CPU/GPU phase totals
must not be added together as wall time. Label sampled VRAM maxima as such;
use allocator high-water measurements where available.

Record the main commitment path because all-host inputs with no checkpoint
use the existing PCS path, whereas a restored checkpoint selects the
prepared path. Otherwise a measured retention difference can also include
a change in commitment scheduling.

The runner should record binary and source identities, dirty diffs, fixture
hashes, effective CPU affinity, GPU identities and driver, complete relevant
`AIUR_*`/`MULTI_STARK_CUDA_*` settings, and proof parameters. Each trial gets
a fresh proof cache and the same execution/sharding configuration. Preserve
each trial's results as it finishes; derive comparisons from those results.

## Measured workload and budget selection

The frozen eight-claim Init fixture has seven joins and 17 proving batches.
Every trial starts with a fresh proof cache, uses all four GPUs, and checks
the verified root and generated row count. The process has a 15-minute
watchdog; its outer scope caps RAM at 400 GiB and disables swap. Trials
take approximately five minutes. The runner does not rebuild or repartition.

The initial comparison uses GPU trace generation throughout: the preserved
old backend with regeneration, the fixed backend with regeneration, and
the fixed backend with 512 MiB of trees per batch. Eight trials completed;
the final trial was interrupted when the sweep was stopped. Its partial
output is excluded explicitly. A single additional fixed-backend trial
uses a 24 GiB allowance. See the linked report for individual timings,
cache outcomes, resource peaks and limitations.

512 MiB came from the earlier experiment and is not a hardware limit or a
tuned recommendation. The diagnostic pilot recorded 91 tree candidates:
32 have 4 GiB node allocations, and the largest batch totals approximately
21.1 GiB. Each checkpoint also carries metadata, so a 4 GiB cap cannot
admit a tree with a full 4 GiB node allocation. A 24 GiB cap can hold the
observed largest batch; actual allocation pressure can still evict trees.
The byte cap applies separately to each batch on its owning GPU.

The 512 MiB runs each reused 15 trees and refused 76 for lack of budget,
with no workspace evictions or LDE spills. Their small timing differences
change sign across repetitions. The 24 GiB trial reused all 91 trees, with
zero refusals, evictions or spills, but took 290.06 seconds versus 284.54
seconds median without caching. Sampled peak device memory increased from
65.35 to 81.78 GiB. This run demonstrates successful retention, with no
measured throughput benefit. One larger-budget trial cannot establish a
small performance change. No further sweep is scheduled.
