# GPU BLAKE3 traces and bounded Merkle checkpoints

The opt-in implementation is in the main ix and multi-stark checkouts,
using the existing local multi-stark Cargo patch and resident workers.
The [design plan](aiur-gpu-trace-generation-plan.md) remains the benchmark
and enablement plan. The first four-GPU Init comparison measured a 4.0%
wall-time reduction with GPU traces; the tree cache had no reuse hits.
See the [measurements and logs](../bench/gpu-trace-init-2026-09-15/README.md).

Build with the existing `cuda` feature. Enable GPU BLAKE3 generation while
keeping regeneration across the barrier:

```sh
export AIUR_TRACE_ONLY_LOOKUPS=1
export AIUR_GPU_TRACE=blake3
export AIUR_TREE_CACHE_BYTES=0
```

Run the same resident-worker command, proof parameters, cell budget and
execution concurrency as the reference. `AIUR_GPU_TRACE=cpu`, or an unset
selector, uses the CPU trace builder. To measure tree reuse separately,
keep GPU generation enabled and set an allowance, for example:

```sh
export AIUR_TREE_CACHE_BYTES=536870912
```

This is a **512 MiB maximum per batch on its owning GPU**, including metadata.
One batch runs per resident worker; four workers can use at most four
allowances, subject to device headroom. Zero explicitly selects `Regenerate`.
An unset variable preserves the existing policy, including the trace-only
guard against full `Retain`. Invalid selectors and budgets fail explicitly.
On Init, the headroom rule evicted all 21 retained trees before reuse.
Keep this allowance at zero for that workload until its workspace estimate
is refined; increasing the cache budget alone will not fix those evictions.

Rust callers can select `Retention::MerkleTrees { max_bytes }` and inspect
or evict a barrier's cache with `tree_cache_bytes()` and
`trim_tree_cache(max_bytes)`. Both rounds keep streaming witness production.
Debug tracing in `aiur::gpu_trace`, `multi_stark::cuda::witness` and
`multi_stark::batch` reports seed sizes, tree retention, reuse and eviction.

**Trace contract.** The provider checks the complete compiled body, operands,
self-call identity and layout. The current IxVM and aggregation compilers
produce identical bodies after substituting the self-call index. Other
circuits and unsupported layouts use the reference builder. Empty circuits
remain inactive; unsupported seed stages or byte values also select the
reference builder.

Each real row uploads a 176-byte seed: one stage byte, 128 input bytes,
32 recorded output bytes, a canonical 64-bit multiplicity, and seven explicit
padding bytes. Extraction checks the stage and byte bounds before narrowing.
The Rust and CUDA layouts have matching compile-time size and offset checks.
The kernel writes the same 533 main columns.
The recursive-call output auxiliaries use the recorded result. The compiled
lookup graph still emits the recursive-call and return messages. Execution
and query recording are unchanged.

`PreparedWitness` mixes host matrices with owned `TraceSource` generators.
The existing CPU producer prepares seeds; the admitted consumer generates
device traces. An LDE handle owns its generator until the last consumer
finishes. Expansion and recovery upload at most 65,536 seed rows per tile.
Lookup recovery generates a tile with one wrapped halo row after raw-trace
release or LDE eviction. Seed allocations use the backend's per-device
CUDA stream pool. Uploads lease one of four reusable portable pinned buffers,
shared across devices. Each holds at most 65,537 seeds (a tile plus its halo),
so pinned seed staging is bounded to 44 MiB plus 704 bytes per process.
The lease lasts until the per-thread CUDA stream finishes, including on error.

The full expanded trace and LDE must still fit during construction. The
prepared path reserves device headroom, releases raw traces and can spill
LDEs to host storage within the current proof. Spilled height groups stay
together for host hashing. An oversized matrix fails admission with a request
to reduce the shard cell budget; GPU generation does not make its FFT
streamable. CPU matrices without a checkpoint use the existing PCS path.

**Barrier lifetime.** A checkpoint owns only Merkle nodes and ordered matrix
dimensions. It owns no LDE, materialization closure, host matrix or seed copy.
Deferred host LDE workers are joined and their results released before
checkpoint extraction finishes. Round two prepares seeds again from the
original record. Nodes occupy `64 * maximum_extended_height` bytes, plus
metadata, so a node buffer exactly equal to the allowance does not fit.

Cache admission conservatively reserves four times the estimated main LDE
bytes, main-trace bytes, the existing minimum-free allowance, and 256 MiB.
Later shard entries are evicted first. The selected checkpoint is discarded
before spilling active LDEs if construction needs its memory. Execution
concurrency and shard cell budgets are not reduced to preserve trees.
Compact seeds fit within the existing host-witness estimate because they
replace larger matrices; execution lookahead is not increased.

**Deferred experiment: correct the tree-cache workspace estimate.** In the
Init benchmark, all 21 retained trees were evicted before round two could
reuse them. No CUDA allocation failed. These were preemptive evictions
caused by the workspace estimate, despite device-memory peaks near 65 GiB.
The current reservation is:

```text
4 × main LDE bytes + main trace bytes + minimum-free allowance + 256 MiB
```

The default minimum-free allowance is 25% of device memory. For just one
2^20-row, 533-column BLAKE3 matrix at blowup four, this reserves 94.94 GiB
on a 95.59 GiB device, before accounting for other circuits and persistent
allocations. The resulting zero cache headroom discards even small trees;
raising the tree-cache byte allowance alone cannot address it.

The follow-up is deferred. Replace the blanket LDE multiplier with an
estimate of the peak simultaneously live allocations, derived from the
actual main, lookup, quotient and FRI shapes and their lifetimes. Account
for existing resident allocations and reusable pool capacity once. Preserve
the explicit cache cap, proof-workspace admission checks, and eviction when
the next phase actually needs the memory; retain only tree nodes across
the barrier.

For that experiment, log predicted workspace, available device memory,
cache bytes and eviction reasons per shard/device. Repeat the fixed Init
comparison with GPU generation enabled, cache budgets of zero and 512 MiB,
and unchanged execution concurrency. Require actual tree reuse, identical
verified roots, and measured RSS/VRAM peaks; also exercise forced eviction
to confirm regeneration remains correct. Keep `AIUR_TREE_CACHE_BYTES=0`
until this policy is implemented and measured.

Round two attaches newly generated LDEs to a saved tree without rehashing on
a hit. Restoration checks the device, ordered dimensions and main-trace
subgroup domain. The batch binds the entry to its original shard and
immutable system. The round-two header check remains, but a cached root
alone does not validate regenerated values. Independent commitments and
complete proof verification are part of the tests.

**Focused validation.** Tests cover every cell and canonical representation
across stages 0–7, varied states and multiplicities, filtered rows, padding,
partial ranges and wrapped halos, using the bytecode builder as the oracle.
Trace-sharded BLAKE3/byte-table batch proofs match CPU-reference proof bytes
with cache hits, partial admission, zero allowance and eviction. Ownership tests
check that a checkpoint releases its source and that callback failures clean
up. Device fixtures compare generation and restoration concurrently on GPUs
0–3. CUDA memcheck exercises the bounded fixtures. These checks passed on the
four-device box, along with a CPU proof regression and `ix-ffi`'s CUDA build
check. Complete sharded proofs passed with normal residency and forced spills.

Forced-spill proofs use three-row generated lookup tiles and verify fully.
Corrupting a recursive-call auxiliary changes an independently computed
commitment and fails verification with the original cached tree. Recovery
can be exercised with:

```sh
export MULTI_STARK_CUDA_TRACE_FORCE_SPILL=1
export MULTI_STARK_CUDA_LOOKUP_TRACE_TILE_ROWS=3
```

The tile override affects generated lookup sources only, with a range of
1–65,536. Forced spill applies to every LDE in the prepared commit path.
These controls are for validation, not normal benchmark settings.

Build focused tests with the appropriate GPU architecture:

```sh
MULTI_STARK_CUDA_ARCHS=120 cargo test -p aiur --lib --features cuda --no-run
```

Run the `gpu_trace::tests` and `gpu_blake3_batch_tree_checkpoint_roundtrip`
filters with one test thread; host worker pools keep their normal parallelism.
On a shared machine, bound host work with `RAYON_NUM_THREADS`,
`MULTI_STARK_CUDA_STAGE1_THREADS` and `MULTI_STARK_CUDA_LOOKUP_THREADS`.
`AIUR_TEST_GPU_DEVICES=0,1,2,3` selects devices for the ownership fixture;
it defaults to device 0.

Re-export the compatibility body from both current Lean compilers with:

```sh
lake env lean -j1 --run crates/aiur/cuda/export_blake3_body.lean
rustfmt --edition 2024 crates/aiur/src/gpu_trace/blake3_body.rs
```

Any updated body requires revalidating the kernel against the bytecode oracle.
The full eight-claim Init workload, its joins and root wraps passed on four
GPUs with the same verified root for CPU generation, GPU generation and the
tree-cache mode. Wall times were 298.17, 286.27 and 285.64 seconds respectively;
the latter had zero cache hits. Peak RSS was 194.00, 190.24 and 192.15 GiB.
These are single runs per configuration. Repeated comparisons, single-GPU
measurements, Mathlib throughput and an effective tree-cache policy remain
enablement gates.
