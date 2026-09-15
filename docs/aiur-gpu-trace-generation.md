# GPU BLAKE3 trace generation

GPU generation is opt-in and runs inside the resident GPU workers. The
Merkle-tree cache has been removed from ix and the local multi-stark
checkout. The [retention experiment](../bench/tree-cache-2026-09-15/README.md)
reused every tree with a 24 GiB allowance, but showed no end-to-end speedup
and increased sampled peak device memory from about 65 to 82 GiB.

The local backend changes are not yet reflected in ix's tracked dependency
pin (`f54b44f4`). Build these checkouts together with a local Cargo path
override until the backend is committed and the pin is updated. The
[CPU/GPU comparison](../bench/gpu-trace-regenerate-2026-09-15/README.md)
uses one frozen binary built with that override.
With the cache removed, the measured CPU/GPU pair took 304.11 / 286.06
seconds: GPU trace generation used 5.93% less wall time and 16.02% less
process CPU time. Both verified the same root with zero LDE spills. These
are one trial per mode; the linked report includes the full measurements.

## Controls

Build with the existing `cuda` feature. For trace-sharded proving:

```sh
export AIUR_TRACE_ONLY_LOOKUPS=1
export AIUR_GPU_TRACE=blake3
```

`AIUR_GPU_TRACE=cpu`, or an unset selector, uses the CPU trace builder.
There is no tree-cache budget setting. Trace-only lookups select
`Retention::Regenerate`: round one keeps shard headers, and round two
rebuilds the traces, LDEs and Merkle trees. The existing full-stage
`Retention::Retain` policy remains available for witnesses with ordinary
lookup payloads.

Keep the same resident-worker command, proof parameters, shard cell budget
and execution concurrency when comparing trace generators. Only the BLAKE3
main-trace writer changes; other circuits use their host trace builders.

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
streamable. Host-only inputs use the existing PCS path.

## Memory and lifetime

Generated sources contain compact immutable seeds. After committing a shard
in regeneration mode, round one drops its main traces, LDEs, Merkle nodes,
lookup witnesses and generators. Only the public header and claims cross
the batch barrier. Round two prepares new seeds and reproduces the original
commitment; a mismatched header fails before the shard proof is accepted.

The generated commitment path admits each trace/LDE construction separately,
releases raw device rows, then admits Merkle hashing. The old whole-proof
cache reservation is gone. Lookup, quotient and FRI retain their existing
workspace checks and LDE spill/recovery paths. Unused CUDA pool capacity is
counted once in available memory. Execution concurrency and shard cell
budgets do not depend on a tree cache.

`multi_stark::cuda::witness` debug events report the main commitment path
and logical LDE spill bytes. `aiur::gpu_trace` reports generated rows and
seed preparation bytes. Neither byte count measures PCIe traffic.

## Focused validation

Cell tests compare every canonical value with the bytecode builder across
stages 0–7, varied inputs and multiplicities, filtered rows, padding,
partial ranges and wrapped halos. Concurrent tests on GPUs 0–3 reproduce
the same commitments with fresh generation. Callback-failure and batch
barrier tests check that generated sources are released.

The sharded BLAKE3 batch test verifies the same proof bytes as CPU traces.
It also rejects corrupted regenerated values at the header check. This
complete proof passes with normal residency and with forced LDE spills
using three-row generated lookup recovery tiles:

```sh
export MULTI_STARK_CUDA_TRACE_FORCE_SPILL=1
export MULTI_STARK_CUDA_LOOKUP_TRACE_TILE_ROWS=3
```

The tile override affects generated lookup sources only, with a range of
1–65,536. These controls are for validation, not timed comparisons.

Run `gpu_trace::tests` and `gpu_blake3_regenerated_batch_matches_cpu` with
one test thread. Bound host work with `RAYON_NUM_THREADS`,
`MULTI_STARK_CUDA_STAGE1_THREADS` and `MULTI_STARK_CUDA_LOOKUP_THREADS`.
`AIUR_TEST_GPU_DEVICES=0,1,2,3` selects devices for the concurrent fixture;
it defaults to device 0.

Re-export the compatibility body from both current Lean compilers with:

```sh
lake env lean -j1 --run crates/aiur/cuda/export_blake3_body.lean
rustfmt --edition 2024 crates/aiur/src/gpu_trace/blake3_body.rs
```

Any updated body requires revalidating the kernel against the bytecode
oracle. The benchmark report records the tested binary, fixture hashes,
settings, verified root, timings and resource peaks.
