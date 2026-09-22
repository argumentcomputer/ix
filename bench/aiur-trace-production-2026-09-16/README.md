# Generated BLAKE3 production dispatch

This checkpoint wires generated BLAKE3 traces into the prover for IxVM,
MultiStark and ixAggr. **No performance benchmark was run for this checkpoint.**
The earlier [microbenchmark](../aiur-trace-cuda-2026-09-16/README.md) remains
historical evidence for its frozen binary.
The subsequent [production replay](../aiur-trace-replay-2026-09-16/README.md)
completes the deferred pair: identical verified proofs, 23.49 s handwritten
versus 23.55 s generated proving time on one FLT join.

## Behavior

- Build with `cuda-trace-codegen` on `aiur` or `ix-ffi`, or set
  `IX_CUDA_TRACE_CODEGEN=1` for Lake. The feature includes CUDA.
- Set `AIUR_GPU_TRACE=generated` and `AIUR_TRACE_ONLY_LOOKUPS=1` before
  constructing the proving systems. `cpu` and `blake3` remain available.
- Registration checks the complete bytecode library, grouping, seed widths,
  and compiled CUDA contract before proof preparation. A missing feature or
  unrecognized/stale library fails explicitly.
- Registration happens once per system and is shared by its `on_device`
  derivatives. Both proving rounds dispatch through that provider.
- Coverage is deliberately partial: BLAKE3 only, at function 33 in IxVM
  and function 86 in MultiStark and ixAggr. Registration logs coverage totals;
  debug logs identify CPU fallbacks for uncovered nonempty function circuits.
  Memory and byte-table circuits use CPU traces. This is not full strict mode.
- Seed packing and device generation have `aiur/codegen_seeds` and
  `aiur/codegen_device_rows` profile spans. Debug dispatch includes rows,
  width, seed bytes and span count.

`ix codegen --trace-bundle` regenerates the host writers, registries, CUDA
units and production manifest together; `--trace-bundle --check` checks
all those files without writing. Individual Rust emission also accepts
`--trace-functions`. Partial selection keeps full-library compatibility
validation. The fixture and production manifests are separate, so fixture
regeneration cannot erase production units.

The expected-bytecode constructors are emitted per function with inlining
disabled. A monolithic constructor made the release compiler run for several
minutes before it was interrupted. The split version's focused release build
finished in 31.71 seconds with existing CUDA objects and dependencies; this is
not a cold-build timing or a runtime performance measurement.

## Correctness and build checks

All checks used CPU affinity 0–7 and eight-thread limits.

- [19 CPU tests](cpu-tests.log) passed with the original backend dependency
  and no CUDA feature.
- [26 GPU tests](gpu-tests.log) passed; the ignored performance test stayed
  ignored. Coverage includes exact canonical cells for the selected function
  in each full production library, stale-library rejection, explicit CPU
  fallback, halos, grouped rows, mixed codecs and concurrent uploads on all
  four GPUs.
- [Two proof tests](proof-tests.log) passed through normal prepared-witness
  dispatch. Both handwritten and generated BLAKE3 proofs verify and equal
  CPU-trace proof bytes. Regeneration releases sources across the barrier,
  detects altered rows, and device-derived systems share registration.
- [Release test build](cuda-build.log), [FFI feature check](ffi-check.log),
  [legacy CUDA check](legacy-cuda-check.log), and Lake configuration typecheck
  passed. The FFI check used `parallel,cuda-trace-codegen`.
- A [negative feature check](missing-feature.log) confirms that a CPU-only
  binary rejects `AIUR_GPU_TRACE=generated` before building the system. The
  test failure in that log is intentional and its diagnostic was checked.
- [Production bundle](generated-check.log), [fixtures](fixtures-check.log)
  and [existing execution modules](execution-check.log) reproduce exactly.

The GPU build still requires the paired backend shared-header/metadata patch
from [the preceding checkpoint](../aiur-trace-cuda-2026-09-16/multi-stark.patch).
The test build used a temporary Cargo patch configuration, and the checked-in
lockfile retains its original backend source. Machine paths, artifact hashes
and source hashes are in [metadata.json](metadata.json).

## Reproduction

For regeneration, use a current CLI from this source revision:

```sh
ix codegen --trace-bundle --check
```

With the backend patch configuration described in the preceding checkpoint:

```sh
taskset -c 0-7 env CARGO_BUILD_JOBS=8 RAYON_NUM_THREADS=8 OMP_NUM_THREADS=8 \
  NVCC=/usr/local/cuda-13.3/bin/nvcc MULTI_STARK_CUDA_ARCHS=120 \
  CARGO_TARGET_DIR=/tmp/aiur-trace-target \
  cargo --config /tmp/trace-backend.toml test -p aiur --lib \
  --release --features cuda-trace-codegen --offline -j8 --no-run

taskset -c 0-7 env RAYON_NUM_THREADS=8 OMP_NUM_THREADS=8 \
  AIUR_GPU_TRACE=cpu AIUR_TEST_GPU_DEVICES=0,1,2,3 \
  "$test_binary" trace_codegen --test-threads=8

taskset -c 0-7 env RAYON_NUM_THREADS=8 OMP_NUM_THREADS=8 \
  AIUR_GPU_TRACE=cpu AIUR_TRACE_ONLY_LOOKUPS=1 \
  "$test_binary" blake3_regenerated_batch_matches_cpu --test-threads=1
```

Preserve and restore Cargo.lock around a temporary backend path patch.
The interpreter-based generation checks here used the private Lean overlay
and native BLAKE3 libraries recorded in the metadata; the complete CLI was
not rebuilt or relinked for this checkpoint.

## Deferred comparison

The next performance measurement is one cached-join pair. Build the CLI
from this checkout with the backend patch and use a cache compatible with
that compiler revision. Use one binary, one GPU, eight CPU cores, the same
join slot and trace plan, and change only `AIUR_GPU_TRACE` between `blake3`
and `generated`. The old pre-merge cache and its proof hash are not a
validated baseline for this revision.

Once a compatible binary/cache are available, the command shape for each
mode is:

```sh
taskset -c 0-7 env CUDA_VISIBLE_DEVICES=3 \
  RAYON_NUM_THREADS=8 OMP_NUM_THREADS=8 LEAN_NUM_THREADS=8 \
  AIUR_GPU_TRACE="$mode" AIUR_TRACE_ONLY_LOOKUPS=1 \
  AIUR_MAX_PIECE_LOG_HEIGHT=24 AIUR_TRACE_SHARD_MAX_CELLS=1500000000 \
  AIUR_TREE_CACHE_BYTES=0 AIUR_AGGREGATE_CACHE_DIR="$cache" \
  AIUR_PROFILE="$output/spans.jsonl" \
  "$ix_binary" aggregate --ixe "$mathlib_ixe" --ixes "$mathlib_ixes" \
  --trace-shards --max-ram 230 --direct-joins --jobs 1 \
  --no-write --reprove-slot "$join_slot"
```

Require identical proof hashes, verified verdicts and per-piece row plans
before comparing proving time, preparation/device spans or peak memory.
No cached join, Init/Mathlib run, or timing microbenchmark was launched here.
Broader function selection, memory/byte primitives, full strict coverage and
replacement of the handwritten provider remain later steps.
