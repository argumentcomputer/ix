# Aiur trace codegen: handoff

State of the generated GPU trace pipeline on `sb/aiur-trace-sharding-gpu`
(ix `c2c87646`) with multi-stark `sb/trace-sharding-gpu` (`3374357`),
reviewed 2026-09-16. The [implementation plan](aiur-cuda-trace-codegen.md)
holds the design rationale and the step ladder; this document records what
is built, how to drive it, the verified defects, and the recommended order
of the remaining work.

## Summary

The compiler from final Aiur bytecode to seed packers and row writers is
complete for every opcode and control form, and it is validated end to end
for one function. Production dispatch is limited to `blake3_compress` in each
of the three programs. The generated path reproduces the handwritten BLAKE3
provider's proofs with equal proving time and slower seed preparation.

Nothing in the branch yet establishes that generation pays for any other
function. The static inventory says most functions ship a canonical seed
nearly as wide as their row and retain most of their arithmetic on the host.
The next major piece of work is therefore the bounded seed schema, not wider
coverage. The concrete defects below should be fixed first.

## Where things live

| Stage | Location |
| --- | --- |
| Trace plan: value ids, column spans, external reads, dependency sets | `Ix/Aiur/Stages/TracePlan.lean` |
| Static inventory as JSON (`ix codegen --trace-report`) | `Ix/Aiur/Stages/TraceReport.lean` |
| Rust emitter: `pack`, `pack_u8`, `pack_checked`, `write` per function | `Ix/Aiur/Stages/TraceCodegen.lean` |
| CUDA emitter and Rust registry | `Ix/Aiur/Stages/TraceCuda.lean` |
| Library fingerprint (Lean side) | `Ix/Aiur/Stages/TraceContract.lean` |
| Bundle selection and CLI flags | `Ix/Cli/CodegenCmd.lean` (`traceBundle`) |
| Runtime: seed context, bound writers, structural bind | `crates/aiur/src/trace_codegen.rs` |
| Library fingerprint (Rust side), grouping validation | `crates/aiur/src/trace_codegen/contract.rs` |
| Seed spans, device dispatch, CPU mirror | `crates/aiur/src/trace_codegen/cuda.rs` |
| Registry of the three programs, registration | `crates/aiur/src/trace_codegen/programs/mod.rs` |
| Generated Rust (checked in) | `crates/aiur/src/trace_codegen/programs/{ixvm,multi_stark,ix_aggr}{,_cuda}.rs` |
| Generated CUDA (checked in) and digest manifest | `crates/aiur/cuda/generated/production/` |
| Shared uploader, pinned staging, seed codec | `crates/aiur/cuda/trace_runtime.{cu,cuh}` |
| Device helpers: inverse, word packing, carries | `crates/aiur/cuda/trace_primitives.cuh` |
| Provider selection (`AIUR_GPU_TRACE`) | `crates/aiur/src/gpu_trace/mod.rs` |
| Per-shard dispatch | `crates/aiur/src/shard.rs` (`prepare_shard_witness`) |
| nvcc build, manifest digests, incremental objects | `crates/aiur/build.rs` |
| multi-stark: generator trait, device view | `src/witness.rs`, `src/cuda/mod.rs` |
| multi-stark: generated commit, spill, hybrid tree | `src/cuda/witness.rs` |
| multi-stark: lookup admission and graph path | `src/types.rs` (`accelerated_lookup_commit`) |
| multi-stark: shared field header | `cuda/goldilocks.cuh` |

Data flow: CPU execution finalizes the record and IO buffer. Per shard, the
generated packers read them immutably and produce one seed span per member
run, `[multiplicity, inputs, resolved external reads]`, either full-width or
in the guarded u8 codec. The shard witness carries `TraceSource::Generated`
and a shape-only lookup witness. multi-stark allocates the device tile and
calls back `write_device_rows`; the uploader leases a pinned slot, uploads,
launches one thread per row, and synchronizes. The lookup-graph kernel
regenerates row tiles with a one-row halo through the same callback, so raw
traces are released after commitment.

## Controls

| Control | Effect |
| --- | --- |
| `IX_CUDA_TRACE_CODEGEN=1` (Lake) or `--features cuda-trace-codegen` (Cargo) | Compiles the runtime and the generated units; implies `cuda` |
| `AIUR_GPU_TRACE=cpu\|blake3\|generated` | Provider; `blake3` is the handwritten kernel, `generated` the compiled one |
| `AIUR_TRACE_ONLY_LOOKUPS=1` | Required by both GPU providers |
| `MULTI_STARK_CUDA_ARCHS=120` | nvcc architecture; `-gencode=arch=compute_120,code=sm_120` |
| `MULTI_STARK_CUDA_TRACE_FORCE_SPILL=1` | Validation only: spill every LDE, exercise generated recovery tiles |
| `MULTI_STARK_CUDA_LOOKUP_TRACE_TILE_ROWS=3` | Validation only: tiny regeneration tiles |
| `AIUR_TEST_GPU_DEVICES=0,1,2,3` | Devices for the concurrent fixture |

Registration happens once per `AiurSystem` and is shared across the
per-device clones. A library whose fingerprint matches no generated program
fails before proving with a regeneration hint. Uncovered circuits fall back
to CPU rows with a debug log per circuit and a coverage summary at
registration.

## Commands

```sh
# Regenerate every checked-in artifact from the current compiler, or check them.
lake exe ix codegen --trace-bundle
lake exe ix codegen --trace-bundle --check

# Static inventory, one JSON document.
lake exe ix codegen --trace-report --target ixvm

# Single-function experiments to stdout.
lake exe ix codegen --trace-rust --target ixvm --trace-functions 33
lake exe ix codegen --trace-cuda --target ixvm --trace-functions 33

# Planner fixtures.
lake exe IxTests aiur-trace-plan

# Rust parity tests without CUDA (scalar packers and writers against populate_row).
cargo test -p aiur trace_codegen::tests

# GPU tests and the two-round generated proof.
NVCC=/usr/local/cuda-13.3/bin/nvcc MULTI_STARK_CUDA_ARCHS=120 \
  cargo test -p aiur --release --features cuda-trace-codegen -- --test-threads 1
```

The paired production replay lives in
[`bench/aiur-trace-replay-2026-09-16`](../bench/aiur-trace-replay-2026-09-16/README.md):
same binary, GPU, cores, cache and slot, only `AIUR_GPU_TRACE` differs.
Proof and trace-plan equality are required before timings are compared.

## Evidence

| Check | Result |
| --- | --- |
| Planner fixtures | 35 pass |
| CPU parity tests | 19 pass |
| GPU tests, including four-device staging and forced spill | 26 pass |
| Two-round generated BLAKE3 proof | Same bytes as CPU traces; altered regeneration rejected |
| Paired FLT join replay, one pair | Same proof and six-piece plan |
| Proving time, handwritten vs generated | 23.49 s vs 23.55 s |
| Seed preparation, handwritten vs generated | 2.33 s vs 2.78 s |

One pair supports "comparable", not a speedup. The generated packer is
slower because it is generic; the handwritten one narrows in place.

## Coverage

`traceBundle` selects `blake3_compress` only. The three production CUDA
units differ in namespace and fingerprint alone. Every other circuit takes
the CPU path, including the memory and byte-table circuits, which have no
generated primitives yet. The registration test asserts that exactly one
function per program is generated; widening coverage requires updating it.

The generated Rust modules embed the complete expected bytecode of each
library for the structural bind, which is most of their size:

| Module | Lines | Writer code | Expected bytecode |
| --- | ---: | ---: | ---: |
| `programs/ixvm.rs` | 6617 | ~1825 | ~4790 (798 functions) |
| `programs/multi_stark.rs` | 3605 | ~1825 | ~1780 |
| `programs/ix_aggr.rs` | 3707 | ~1825 | ~1880 |

## What the inventory says

From `bench/aiur-trace-plan-2026-09-15/functions.csv`, 1,220 constrained
functions across the three programs, static sites only, no row weights:

| Measure | Functions |
| --- | ---: |
| Canonical seed within 1.5x of the row width | 833 |
| With external reads (call, load, IO, bigint) | 1,149 |
| Host preparation sites at or above GPU row sites | 321 |
| Optimistic all-u8 expansion of 4x or better | 1,055 |
| With measured real rows | 0 |

Summed over the library, host preparation retains 84% as many arithmetic
sites as the row writers execute, because call and load keys must be
computed to resolve external reads. Under the canonical codec, wider
coverage mostly re-uploads the same bytes and adds a second host pass. The
all-u8 codec would change that for most functions, but it is a per-span
all-or-nothing guard with no bounds analysis behind it, so its hit rate on
real records is unknown. Row weights are still `null`; the inventory
cannot yet say which circuits carry the bytes.

## Verified defects and hazards

Ranked. File references are to this branch pair.

1. **Lookup admission budgets the wrong kernel after a spill.** multi-stark
   `src/types.rs:970` decides `graph_path` from LDE residency and sizes the
   admission budget accordingly, while `src/cuda/mmcs.rs:183`
   (`resident_with_trace`) also accepts generator-backed and retained-trace
   LDEs, so the graph kernel with regeneration tiles runs under the direct
   path's budget once an LDE has spilled. Correctness holds and the forced
   spill test passes, but behavior near the device limit is unverified in
   either direction. Fix: make the admission predicate match
   `resident_with_trace`.
2. **Per-row codec selection fragments spans and packs twice.**
   `crates/aiur/src/trace_codegen/cuda.rs:177` runs the u8 packer per row
   and, on a guard failure, runs the full-width packer again. Each encoding
   change closes the span, and dispatch at `cuda.rs:350` performs one
   upload, launch and synchronize per span. Rows that alternate between
   fitting and not fitting a byte produce one-row spans and serialized
   launches. BLAKE3 never alternates, so the replay cannot show this.
   Pointer-heavy and general field functions will. This is resolved by a
   per-value seed schema chosen in the plan rather than at runtime.
3. **The trace-bundle freshness check is not in CI.**
   `ix codegen --trace-bundle --check` compares Rust writers, registries,
   CUDA sources and the manifest against Lean output, but
   `.github/workflows/ci.yml:40` runs only the ordinary `codegen --check`.
   A stale Rust module is caught only at registration.
4. **Handwritten BLAKE3 tile cap.** `crates/aiur/src/gpu_trace/mod.rs:237`
   does not clamp tiles to the kernel's 65,537-row limit, which
   `crates/aiur/cuda/blake3_trace.cu:151` enforces by returning an error.
   The generated path clamps. Latent while multi-stark tiles at 65,536 rows
   plus one halo row.
5. **Preparation failures abort the process.** `gpu_trace/mod.rs:117`
   panics inside a rayon map on any packing error; the CPU mirror in
   `cuda.rs` uses `expect` on decoded seeds. Ordinary byte-guard failures
   already fall back to canonical seeds, so these fire on inconsistent
   records or resource failures, not on ordinary inputs. Decide whether
   resource failures should return an error before a strict mode and a
   normal mode diverge.
6. **The multi-stark pin is a feature-branch commit.** `3374357` adds
   `links = "multi_stark_cuda"` and the `cargo:include` line that
   `crates/aiur/build.rs:44` reads through `DEP_MULTI_STARK_CUDA_INCLUDE`.
   Any earlier rev fails that build script's `expect`. The commit must land
   on multi-stark main before the aiur feature can. The message of ix
   `0369233d` names an older pin and is stale.

Lower priority, to measure as coverage grows:

- `inverse` in `trace_primitives.cuh` is a full Fermat exponentiation.
  Default-arm inverses use constant tables only for case values below 16;
  `eqZero` with an auxiliary column always exponentiates.
- One thread writes its whole row, so stores across a warp are strided by
  the row width. The plan defers a layout change until measured.
- Byte guards return an error code only for binary u8 operations; shifts
  and bit decomposition trust their input. A diagnostics gap on invalid
  records, not a correctness gap on valid ones.
- The fingerprint hashes assertion and debug message strings, so a message
  edit invalidates all generated artifacts.
- The test manifest's fixture units are compiled into the CUDA archive
  under the feature. Release links pull only referenced objects, so they do
  not reach production binaries, but the build pays for them.
  Content-addressed objects in `OUT_DIR` are never pruned.
- `bench/aiur-trace-replay-2026-09-16/__pycache__/` holds two committed
  `.pyc` files.

## Recommended order

1. Fix lookup admission in multi-stark so budgeting and execution agree on
   the kernel, and re-run the forced-spill proof at a tight
   `MULTI_STARK_CUDA_MIN_FREE_BYTES`.
2. Add `lake exe ix codegen --trace-bundle --check` to `ci.yml` next to the
   existing codegen check. Clamp the handwritten tile loop while there.
3. Add per-value seed typing to the plan: derive u8, u16, u32 or full width
   per seed word from byte operations, constants, branch guards and value
   flow; emit one schema to both codecs; keep guards per value and the
   full-width variant as the checked fallback for a whole member span. This
   removes the double packing and the span fragmentation together, and it
   is the only lever that makes non-BLAKE3 functions pay.
4. Weight the inventory: fill `real_rows` per member from one merged
   program record, the cached FLT join is enough, and rank circuits by
   seed bytes and retained host arithmetic. Decide coverage from that
   ranking, not from function count.
5. Expand `traceBundle` to the ranked selection, update the registration
   test, compile all selected writers once and run the exact-cell parity
   harness against the bytecode oracle on the real record. Watch nvcc time,
   registers and spills for the wide functions.
6. Grouped spans for multi-member circuits, then the memory and byte-table
   primitives, so a strict mode has no CPU fallback. Only then remove the
   handwritten BLAKE3 provider.

Do not expand coverage under the current runtime codec selection, and do
not treat the one replay pair as a throughput result. Keep the handwritten
provider as the comparison target until step 5 has a like-for-like pair on
more than BLAKE3.
