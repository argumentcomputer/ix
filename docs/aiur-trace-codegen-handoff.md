# Aiur trace codegen: handoff

State of the generated GPU trace pipeline on `sb/aiur-trace-sharding-gpu`
(ix `c2c87646`) with multi-stark `sb/trace-sharding-gpu` (`3374357`),
reviewed 2026-09-16. The [implementation plan](aiur-cuda-trace-codegen.md)
holds the design rationale and the step ladder; this document records what
is built, how to drive it, the verified defects, and the recommended order
of the remaining work.

## Summary

The compiler from final Aiur bytecode to seed packers and row writers is
complete for every opcode and control form. Production dispatch covers 42
IxVM functions, 10 multi-stark and 4 ix-aggr: `blake3_compress`, the
circuits whose typed seeds halve their canonical seeds, and the IxVM circuits
with the most measured host witness time on the Init proof. On that proof
generation now saves 6% of wall time and 40% of CPU time against CPU traces
(`bench/aiur-trace-init-2026-09-16`). The generated path reproduced the handwritten BLAKE3
provider's proofs with equal proving time, and once its seed preparation
matched, the handwritten provider was removed: `AIUR_GPU_TRACE` now selects
`cpu` or `generated` only, and the bare `cuda` feature builds no aiur kernels.

State on 2026-09-17, end of day. The uploader pipelines seed copies and
blanks tiles with one memset (item 7 below). Mathlib was measured on one
GPU over 15-minute windows on the 78-shard partition of the four-GPU
bench (`bench/aiur-trace-mathlib-2026-09-17`): on the same 11 claims
generation saves 39 s of stage-one commitment and 118 s of host witness
but adds 36 s of lookup construction, because the generated commit path
keeps no copy of a trace and the lookup kernel regenerates its tiles.
That regression, and the unprofiled 139 s of seed packing, are the next
trace-generation targets (item 8). The span summarizer `spans.py` had
undercounted short spans across ID reuse; every archived summary was
recomputed. The multi-stark admission fix (defect 1) is commit `d557aa7` on
`sb/trace-sharding-gpu`, pushed and pinned by ix, so the `--config`
patch below is only needed for the next multi-stark change. `--exec-jobs 3` is the executor count to prove with; on Init it
closed the one executor-caused gap (438 to 425 s), the rest of the idle
GPU is the four-shard graph.

Nothing in the branch yet establishes that generation pays for any other
function. The static inventory says most functions ship a canonical seed
nearly as wide as their row and retain most of their arithmetic on the host.
The typed seed schema that addresses the first half of that is now in
place (see below); what remains before wider coverage is weighting the
inventory with real row counts and ranking circuits by it.

## Where things live

| Stage | Location |
| --- | --- |
| Trace plan: value ids, column spans, external reads, dependency sets | `Ix/Aiur/Stages/TracePlan.lean` |
| Static inventory as JSON (`ix codegen --trace-report`) | `Ix/Aiur/Stages/TraceReport.lean` |
| Seed bounds analysis and typed schema (`resolveSchemas`) | `Ix/Aiur/Stages/TracePlan.lean` |
| Rust emitter: `pack`, `pack_typed`, `pack_checked`, `write` and `SCHEMA_n` per function | `Ix/Aiur/Stages/TraceCodegen.lean` |
| CUDA emitter and Rust registry | `Ix/Aiur/Stages/TraceCuda.lean` |
| Library fingerprint (Lean side) | `Ix/Aiur/Stages/TraceContract.lean` |
| Bundle selection and CLI flags | `Ix/Cli/CodegenCmd.lean` (`traceBundle`) |
| Runtime: seed context, bound writers, structural bind | `crates/aiur/src/trace_codegen.rs` |
| Library fingerprint (Rust side), grouping validation | `crates/aiur/src/trace_codegen/contract.rs` |
| Seed spans, device dispatch, CPU mirror; memory-table generator (`prepare_memory`) | `crates/aiur/src/trace_codegen/cuda.rs` |
| Registry of the three programs, registration | `crates/aiur/src/trace_codegen/programs/mod.rs` |
| Generated Rust (checked in) | `crates/aiur/src/trace_codegen/programs/{ixvm,multi_stark,ix_aggr}{,_cuda}.rs` |
| Generated CUDA (checked in) and digest manifest | `crates/aiur/cuda/generated/production/` |
| Shared uploader, pinned staging, memory-table kernel | `crates/aiur/cuda/trace_runtime.{cu,cuh}` |
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
run, `[multiplicity, inputs, resolved external reads]`, in the function's
typed schema or, after a guard failure, full width. The shard witness
carries `TraceSource::Generated` and a shape-only lookup witness. multi-stark
allocates the device tile and calls back `write_device_rows`; the uploader
leases a pinned slot, blanks the tile with one memset, copies the span
through the slot's ring of eight 2 MiB chunk buffers, each guarded by the
event of its last transfer so host copies overlap the DMA, launches one
thread per real row, and synchronizes. Kernels write only the columns a
row sets. The lookup-graph kernel regenerates row tiles with a one-row
halo through the same callback, so raw traces are released after commitment.

## Typed seed schema

Every function plan carries a `SeedSchema`: one width per seed word, `u8`,
`u16`, `u32` or full, with byte offsets and a stride. The compiler derives
it from exclusive value bounds and both emitters read the same schema, so
the Rust packer, the CPU mirror and the CUDA kernel agree by construction
and the bind step checks the emitted offsets against the widths.

- **Bounds.** A word narrows when any use in the function constrains it:
  operands of byte-table operations and `u32_to_field`, operands of
  `u32_less_than`, both sides of an `assert_eq`, the discriminant of a match
  with no fallback (bounded by its largest case), arguments passed to
  constrained callees whose inputs are narrow, values yielded into a
  continuation whose merge is narrow, and pointer positions (`load` pointer,
  I/O index and length). Producers carry bounds forward: constants, byte
  results, bits, `add`/`mul` of bounded values, call results from callee
  outputs, `load` results from their table's bounds, and store pointers,
  I/O info and BigUint hint pointers as u32.
- **Library fixpoints.** Callee output bounds and per-memory-width bounds
  (the join of every store site's operands, slot by slot) are one least
  fixpoint, iterated upward from bytes, so a recursive stage machine like
  BLAKE3 whose returns are its own call results narrows instead of staying
  wide, and a table only ever stored with bytes loads bytes. A table with no
  store site stays unknown. Input bounds then iterate downward from unknown.
  Both run over width classes, so they terminate; a phase that does not
  settle falls back to unknown.
- **Speculation is guarded.** The union over paths is deliberate: a value
  used as a byte on one arm has a byte type in the source language on every
  arm, and pointers are a record base plus a table index, so 32 bits hold
  them. Each narrowed word is still checked as it is packed. A row that does
  not fit widens the member span so far to full width by re-encoding the
  typed bytes (no second packing pass) and the rest of that member run stays
  full width. So spans never mix encodings and never fragment per row.
- **Layout.** Wider words first, in index order within a width, padded to
  eight bytes, so every word is naturally aligned and the multiplicity is
  always a full word at offset zero. Unused branch-shared slots pack as one
  zero byte. An all-full schema is byte-identical to the canonical encoding
  and is dispatched as such.
- **Performance shape.** Inputs are packed by the runtime in one loop per
  run of same-width consecutive inputs, which vectorizes; the generated
  `pack_typed` stores read results with literal offsets. Emitting one store
  per input into the generated code, or dispatching on the width per word,
  was two to three times slower than the handwritten packer.
- **Contract.** The seed wire format is `seed-v2/writer-v2` in the library
  fingerprint and manifest ABI 2, so stale artifacts fail to bind rather
  than mis-decode. For production BLAKE3 the schema is the handwritten
  176-byte layout: multiplicity, the stage as a full word, then 160 bytes.

## Controls

| Control | Effect |
| --- | --- |
| `IX_CUDA_TRACE_CODEGEN=1` (Lake) or `--features cuda-trace-codegen` (Cargo) | Compiles the runtime and the generated units; implies `cuda` |
| `AIUR_GPU_TRACE=cpu\|generated` | Provider; `generated` is the compiled one, `cpu` the reference builder |
| `AIUR_TRACE_ONLY_LOOKUPS=1` | Required by both GPU providers |
| `MULTI_STARK_CUDA_ARCHS=120` | nvcc architecture; `-gencode=arch=compute_120,code=sm_120` |
| `MULTI_STARK_CUDA_TRACE_FORCE_SPILL=1` | Validation only: spill every LDE, exercise generated recovery tiles |
| `MULTI_STARK_CUDA_LOOKUP_TRACE_TILE_ROWS=3` | Validation only: tiny regeneration tiles |
| `MULTI_STARK_CUDA_MIN_FREE_BYTES=<bytes>` | Device headroom kept by spilling; default is a quarter of the card |
| `MULTI_STARK_CUDA_MEMORY_LOG=1` | Logs stage-1 placement and, per lookup job, `graph=` path, budget and free bytes to stderr |
| `AIUR_TEST_GPU_DEVICES=0,1,2,3` | Devices for the concurrent fixture |
| `AIUR_GPU_SEED_CACHE_BYTES=<bytes>` | Most seed bytes kept resident per device for round-two sources, default 16 GiB; the backend releases caches before it spills any LDE, and after each LDE's lookup job |
| `AIUR_GPU_TRACE_MEMORY=1` | With `generated`: build memory-table rows on the device too; off by default because it moved no fewer bytes and cost 5 s on Init |
| `AIUR_PROFILE=<new .jsonl>` | Timestamped span events; `aiur/cpu_circuit` (circuit, kind, rows) and `aiur/codegen_seeds` give per-circuit witness time |
| `AIUR_METRICS=<new .jsonl>` | Lightweight per-piece summaries; [collection commands and field definitions](aiur-lightweight-metrics.md) |

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

## Running on the GPU host

The bench hosts run NixOS with the image's CUDA toolkit at
`/usr/local/cuda-13.3` and a CUDA 13.2 driver. Three things trip a fresh
agent before any test runs.

**The Bash sandbox hides the GPU.** `/dev/nvidia*` is not visible inside
Claude Code's sandbox, so `nvidia-smi` reports that it cannot talk to the
driver even though the kernel modules are loaded. Builds work inside the
sandbox (nvcc needs no device); anything that opens the device must run
with the sandbox disabled.

**Nix-built binaries do not find the host's driver or `libstdc++`.** A
binary linked by the Nix Rust toolchain runs on Nix glibc, whose loader
never searches `/usr/lib/x86_64-linux-gnu`. The statically linked CUDA
runtime then fails to `dlopen` `libcuda.so.1` and reports the misleading
"CUDA driver version is insufficient for CUDA runtime version" (error 35).
The `libstdc++` that nvcc's host objects need is missing for the same
reason. Supply both, and nothing else, so libc is not mixed:

```sh
# libstdc++ from the gcc that built the binary; a newer gcc's lib pulls a
# newer glibc and fails with GLIBC_ABI_DT_X86_64_PLT.
export LD_LIBRARY_PATH="$(dirname "$(gcc -print-file-name=libstdc++.so.6)"):$LD_LIBRARY_PATH"
# Only the driver library, exactly as the flake's `cuda` shell hook does.
export LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libcuda.so.1
```

Binaries built with the image's own GCC against the host glibc, as the
earlier benches were, need neither export. The flake's `cuda` dev shell
pins a Nix-built CUDA 13.2 toolkit that is not in the store on these hosts;
entering it downloads the unfree toolkit, so the earlier benches did not
use it.

**Testing a multi-stark change from ix.** Point Cargo at the local checkout
with a config file outside both repos, and restore `Cargo.lock` afterwards:

```sh
cat > "$TMPDIR/trace-backend.toml" <<'EOF'
[patch."https://github.com/argumentcomputer/multi-stark.git"]
multi-stark = { path = "/home/sam/repos/multi-stark" }
EOF
NVCC=/usr/local/cuda-13.3/bin/nvcc MULTI_STARK_CUDA_ARCHS=120 \
  cargo --config "$TMPDIR/trace-backend.toml" test -p aiur --lib --release \
  --features cuda-trace-codegen --no-run
git checkout -- Cargo.lock   # after the run
```

The forced-spill proof, at a reserve chosen against `nvidia-smi`'s free
memory (on a 96 GiB card 100 GB passes and 101.5 GB fails in stage-1
admission before any lookup runs):

```sh
taskset -c 0-7 env RAYON_NUM_THREADS=8 OMP_NUM_THREADS=8 \
  AIUR_GPU_TRACE=cpu AIUR_TRACE_ONLY_LOOKUPS=1 \
  MULTI_STARK_CUDA_TRACE_FORCE_SPILL=1 MULTI_STARK_CUDA_LOOKUP_TRACE_TILE_ROWS=3 \
  MULTI_STARK_CUDA_MIN_FREE_BYTES=100000000000 MULTI_STARK_CUDA_MEMORY_LOG=1 \
  "$test_binary" regenerated_batch_matches_cpu --test-threads=1 --nocapture
```

The `shard 0 did not reproduce its round-one header` panic in that output
is the test's deliberate corruption check, not a failure. With the memory
log on, every `lookup job` line should read `graph=true` under forced
spill; `graph=false` on a spilled, regenerable LDE is the admission defect
described below.

**Mathlib on one GPU.** The oleans are not built on these boxes and the
sandbox blocks `~/.cache/mathlib`, so fetch the cache into a writable
directory, compile with `--no-build`, and cut the calibrated 78 shards
explicitly; the seed gives 100 to 115 here and must not be used for
comparisons (see the bench README for the derivation of 78):

```sh
cd Benchmarks/Compile && MATHLIB_CACHE_DIR=$scratch/mathlib-cache lake exe cache get && cd -
ix compile --no-build Benchmarks/Compile/CompileMathlib.lean --out mathlib.ixe   # 70 s, 20 GiB
ix shard mathlib.ixe --shards 78 --out mathlib-78.ixes                            # 54 s
# sha256: mathlib.ixe d84ece55…, mathlib-78.ixes 29108219… (the four-GPU run's inputs)
AIUR_GPU_TRACE=generated AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24 \
  AIUR_TRACE_SHARD_MAX_CELLS=1500000000 AIUR_PROFILE=spans.jsonl \
  timeout --signal=TERM 900 ix prove --ixe mathlib.ixe --ixes mathlib-78.ixes \
  --trace-shards --lanes 1 --exec-jobs 3 --max-ram 230 --no-index
```

A full one-GPU proof is on the order of three hours per mode; a 15-minute
window proves 11 claims and 6 joins, and `bench/aiur-trace-mathlib-2026-09-17/matched.py`
compares the same units phase by phase from the lanes log and the spans.
Stop a run with `timeout` rather than by hand so GNU time's summary
survives. `bench/aiur-trace-init-2026-09-16/spans.py` is the span
summarizer; use the current version, the earlier one lost intervals
across span-ID reuse.

## Evidence

| Check | Result |
| --- | --- |
| Planner fixtures, including thirteen schema tests | 48 pass |
| CPU suite of `aiur`, including the typed guard fallback | 86 pass |
| GPU suite of `aiur` on one device, including forced spill, span widening, memory tables and multi-device commits | 97 pass |
| Generated BLAKE3 timing, 65,536 rows: upload typed vs canonical, typed in one production span, preparation vs host rows | 2.29 vs 8.59 ms, 1.80 ms, 2.16 vs 110 ms |
| Init proof, 4 claims, one GPU, CPU traces vs BLAKE3-only vs weighted coverage vs pipelined upload (`bench/aiur-trace-init-2026-09-16`) | 472 vs 452 vs 442 vs 441 s end to end, same root; CPU time 3537 vs 2983 vs 2106 vs 2094 s; device callbacks 29.9 vs 27.4 s union; lookup construction 38 s with CPU traces, 54 s generated |
| Mathlib, 78 shards, one GPU, 15-minute windows, CPU vs generated traces (`bench/aiur-trace-mathlib-2026-09-17`) | Same 11 claims: proof −13.8 s, stage-one commit −39.4 s, lookup construction +35.8 s, host witness −118 s, seed packing 139 s, device callbacks 74 s; claim proof 54.7 vs 53.4 s mean, join 31.3 vs 28.5 s; no fallbacks |
| Two-round generated BLAKE3 proof, normal and forced spill at 100 GB reserve | Same bytes as CPU traces; altered regeneration rejected |
| Init, generated traces, device-resident seeds off vs on (`bench/aiur-seed-cache-2026-09-17`) | Lookup construction 53.7 to 48.6 s, its callbacks 11.3 to 6.3 s, proving union 256.5 to 250.6 s, end to end 433 to 431 s, same root |
| BLAKE3 gate, 65,536 rows, preparation handwritten vs generated, before removal | 7.84 vs 7.64 ms and 7.45 vs 7.80 ms |
| BLAKE3 gate, synchronous upload handwritten vs generated, before removal | 2.30 vs 2.28 ms |
| Paired FLT join replay, one pair, before the typed schema | Same proof and six-piece plan |
| Proving time, handwritten vs generated, before the typed schema | 23.49 s vs 23.55 s |
| Seed preparation, handwritten vs generated, before the typed schema | 2.33 s vs 2.78 s |

One pair supports "comparable", not a speedup. The replay predates the typed
schema, which replaced the generic byte packer with per-run loops; the
microbenchmark is now at parity, and the replay should be repeated.

## Coverage

`traceBundle` selects `blake3_compress`, every circuit whose members'
typed seeds sum to at most half their canonical seeds
(`ProgramPlan.compactCircuitFunctions`), and the `weightedCircuits` list in
`Ix/Cli/CodegenCmd.lean`: the IxVM circuits with the most host witness time
in the Init proof (`bench/aiur-trace-init-2026-09-16`), named by function so
any alias resolves and the whole circuit is taken. Memory tables can
be generated by one hand-written kernel for every width (`prepare_memory`,
`aiur_trace_memory`, opt-in through `AIUR_GPU_TRACE_MEMORY=1`): seeds are
`[multiplicity, pointer, values]` copied out of the record, rows are
`[multiplicity, 1, pointer, values]`, and every table row is real, as the
CPU builder emits them. Measured on Init it is a small loss, since the seed
is the row less one column, so it is off by default. Byte tables take the
CPU path. The registration test checks that the
covered circuits are exactly the selected functions and drives the BLAKE3
member with fixture rows; the other selected writers are exercised only by
the end-to-end proof comparison against CPU traces, which requires identical
proof bytes, so a unit-level oracle for them is still an open item.

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
typed schema narrows words from an actual bounds analysis; the
[schema inventory](../bench/aiur-trace-schema-2026-09-16/README.md) measures
it statically: typed seeds are 0.70 to 0.76 of canonical summed over each
library and 0.55 to 0.58 of the main row, 59% of IxVM seed words are still
full width because they hold addresses, hashes and field values, and only
BLAKE3 and the klimbs family compress more than 2x. The report carries
`typed_seed_bytes` and `typed_seed_word_bits` per function. Row weights are
still `null`; the inventory cannot yet say which circuits carry the bytes.

## Verified defects and hazards

Ranked. File references are to this branch pair.

1. **Lookup admission budgets the wrong kernel after a spill.** multi-stark
   `src/types.rs:970` decides `graph_path` from LDE residency and sizes the
   admission budget accordingly, while `src/cuda/mmcs.rs:183`
   (`resident_with_trace`) also accepts generator-backed and retained-trace
   LDEs, so the graph kernel with regeneration tiles runs under the direct
   path's budget once an LDE has spilled. Correctness holds and the forced
   spill test passes, but behavior near the device limit is unverified in
   either direction. Under forced spill the memory log showed `graph=false`
   for half the jobs while the graph kernel ran, under-budgeting one job by
   about seven times and over-budgeting another. Fixed on the multi-stark
   branch by `CudaMmcsData::has_resident_with_trace`, a side-effect-free
   twin of `resident_with_trace` that admission, the job sort and the spill
   fallback all use, with the chosen path passed into evaluation instead of
   re-derived; the forced-spill proof and all multi-stark tests pass with it
   at 100 GB reserve on a 96 GiB card. Lands in ix with the next pin bump.
   Original fix note: make the admission predicate match
   `resident_with_trace`.
2. **Per-row codec selection fragments spans and packs twice.** Fixed by
   the typed seed schema (see above). The old code ran the u8 packer per
   row and, on a guard failure, the full-width packer again; each encoding
   change closed the span and cost one upload, launch and synchronize, so
   rows alternating between fitting and not fitting a byte produced
   one-row spans. Now a member run is one span that at most widens once,
   and the widening re-encodes typed bytes instead of repacking.
   `wide_rows_widen_the_member_span_once` covers the alternating case.
3. **The trace-bundle freshness check is not in CI.**
   `ix codegen --trace-bundle --check` compares Rust writers, registries,
   CUDA sources and the manifest against Lean output, but
   `.github/workflows/ci.yml:40` runs only the ordinary `codegen --check`.
   A stale Rust module is caught only at registration.
4. **Handwritten BLAKE3 tile cap.** Gone with the handwritten provider:
   `gpu_trace/mod.rs` now only selects between the CPU builder and the
   generated provider, and `blake3_trace.cu`, `blake3_body.rs` and its
   exporter are deleted. The generated path clamps to the tile.
5. **Preparation failures abort the process.** Fixed: a preparation error
   now logs a warning with the circuit and row count and returns the
   circuit to the CPU builder, which is the reference. The CPU mirror in
   `cuda.rs` still uses `expect` on decoded seeds, which only fires on bytes
   the packer itself validated. A strict mode that refuses the fallback
   remains to be defined with the primitives.
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
   `MULTI_STARK_CUDA_MIN_FREE_BYTES`. Done: multi-stark `d557aa7` (see
   defect 1), pinned by ix.
2. Add `lake exe ix codegen --trace-bundle --check` to `ci.yml` next to the
   existing codegen check. Clamp the handwritten tile loop while there.
   Done: the CI step exists; the tile loop went with the provider.
3. Add per-value seed typing to the plan: derive u8, u16, u32 or full width
   per seed word from byte operations, constants, branch guards and value
   flow; emit one schema to both codecs; keep guards per value and the
   full-width variant as the checked fallback for a whole member span. This
   removes the double packing and the span fragmentation together, and it
   is the only lever that makes non-BLAKE3 functions pay. Done: see the
   typed seed schema section; the BLAKE3 gate passes at 0.97 to 1.05 of the
   handwritten preparation time. Not yet redone: the paired FLT replay.
4. Weight the inventory: fill `real_rows` per member from one merged
   program record, the cached FLT join is enough, and rank circuits by
   seed bytes and retained host arithmetic. Decide coverage from that
   ranking, not from function count. Done against the Init proof instead of
   FLT: `bench/aiur-trace-init-2026-09-16/weights.py` ranks IxVM circuits by
   measured host witness time from `aiur/cpu_circuit` spans, and the top of
   that ranking is the `weightedCircuits` selection. The static half is in
   the [schema inventory](../bench/aiur-trace-schema-2026-09-16/README.md).
   Static compression alone picked circuits with few rows and moved wall
   time by nothing; redo the weighting on the FLT record when it is at hand.
5. Expand `traceBundle` to the ranked selection, update the registration
   test, compile all selected writers once and run the exact-cell parity
   harness against the bytecode oracle on the real record. Watch nvcc time,
   registers and spills for the wide functions.
6. Grouped spans for multi-member circuits, then the memory and byte-table
   primitives, so a strict mode has no CPU fallback. Memory tables are done
   and measured: they generate correctly but a memory seed is the row less
   one column, so device generation moved no fewer bytes and cost 5 s on
   Init; it ships opt-in. Byte tables are 256 and 65,536 fixed rows and do
   not need it. A strict mode therefore has to accept memory tables on the
   device at a small cost, or the CPU fallback stays. The handwritten BLAKE3
   provider was removed ahead of this once the generated one matched it on
   proof bytes and preparation time; the comparison target is now
   `AIUR_GPU_TRACE=cpu`, and the opt-in `blake3_generated_timing` test
   records upload and preparation against materializing the same rows on
   the host.
7. Upload pipelining is done: the uploader blanks the tile with one memset
   and streams the span through a ring of pinned chunks with transfer
   events, and kernels no longer zero their rows (Init callbacks 29.9 to
   27.4 s union, tile 2.31 to 1.80 ms). On the BLAKE3 tile the copy is no
   longer the span's cost; the kernel is. Next on the device side: the
   generated kernels' register pressure and row-major stores (see the
   kernel plan). Whether packing straight into pinned memory pays for the
   other writers is not established: the callback spans include
   allocation, the blank, DMA, kernels and the stream wait, and one tile's
   copy fraction does not transfer to every circuit.
8. Measured on Mathlib (`bench/aiur-trace-mathlib-2026-09-17`), same 11
   claims: generation saves 39 s of stage-one commitment and 118 s of host
   witness but adds 36 s of lookup construction and spends 139 s packing
   seeds and 74 s in device callbacks, for a net 14 s (2%) on 600 s of
   claim proofs and 21 s (13%) on 161 s of join proofs. In order:
   (a) lookup regeneration: the generated commit path releases the raw
   device trace and keeps no host copy, so the lookup kernel regenerates
   every tile through the callbacks (Init shows the same, 38 s to 54 s);
   measure bounded retention of expensive raw traces and caching of the
   compact device seeds against the extra live device memory, preserving
   admission and eviction. Built: a round-two source uploads its seeds
   once, at its first commit tile, into one device allocation; the lookup
   tiles run from it with no host copy, no staging and no seed allocation;
   multi-stark frees it after the LDE's lookup job, before any LDE spill
   or eviction, and under `AIUR_GPU_SEED_CACHE_BYTES`. Round one keeps
   nothing. The paired Init and Mathlib measurements are still to run. (b) Split the seed-packing span into query
   filtering, packing, allocation, concatenation and scheduling waits
   before choosing between direct writes into the final buffers, wider
   parallelism and a device-side gather from record tables; the last
   needs the callee and store relationships that `SeedContext` resolves by
   hash lookup to be represented on the device, a larger project the
   upstream audits support only as selective expansion. (c) In multi-stark,
   NTT is about 49% of kernel time on the current claim profile and BLAKE3
   hashing 20%; the fused LDE work in the kernel plan is the largest
   evidenced kernel target, and short-row BLAKE3 dispatch already exists.

Do not treat the one replay pair as a throughput result; the next paired
replay is generated against CPU traces with the typed schema.
