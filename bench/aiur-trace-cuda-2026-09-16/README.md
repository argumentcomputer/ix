# Generated CUDA trace writers: first performance gate

The trace plan now emits CUDA C++, Rust seed packers (including direct packed
bytes), scalar oracle writers and a registry for the same function library.
BLAKE3 and the merged `u64_mul` execute through generated kernels; there is
no function-name specialization in the emitter. Production prover dispatch
still uses the existing provider.

All builds and tests used affinity to CPUs 0–7, Cargo/Rayon limits of eight,
and separate worktrees. The original ix and multi-stark checkouts remained clean.
[Metadata and source hashes](metadata.json) identify both worktrees, tools
and the frozen benchmark binary. The backend change is also preserved as
[a patch](multi-stark.patch) against ix's pinned multi-stark revision.

## Results

**Step 2's microbenchmark gate passes.** One 65,536-row tile, all eight
BLAKE3 stages, 176-byte seeds, same GPU and output allocation. Medians of
nine alternating samples from the final frozen binary:

| Timed work | Handwritten | Generated | Change |
| --- | ---: | ---: | ---: |
| Host preparation | 8.367 ms | 8.496 ms | 1.5% slower |
| Synchronous seed upload + generation | 2.392 ms | 2.265 ms | 5.3% faster |

Both are within the allowed 5% regression. GPU timing includes staging,
allocation/free, synchronization and error reporting, and excludes downloading
the matrix. Preparation includes allocating and dropping the owned source;
registration is outside the timer for both variants. Rows are synthetic
unique byte inputs with full-width multiplicities; this measures the packing
and callback costs, not execution or complete proof speed. CPU timing varied
between captures while the unrelated host build was active. No end-to-end
speedup or utilization gain is inferred.

The initial generic codec made preparation 3.59 times slower. Emitting the
byte payload directly, with a guard and canonical fallback, removed that
cost. The emitter uses the same rule for every function. Logs preserve the
[initial result](performance-initial.log), [packed result](performance-packed.log)
and [final frozen comparison](performance-final.log).

Correctness checks:

- **24 GPU tests passed**, covering all operation/control fixtures, the actual
  compiler's BLAKE3 and `u64_mul`, canonical field words, full-width fallback,
  negative multiplicities, zero inverses, branch-dependent columns and
  immutable external reads. [GPU log](gpu-tests.log).
- Grouped members, 65,537-row tiles, padding and wraparound halos agree with
  the scalar oracle. Eight concurrent upload threads passed across all four
  GPUs. Repeated device errors release their staging leases; alternating
  codecs do not retain unused whole-tile reservations.
- A two-shard, two-round generated BLAKE3 proof verifies and equals the CPU
  trace proof byte for byte. Generated sources are released at the barrier;
  altered regenerated cells are rejected. The panic printed in the log is
  this expected corruption check. [Proof log](proof-regeneration.log).
- **18 CPU tests and 35 planner fixtures passed** without CUDA. Lean and Rust
  agree on the canonical library fingerprint. Changed callees, branch order,
  seed widths and invalid groups are rejected; valid regrouping is accepted.
  [CPU log](cpu-tests.log), [planner log](planner-tests.log).
- Generated fixtures reproduce exactly, and all three existing Rust execution
  modules still reproduce byte for byte. [Fixture check](generated-check.log),
  [execution check](execution-check.log).

## Build and resource observations

`ix codegen --trace-cuda --target ixvm --trace-functions 33,127` emits the
production BLAKE3 and `u64_mul` writers. Both compiled to native `sm_120`
cubins in a separate unit. Its [nvcc report](ixvm-cuda-resources.log) records:

| Writer | Registers/thread | Spill stores / loads |
| --- | ---: | ---: |
| BLAKE3, packed | 178 | 0 / 0 bytes |
| BLAKE3, canonical words | 254 | 176 / 208 bytes |
| `u64_mul`, packed | 48 | 0 / 0 bytes |
| `u64_mul`, canonical words | 62 | 0 / 0 bytes |

Packed BLAKE3 meets the timing gate despite higher register use than the
handwritten kernel. The wide variant's spills remain relevant to later
coverage decisions; these results do not establish performance for all
IxVM functions. The final focused release test build took 12.0 seconds with
cached dependencies, not a cold whole-project build.

The opt-in `cuda-trace-codegen` feature builds only the small checked-in
fixture manifest. Its registry rejects missing writers explicitly. Source
digests are checked before nvcc; objects are cached by source, shared headers,
nvcc version, architecture and flags. There is one shared uploader with four
portable pinned slots of 16 MiB, independent of the number of emitted units.
The handwritten provider retains its separate staging pool during comparison.

The versioned fingerprint binds function order, flags, layouts, operations,
constants, ordered branches, call targets and memory widths. Legal circuit
grouping is validated separately. Both full-width and packed seeds preserve
canonical cells; multiplicity always remains eight bytes. Sources own their
seeds, and regeneration borrows the finalized record until packing completes.

## Reproduction

The experimental feature needs the paired backend header/metadata change.
Apply `multi-stark.patch` in a separate checkout of
`9ba93c0b448c77b99eafe867c3078a83ee0eef2f`, then point a temporary Cargo config
at that checkout:

```toml
[patch."https://github.com/argumentcomputer/multi-stark.git"]
multi-stark = { path = "/path/to/multi-stark-worktree" }
```

From the ix worktree, with that config saved as `/tmp/trace-backend.toml`:

```sh
taskset -c 0-7 env CARGO_BUILD_JOBS=8 RAYON_NUM_THREADS=8 \
  NVCC=/usr/local/cuda-13.3/bin/nvcc MULTI_STARK_CUDA_ARCHS=120 \
  CARGO_TARGET_DIR=/tmp/aiur-trace-target \
  cargo --config /tmp/trace-backend.toml test -p aiur --lib \
  --release --features cuda-trace-codegen -j8 --no-run
```

This local patch changes Cargo's backend lockfile source; preserve and
restore the worktree's lockfile after the experiment. No dependency versions
need updating. Run the resulting test binary as follows (use only `0` for a
single-GPU host):

```sh
export RAYON_NUM_THREADS=8 OMP_NUM_THREADS=8
taskset -c 0-7 env AIUR_TEST_GPU_DEVICES=0,1,2,3 "$binary" \
  trace_codegen --test-threads=8
taskset -c 0-7 env AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_GPU_TRACE=cpu "$binary" \
  synthesis::tests::codegen_blake3_regenerated_batch_matches_cpu \
  --exact --test-threads=1
taskset -c 0-7 "$binary" \
  trace_codegen::tests::cuda::blake3_performance_gate \
  --ignored --exact --nocapture --test-threads=1
```

`AIUR_GPU_TRACE=cpu` makes the reference witness use CPU rows; the proof test
explicitly installs the compiled source for its generated comparison.
The fixture generator remains
`bench/aiur-trace-codegen-2026-09-16/Generate.lean`. It now writes the scalar,
packed, CUDA and registry artifacts plus their manifest; `--check` compares
all of them. Running its Lean interpreter requires loading the existing
Blake3 and Blake3Rust native libraries. The private interpreter wrapper and
artifact directory used here are identified in the metadata.

## Remaining rollout

All opcode/control lowering exists, but all 1,220 production CUDA writers
have not been compiled or profiled. Next are production registry/dispatch,
measured function selection and build partitioning, memory/byte-table
primitives, and full strict coverage. Real workload row weights and packing
costs still determine that order. Mixed byte/wide records can produce many
small spans and need a measured batching policy before broad rollout.
The handwritten provider remains the comparison target until those gates
and a representative end-to-end proof comparison pass.
