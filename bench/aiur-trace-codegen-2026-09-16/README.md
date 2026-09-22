# Generated Aiur seeds and scalar traces

This records the earlier scalar-stage checkpoint. CUDA emission, direct
packed preparation and later validation are in the
[CUDA follow-up](../aiur-trace-cuda-2026-09-16/README.md). The source hashes
below identify that earlier checkpoint, not the current generated files.

Implemented and validated in the `aiur-cuda-trace-codegen` worktree, based
on `dcfa650564dc0d3193eda4719503771370eb7957`. Compilation and tests were
restricted to CPUs 0–7 and eight threads, with separate Lean/Cargo artifacts
from the FLT checkout. Source hashes and commands are in
[metadata.json](metadata.json).

## Results

- **16 Rust tests passed.** Generated main-trace cells equal the existing
  Rust trace builder's canonical cells. Fixtures cover all 34 bytecode
  operations, every control form, degree-dependent columns, virtual carries,
  branch sharing, nested yields, early returns, grouped selector offsets,
  store/load pointers with nonzero bases, call outputs, I/O and BigUint hints.
- The current compiler's BLAKE3 body passed for **all eight stages across
  four input states**, with negative and large positive multiplicities.
  Each row has 533 cells; 162 logical seed words pack into **176 bytes** when
  the payload passes the byte guard. The generated scalar writer can run
  after the execution record has been dropped.
- Checked preparation agrees with normal preparation and detects an
  intentionally wrong returned-call alias, identifying its function, query
  and operation. Packing leaves the finalized record unchanged.
- Zero inverses, `p-1`, u32 boundaries, noncanonical seeds, compact-codec
  overflow and padding, missing match arms, inactive queries, altered
  unconstrained callees and reordered match arms have explicit checks.
- **All 1,220 production function writers type-check** in a separate Rust
  consumer of `aiur`. This includes both preparation variants and the scalar
  writer, with the actual production groups.
- All **35 planner fixtures passed** again. All three existing Rust execution
  modules regenerate byte for byte, and the generated Rust fixture is current.

| Program | Constrained functions | Generated Rust bytes | Generation time |
| --- | ---: | ---: | ---: |
| IxVM | 757 | 7,802,757 | 3.94 s |
| MultiStark | 223 | 3,044,037 | 2.61 s |
| Aggregation | 240 | 3,089,689 | 2.48 s |

Generation includes Lean startup and compiling the Aiur source to bytecode.
The three modules together took 42.7 s to type-check with cached Rust
dependencies. These are single observations under competing host load,
not CUDA build timings or proof-performance measurements.

Logs: [Rust tests](rust-tests.log), [planner fixtures](planner-tests.log),
[production type-check](production-typecheck.log),
[execution artifact check](execution-codegen-check.log),
[fixture freshness](fixture-freshness.log).

## Implementation boundary

[`TraceCodegen.lean`](../../Ix/Aiur/Stages/TraceCodegen.lean) consumes the
trace plan and emits three functions per constrained function: normal seed
preparation, preparation with alias checks, and a scalar row writer. Branches
retain fixed seed/column offsets and only execute the reads on their chosen
path. The row writer has no access to the record or I/O.

[`trace_codegen.rs`](../../crates/aiur/src/trace_codegen.rs) supplies read-only
lookups, caller-owned seed/row buffers, canonical word validation, grouped
member placement and the compact codec. Multiplicity always occupies eight
bytes. A non-byte payload selects full-width words; narrowing never truncates
a value. Encoding is explicit metadata, not a tag inferred from byte length.

Binding compares the complete expected bytecode library, layouts and circuit
partition, including unconstrained callees and the order of match cases.
Case order matters because it determines default-arm inverse columns;
ordinary map equality ignores that order. This structural guard precedes
the planned versioned manifest/fingerprint. Generated production modules are
experimental outputs, not registered in the prover.

The existing handwritten GPU provider remains active. No GPU proof or
speedup is claimed here. Remaining work is CUDA emission and arithmetic,
device seed decoding, bounded pinned batch staging, manifest/build/dispatch
integration, grouped ranges and halos, primitive circuits, and the planned
GPU parity and performance gates. Workload row weights and CPU packing costs
also remain unmeasured.

## Reproduction

With the changed Lean modules built in a configured checkout:

```sh
taskset -c 0-7 lake env lean -j8 --run \
  bench/aiur-trace-codegen-2026-09-16/Generate.lean --check

taskset -c 0-7 env CARGO_BUILD_JOBS=8 RAYON_NUM_THREADS=8 \
  cargo test -p aiur --lib trace_codegen --locked -j8 -- --test-threads=8

taskset -c 0-7 lake env lean -j8 --run \
  bench/aiur-trace-plan-2026-09-15/Run.lean --trace-rust --target ixvm \
  > /tmp/ixvm-trace.rs
```

Omit `--check` from `Generate.lean` to regenerate the checked-in test fixture.
Use `multi-stark` or `ix-aggr` for the other production modules. A rebuilt
`ix codegen --trace-rust --target <program>` exposes the same emitter and
writes to stdout without changing the execution artifacts.

The type-check used a temporary crate importing all three modules, with
`aiur` pointing at this worktree and `multi-stark` pinned to
`9ba93c0b448c77b99eafe867c3078a83ee0eef2f`. Its manifest, generated source
hashes, isolated target directory and exact offline command are recorded
in `metadata.json`.
