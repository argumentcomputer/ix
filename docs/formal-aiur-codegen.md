# Formal Aiur programs: code generation

Code generators consume a checked program, not a storage format:

```text
checked bytecode ──────→ native generator ─→ Rust source ─→ build
checked trace plans ───→ CUDA generator ───→ CUDA source ─→ build
        │
        └─────────────→ artifact cache (.lake/aiur, Ixon packages)
```

- **Native codegen** (`aiur-codegen`) emits Rust executors from checked
  bytecode and its normalized execution plan only.
- **CUDA codegen** (`aiur-tracegen`) emits trace writers from population
  plans and placement only.
- **The artifact cache** stores the certified compiler's output as Ixon
  packages (`Aiur.Artifact`, `aiur::artifact`) so commands avoid
  recompiling. The generation step loads the programs from it through
  `aiur::artifact::Package::load`; the generators themselves take the
  checked program.

## Code generation

Code generation runs inside `lake build ix`, before Cargo, and writes into
the build directory, never the source tree. Nothing generated is committed.

```text
lake build ix
  ix_rs                Rust archive without generated code
  formal-codegen       Lean executable: the certified compiler, linking ix_rs
  formal_generated     formal-codegen .lake/build/formal-generated [--cuda]
    1. each program from the artifact cache; misses compile concurrently
    2. native/{ixvm,verifier,aggregation}.rs        (aiur-codegen)
    3. CUDA builds only: cuda/{ixvm,verifier,aggregation}/  (aiur-tracegen)
  ix_rs_net            Cargo compiles the generated files into ix
```

`formal-codegen` (`FormalCodegen.lean`) selects each program as any command
does (`FormalAiur.targetPaths`): the `IX_*_ARTIFACT` variables name trusted
packages, and otherwise the package comes from `.lake/aiur` or is compiled
in process on a miss (see [direct FFI](formal-aiur-direct-ffi.md)). It loads
each package into a registry and asks the prover for its generated sources
(`FormalProver.Program.codegen`, `ix_prover::codegen`).

### Native executors

The Rust emitter is the ordinary library `aiur-codegen`. Its input is a checked
program (bytecode and the native execution plan), and its output is Rust
source text. `crates/formal-generated` compiles the generated files with
plain `include!`, so Cargo tracks them as ordinary sources. Cargo never
invokes Lake and never reads a compiled package.

The emitter's own test (`crates/aiur-codegen-tests`) generates the executors
of fixture programs from its build script and checks them against the
interpreter, including the call heights of programs with depth circuits.
`ixvm-native` and `stark-verifier-native` compare the linked executors
with the interpreter on real invocations.

Generated executors record call heights, which depth circuits read, in the
runtime (`aiur::native`), so generated code does not depend on the trace
and a program with depth circuits runs on its linked executor like any
other (`Executor::select`).

### CUDA trace writers

`aiur-tracegen` is a library over population plans and placement. In a
CUDA build it emits one unit per supported circuit and a Rust binding
(`bundle.rs`) per program; per-circuit units let nvcc compile and cache
them in parallel. A program's trace with depth circuits needs a program
that records call heights to be described, which the loaded program does.

CUDA output is gated by the same selection that enables the `cuda` Cargo
feature (`cudaEnabled` in `lakefile.lean`: `IX_CUDA`, or
`IX_FORMAL_COMPILED_TRACE=1`, which implies it).

- A CPU build runs only the native emitter: no tracegen work, and any CUDA
  output from an earlier CUDA build is removed.
- The selection is part of the generation step's trace, so switching CUDA
  on regenerates with the CUDA sources, and the build never compiles stale
  CUDA output.
- The writers are compiled and linked with `IX_FORMAL_COMPILED_TRACE=1`
  and selected at run time with `AIUR_GPU_TRACE=compiled`; only IxVM's
  bundle is registered.

### When generation runs

`formal_generated` reruns when `formal-codegen` itself (and with it the
compiler and programs it links, the emitters or their Lean callers) or the
CUDA selection changed. It rewrites only files whose contents changed, so
Cargo recompiles only executors that actually changed. A native executor's
file records only its fingerprint, so a change that leaves the bytecode and
the execution plan alone, such as regrouping circuits, leaves it
byte-identical. The CUDA files depend on the grouping and also record the
digest of the package they were generated from.

The first build in a checkout, and the first after a program or compiler
change, pays the certified compile (several minutes, the three programs
compiled concurrently). Later builds load the packages from the cache.

`ix codegen --out DIR [--cuda]` writes the same sources to a chosen
directory for inspection, and `ix prepare` fills the cache ahead of time.

### Fingerprints

Each generated unit carries the fingerprint of exactly what it depends on:

| Generated code | Fingerprint inputs |
|---|---|
| Native executor | bytecode and the native execution plan (`native_fingerprint`, scheme 2) |
| CUDA trace writer | population plans and placement (the population description fingerprint, scheme 2) |

At runtime `ix` recomputes these from the loaded program and compares. A
mismatch falls back to the interpreter, or is rejected under
`IX_FORMAL_NATIVE=1` (`FormalAiur.checkExecutor`). Since every build
generates the executors for the current programs, a mismatch means `ix` is
older than the programs it runs, for example after an explicit
`--aiur-artifact`, and the message says to rebuild with `lake build ix`.

- A grouping-only change leaves CPU executors valid.
- Changing how the artifact file pools rows or polynomial nodes invalidates
  nothing: the native fingerprint hashes the bytecode with table rows inline
  (`aiur::artifact::program_bytes`), and the population fingerprint hashes
  polynomials as trees.

## Packaging

- **Nix.** The Crane-built archives have no generated code; the flake sets
  `nativeExecutors` to false, so the packaged `ix` runs every job on the
  interpreter, with identical results.
- **Rust-only builds.** `cargo build` of the workspace builds
  `formal-generated` empty; only `lake build ix` enables its `executors`
  feature, which needs the generated directory.
