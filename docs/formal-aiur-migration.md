# Formal Aiur in Ix

The new implementation is imported from `aiur` commit
`7584bf5` on `bench/ixvm-audit`. Its compiler correctness proofs are retained;
the Lean sources are adapted to Ix's Lean/Mathlib 4.34.1 toolchain. In particular,
the Aiur package selects Lean's legacy `do` elaborator to preserve the verified
monadic definitions from 4.29. Proof adaptations do not add axioms or `sorry`.

## Package boundaries

| Component | Lean package/library | Rust crate |
| --- | --- | --- |
| Generic language, compiler, proofs, libraries | `Aiur/` / `Aiur` | `crates/aiur` |
| Stage-one IxVM program and host | `IxVM/` / `IxVM` | `crates/ixvm` |
| Existing language and prover | `LegacyAiur` | `crates/aiur-legacy` |
| Existing IxVM and recursive verifier | `LegacyIxVM`, `LegacyMultiStark` | `crates/ixvm-legacy` |
| Existing generated execution kernels | generator in `LegacyAiur` | `crates/ixvm-legacy-native` (optional) |

The generic Aiur crate does not depend on IxVM, the legacy interpreter, or a
Lean installation. The IxVM crate registers its hint channels and table
accelerators using Aiur's generic APIs. Its Rust binary accepts an exported
execution package. Lean's `IxVM.parse` loads the application and its shared
Goldilocks word/hash library; callers select entrypoints with
`Aiur.Modules.prepare`.

Aiur owns the FFI: `Aiur/c/execution.c` adapts Lean objects to the JSON C ABI
exported by the Rust `aiur` static library. Lake's `aiur/execution_o` and
`aiur/aiur_rs` targets are linked only by executables that use it. The IxVM
export driver builds without Rust and invokes the separate `ixvm` host for
execution with its application hint providers. Pure Lean library/proof builds
do not run Cargo. Cargo builds do not invoke Lake. Serialization remains the
current bridge; this migration does not replace it with a direct object ABI.
The old experimental IxVM
`ffi` replay command is removed: the data-only ABI cannot supply the word
library's closure hints. Generic Aiur FFI execution and tracing remain covered
by their own test executables.

## Build and run

From the repository root:

```sh
lake -d Aiur build
lake -d Aiur test
cargo test --locked -p aiur -p ixvm --features parallel --all-targets

lake -d IxVM build ixvm
lake -d IxVM exe ixvm export /tmp/ixvm-execution.json
cargo run --release --locked -p ixvm -- /tmp/ixvm-execution.json all

lake -d IxVM exe ixvm export-trace /tmp/ixvm-trace.json
cargo run --release --locked -p ixvm --features parallel --example ixvm_bench -- \
  /tmp/ixvm-trace.json IxVM/IxVM/fixtures/nat-add-comm.json witness 1
```

The last command executes bytecode, generates traces, and proves and verifies
the fixed fixture. `stats` exports per-function stage-one widths. These drivers
also work from the root Lake workspace as `lake exe ixvm/ixvm ...`.

## Legacy support and native builds

The production `ix` commands still use the legacy implementation. Sharded
proving, recursive aggregation, GPU execution/proving, and the current claim
envelopes remain available there. The migrated IxVM is the existing experimental
stage-one port, pinned to Ix revision
`91348190f091d53ab0838440eaeaf0cb36f2737f`; it is not a replacement for all current
production entrypoints. `tools/ixvm/adapt.py --check` checks reproducibility of
the source port against that revision, which remains in this repository's Git
history. `tools/ixvm/audit.py --out DIR` inventories its semantic differences;
the audit is not an equivalence proof.

Normal builds use legacy bytecode and leave generated native execution out of
the dependency graph. To select the existing native kernels:

```sh
IX_NATIVE=1 lake build ix
cargo build -p ix-ffi --features legacy-native,parallel
```

The three native kernels share one optional crate. `cargo --workspace` explicitly
includes that crate; ordinary workspace default members exclude it. Legacy
GPU flags (`IX_CUDA`, `IX_CUDA_TRACE_CODEGEN`) are retained independently.
`ix codegen` and `trace-fixtures` still regenerate legacy artifacts at their
new paths.

Future Aiur procedural macros should live in an optional `aiur-macros` crate,
with their IxVM expansion compiled in a separate optional `ixvm-native` crate.
Neither belongs in the ordinary `aiur` or `ixvm` dependency graph. This change
does not implement the future macro backend or create empty placeholder crates.

## Migration validation

Validated on 2026-10-22 with Lean 4.34.1 and Rust 1.98.1:

- All 365 Aiur modules build, including compiler soundness/completeness,
  provenance, optimization, physical deduplication, and word-library proofs.
  The existing theorem statements are retained, with no added axioms or
  `sorry`. The package's default target explicitly includes every submodule.
- The full Aiur regression suite, execution/FFI checks, trace checks, U32 tests,
  and shared-library tests pass. Trace tests include 202 executions under each
  of three compiler configurations and 54 executions over F₂, accepted by
  Lean's `checkMemo`.
- `cargo test -p aiur -p ixvm --all-targets --features parallel` passes all
  82 tests. Workspace Clippy with the new parallel and legacy native features
  passes with warnings denied.
- `Tests.AiurBoundaries` imports both implementations and elaborates both
  surface languages together. Legacy parser categories use a `legacy_aiur_`
  prefix because Lean syntax-category names are global.
- The new IxVM accepts all five validation entrypoints and all 342 fixture
  serialization cases. Corrupted serialization, a wrong address, missing
  advice, and a correctly hashed invalid proof are rejected.
- The fixed `Nat.add_comm` fixture executes, generates a witness, proves, and
  verifies through multi-stark. Its exported package SHA-256 matches the
  recorded pre-migration digest exactly:
  `14cc72161dd26070d290ffd949b10b9225b0792da0a98633827340ca49da1e48`.

| New IxVM fixture result | Value |
| --- | ---: |
| Function queries | 75,988 |
| Fixed-table queries | 140,137 |
| ROM queries | 21,981 |
| Stage-one columns | 18,222 |
| Stage-one cells | 4,082,430 |
| Execution-record fingerprint | 17083028404579245216 |
| Trace fingerprint | 18300081860579238156 |

Both fingerprints match the pre-migration results. These checks concern
migration fidelity; they do not establish equivalence to today's legacy IxVM.

The legacy Rust tests pass (102 tests, 3 ignored), as do six legacy host tests
including the bytecode fallback. The rebuilt legacy Lean execution, cost,
trace-plan, and generated-Rust checks pass. The retained native and bytecode
`Nat.add_comm` runs report matching circuit widths, FFT cost, and cache-hit
counts. Generated execution kernels, Rust trace writers, CUDA units, and
manifests pass their regeneration checks. GPU execution and proving were not
run locally.
