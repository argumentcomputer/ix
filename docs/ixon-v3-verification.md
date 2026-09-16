# Ixon v3 implementation and verification record

Ixon v3 carries independent usage, ownership, and relative-locality contracts
through the Ix source frontend, Lean and Rust compilers, canonical bytes,
sharing, text syntax, FFI, and decompilation. Scoped shared borrowing uses an
explicit let kind. Native admission checks resources and erased typing before
an annotated production artifact is emitted.

## Implemented boundary

- Definitions, theorems, opaque bodies, and explicitly admitted interfaces are
  supported. Annotated inductive/constructor/recursor generation and nonidentity
  compiler surgery reject before emission.
- Native Resource claims bind the complete constant-set root, object format,
  validator, and canonical profile. The profile commits external assumptions,
  representation rules, primitive pins, and analysis limits.
- IxVM preserves all contract fields and proves its advertised erased-typing
  or structural statement. Resource-proof requests reject explicitly.
- Compilatrix migration remains external. The
  [handoff package](compilatrix-ixon-v3.md) supplies complete accepted and
  rejected environments, a profile, a resource claim, and exact identities.

The [resource-checker specification](resource-checking.md) records the bounded
normalization, higher-order capture, recursion, and projection fragment.

## Executed gates

Commands run from the repository root:

| Gate | Result |
| --- | --- |
| `lake build IxCompileVerify IxTcVerify Ix.Resource.Audit` | Passed; exact trust manifests and local sorry-frontier audits |
| `lake build IxTests ixon-v3-tests ix` | Passed |
| `lake lint -- --wfail` | Passed for every target included by the CI lint driver |
| `lake env .lake/build/bin/IxTests` | Entire primary suite passed, including recursive proof and aggregate consumers |
| `lake env .lake/build/bin/IxTests cli` | Passed, including fresh-process source and imported contracts, anonymous output, and no-artifact rejection |
| `lake env .lake/build/bin/IxTests --ignored validate-aux aux-gen-diff decompile-diff` | Passed production-driver parity and complete decompiler fidelity |
| `lake env .lake/build/bin/IxTests --ignored compile-determinism` | Fixture corpus and Batteries each emitted SHA256-identical files in separate processes |
| `lake env .lake/build/bin/IxTests --ignored ixvm` | Passed all kernel, adversarial, generated-code parity, exact FFT-cost, and shard checks |
| `lake env .lake/build/bin/ixon-v3-tests` | Passed, including bytecode/generated-Rust/source-interpreter claim parity and proof verification |
| `.lake/build/bin/ixon-v3-primitives` followed by `.lake/build/bin/ixon-v3-tests --primitives` | Passed; 3,634 constants and 3,540 addressed interfaces validated |
| `.lake/build/bin/ix codegen --check` | Passed for the regenerated kernel and both recursive consumers |
| `cargo fmt --all -- --check` | Passed |
| `cargo clippy --release --workspace --all-targets --features ix-ffi/parallel,ix-ffi/net,ix-ffi/test-ffi -- -D warnings` | Passed |
| `cargo check --release --workspace --all-targets --features ix-ffi/parallel,ix-ffi/net,ix-ffi/test-ffi` | Passed |
| `cargo test --release --workspace` | 1,563 passed; 14 existing ignored tests |
| `cargo nextest run --release --profile ci --workspace` | 1,563 passed; 14 existing skipped tests |

The dedicated v3 suite reports 1,844 golden-byte/rejection checks, 475 FFI and
sharing checks, 3,639 VM checks, 458 text checks, 131 resource checks, and 18
admission checks, plus addressed validation, compiler transport, decompilation,
claim, catalog, primitive, source, and handoff suites. It includes all 16 binder
contracts and 64 arrow contracts, both let kinds, independent byte/address
fixtures, malformed encodings, every fixture truncation, and trailing bytes.
The VM suite also checks all 11 counted decoding paths with a complete
single-element input and truncated inputs declaring two or `UInt64.max`
elements. These 66 checks run through bytecode and source interpretation.
Malformed cases must reject during decoding, before any reserialization check.

The ordinary production corpus has 6,656 source constants. The serial and
parallel Lean drivers and Rust emit the same 6,940,577-byte environment, with
7,404 named entries and no address, byte, or metadata mismatches. Decompilation
reconstructs all 6,656 source constants with no errors or mismatches. The
low-level diagnostic probes retain their existing mismatch baselines; the
production-driver and fidelity gates require zero mismatches.

## Formal trust frontier

The compiler manifest audits 143 roots. The typechecker manifests audit 2,034
completed roots, one conditional root, and seven statement roots. Their
existing transitive assumptions remain explicit in the manifests. Both local
sorry-frontier checks pass.

The new resource audit covers 15 roots connected to executable quantitative,
scope, ownership, loan-ending, and join checks. Contract-code inverses and
quantitative laws use the implemented finite domains. No new axioms or local
`sorry` placeholders were added.

These results establish the stated codec and state-transition properties.
They do not establish a theorem for the entire resource checker against a
machine operational semantics or verify a backend allocation strategy.

## Migration observations

Environment format is 3, catalog-manifest format is 2, and claim/proof envelopes
bind format 3 plus a validator identity. Old typed objects, claims, and
primitive addresses require regeneration. The historical Mathlib proof fixture
retains its original hash and root bytes and now rejects at the v3 envelope
boundary.

The v3 VM's decoding and canonicality checks change its deterministic FFT-cost
estimates. Across the 83 existing kernel pins the increase over the pre-v3
baseline is 0.008%–1.278%; `Nat.add_comm` changes from 321,012,193 to 322,598,714.
The shard fixture changes from 6,999,296,124 to 7,072,190,269 (+1.041%). Exact
equality assertions are retained when migrating these pins.

An initial v3 implementation traversed counted byte sequences before parsing
them. Removing those preliminary walks preserves rejection through strict
incremental reads and reduces every kernel pin, by 0.021%–6.975%. For
`Nat.add_comm`, the cost falls from 336,711,085 to 322,598,714 (-4.191%), removing
89.894% of its initial v3 increase. The shard falls from 7,645,795,797 to
7,072,190,269 (-7.502%). The generated VM and bytecode interpreter agree on the
new per-circuit counts. These figures are deterministic estimates of FFT work.

The v3 suite and primitive-closure validation are registered in CI. This record
does not claim execution of the specialized CUDA, SP1, or Zisk toolchain jobs.
