# Ixon v3 implementation and verification record

> **Historical record.** This file records the gates executed when the
> contract model (usage, ownership, relative locality) was introduced in
> format v3. The current format is **v4**, which keeps that contract model
> but replaces Tag0/Tag2/Tag4 with TagN and makes sharing canonical. See
> the [v4 specification](Ixon-v4.md) and [Ixon](Ixon.md). The figures below
> were measured on v3 and are not re-asserted for v4. In particular, the
> byte sizes, addresses and FFT-cost pins all change with the v4 bytes.

<!-- PENDING: [verify] v4 verification record: run the CI-equivalent gates at the PR commit (lake build; lake build IxCompileVerify IxTcVerify; lake test, the ignored suites compile-determinism, fidelity-*, rust-compile, rust-serialize, rust-decompile, decompile-diff, ixon-corpus, ixvm; lake test -- cli; ixon-v4-tests and ixon-v4-primitives; cargo test --workspace; cargo clippy -D warnings; cargo fmt --check; lake lint; lake exe ix codegen --check) and record the commands and results in a v4 record linked from here. -->

Ixon v3 carries independent usage, ownership, and relative-locality contracts
through the Ix source frontend, Lean and Rust compilers, canonical bytes,
sharing, text syntax, FFI, and decompilation. Scoped shared borrowing uses an
explicit let kind. Native admission checks resources and erased typing before
an annotated production artifact is emitted.

## Implemented boundary (contract model)

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

## Executed gates (v3)

Commands run from the repository root at the v3 change:

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

## Formal trust frontier (v3)

At the v3 change the compiler manifest audited 143 roots. (For v4 the
manifest has 250 roots at commit `d47b39f9`, including the TagN and
sharing-construction theorems.) The typechecker manifests audited 2,034
completed roots, one conditional root, and seven statement roots. Their
existing transitive assumptions remain explicit in the manifests. Both local
sorry-frontier checks passed.

The new resource audit covers 15 roots connected to executable quantitative,
scope, ownership, loan-ending, and join checks. Contract-code inverses and
quantitative laws use the implemented finite domains. No new axioms or local
`sorry` placeholders were added.

These results establish the stated codec and state-transition properties.
They do not establish a theorem for the entire resource checker against a
machine operational semantics or verify a backend allocation strategy.

## Migration observations (v3)

At the v3 change the environment format was 3, the catalog-manifest format 2,
and claim/proof envelopes bound format 3 plus a validator identity (v4 moves
the format to 4; the catalog-manifest format stays 2). Old typed objects,
claims, and primitive addresses required regeneration. The historical Mathlib
proof fixture retains its original hash and root bytes and rejects at the
envelope boundary.

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
does not claim execution of the specialized CUDA toolchain job.
