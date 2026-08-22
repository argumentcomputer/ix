# Trusted-extern ledger

Last reviewed: 2026-08-19. The machine-readable ledger is
[`trusted-externs.json`](trusted-externs.json); `nix flake check` validates
it with [`scripts/check_trusted_externs.py`](../scripts/check_trusted_externs.py).

This document separates three things that are easy to blur:

1. a native semantic boundary whose result Compilatr.ix uses;
2. the Gen-0 seed/build/runtime supply chain used to construct and test it;
3. interpreter oracles that are mathematical models, not linked native code.

Only the first category is a target-language trusted extern. The others still
matter to bootstrap and test confidence, so they are accounted for without
pretending they are `@[extern]` declarations.

## Change-control rule

Every external Lake package and external Lean import root must have an entry.
For a native package, every `@[extern]` symbol anywhere in its pinned source
tree is listed — including sibling modules this repository does not import and
exports it does not call — with the shipping module and current reachability
recorded per symbol. Each entry names the semantics assumed, owner, evidence,
proof effect, and an observable retirement condition.

The checker deliberately fails closed on changes to:

- Lake dependencies and revisions;
- the Lean source inventory itself, derived from `lakefile.toml`
  `[[lean_lib]]`/`[[lean_exe]]` roots (a missing root or an empty root set is
  a hard failure, so a new top-level module cannot escape the scan);
- external import roots and qualified native entry points used in project
  sources;
- the complete extern inventory of every `.lean` file in each pinned package
  source tree, covering `@[extern ...] opaque`/`def` declarations and
  post-hoc `attribute [extern ...]` commands, plus each symbol's
  imported/unimported reachability claim (checked against actual imports);
- declaration-level `axiom`, standalone `sorry`, or `native_decide` tokens in
  the checked project sources (a tripwire on comment/string-stripped lines);
- every package/version and the complete checksum-bearing Cargo lockfile;
- every locked Nix flake node and the build-selection files, including
  `.envrc` (it injects `NIX_CONFIG` for direnv users);
- every `uses:` reference in every CI workflow file: a reference not pinned
  to a full 40-hex commit is rejected outright, and the pinned inventory must
  match the ledger.

Updating a dependency therefore requires reviewing and updating this ledger,
not merely refreshing a lockfile. An entry may only be removed when its exit
criteria are met and the coverage check confirms that its boundary vanished.

## Active native interface: BLAKE3 Rust

| Field | Ledger value |
| --- | --- |
| Owner | Compilatr.ix maintainers |
| Project entry point | `Blake3.Rust.hash` in `Compilatrix/Ixon/Hash.lean` |
| Assumed semantics | Standard BLAKE3 XOF over exactly the input bytes; a 32-byte request is the standard 256-bit digest |
| Logical/proof status | Assumption: no Lean refinement theorem currently connects returned bytes to a pure BLAKE3 specification. Canonical-address identity is conditional on an explicit pairwise `Address.Blake3NoCollision` premise; no global hash-injectivity axiom is asserted. |
| Evidence | Official empty-input vector, output length, determinism/input-sensitivity checks, and a full constant-address fixture in `Tests.lean` |
| Primary pin | Blake3.lean `aaf530784082a2c00b0a93648741429d274102ca` |
| Rust implementation | `blake3` 1.8.4; `lean-ffi` `cc98ebf67bf453ac3827cb767f78b13ea674dd6a` |
| Retirement | Pure Lean BLAKE3 plus a refinement theorem and official corpus compatibility, compiled by our backend after M3 |

The audit enumerates extern declarations across the entire pinned package
source tree — every `.lean` file, in `@[extern ...] opaque`/`def` and
post-hoc `attribute [extern ...]` form — not just the imported entry module.
The tree ships twelve C-ABI symbols across two backend modules. Compilatr.ix
imports only `Blake3.Rust`; the active hash path calls `rs_blake3_init`,
`rs_blake3_hasher_update`, and `rs_blake3_hasher_finalize`, and the version,
keyed-init, and derive-key exports remain listed because downstream code can
reach the imported public API. The sibling `Blake3.C` module binds the
vendored C implementation behind six `c_blake3_*` symbols; it is not imported
(the checker verifies this against actual imports), so none of them are
linkable from this project today, but enabling them is one lakefile line
away, so they are listed and any drift fails the check:

| Lean declaration | Foreign symbol | Current reachability |
| --- | --- | --- |
| `Blake3.Rust.internalVersion` | `rs_blake3_version` | imported, uncalled |
| `Blake3.Rust.hasherInit` | `rs_blake3_init` | active hash path |
| `Blake3.Rust.hasherInitKeyed` | `rs_blake3_init_keyed` | imported, uncalled |
| `Blake3.Rust.hasherInitDeriveKey` | `rs_blake3_init_derive_key` | imported, uncalled |
| `Blake3.Rust.hasherUpdate` | `rs_blake3_hasher_update` | active hash path |
| `Blake3.Rust.hasherFinalize` | `rs_blake3_hasher_finalize` | active hash path |
| `Blake3.C.internalVersion` | `c_blake3_version` | present, unimported |
| `Blake3.C.hasherInit` | `c_blake3_init` | present, unimported |
| `Blake3.C.hasherInitKeyed` | `c_blake3_init_keyed` | present, unimported |
| `Blake3.C.hasherInitDeriveKey` | `c_blake3_init_derive_key` | present, unimported |
| `Blake3.C.hasherUpdate` | `c_blake3_hasher_update` | present, unimported |
| `Blake3.C.hasherFinalize` | `c_blake3_hasher_finalize` | present, unimported |

The complete 39-package Cargo inventory (including bindgen/build-time crates)
is stored by name and exact version in the JSON ledger. Its exact Cargo.lock
SHA-256 is also pinned, so source URLs, checksums, and dependency edges cannot
change while leaving the name/version inventory unchanged.

Retirement is complete only when no native Blake3 module is imported, existing
address fixtures either remain byte-identical or undergo an explicit versioned
address roll, the official vector corpus passes, and the Rust static library
is absent from the runtime closure.

## Seed, runtime, and build trust

These entries explain what can affect a Gen-0 build without mislabeling it as
a project FFI symbol.

| Entry | Current role | Retirement/containment |
| --- | --- | --- |
| Lean 4.33.0 seed/runtime | Elaborates, kernel-checks, compiles, executes `#guard`s, and hosts compiled tests | Gen-1 self-host plus address-exact diverse double compilation; production checking moves to the ix4lean-derived verified checker |
| GMP 6.3.0 | Lean runtime arbitrary-precision arithmetic; direct Nix build input | Verified limb bignums refining `Nat`/`Int`, compiled in the no-runtime fragment after M3 |
| Host C ABI/runtime | glibc 2.40-66 on the x86_64-linux baseline, plus compiler runtime; hosts Lean and Rust | Gen 1 removes upstream runtime; allocator/memcpy and libc surface retire to verified `.ix` code plus a syscall model |
| Locked Nix supply chain | nixpkgs, lean4-nix, flake-parts, crane, fenix/Rust, Clang/LLD, rsync, binary substitution | Locked hashes now; later diverse reproduction and address-exact output comparison remove it from the semantic TCB |
| GitHub runner/actions | Runs the locked flake automatically | CI is advisory; release attestation must reproduce the flake independently |

The recorded GMP/glibc versions describe the inspected x86_64-linux closure.
Other configured systems use their corresponding locked Nix platform closure;
the ledger does not claim that Darwin uses glibc.

## Modeled extern oracles are not native dependencies

IxIR₀ and IxIR₁ intentionally make extern semantics parametric in an oracle.
The current concrete oracles are test fixtures:

- IxIR₀ address `[0x40; 32]`: two literal `Nat`s map to their sum; any
  constructor-shaped input is rejected.
- IxIR₁ address `[0x67; 32]`: two scalar literal `Nat`s map to their sum.

Neither is linked foreign code or production-approved. They test the formal
hook through which a future per-address ledger entry will connect to the IR.
Likewise, erasure may represent source opaque/partial/axiom declarations as
`IxIR0.Decl.extern`, but the proof-producing erasure validator currently
rejects that frontier. Lowering a declaration does **not** authorize an
implementation. Production execution requires a new per-address entry and a
source/target oracle correspondence proof.

## Known limitations

- BLAKE3 has conformance tests, not a refinement proof or collision-resistance
  formalization. Address-identity theorems expose the required pairwise
  no-collision condition as a premise rather than hiding it in the TCB.
- The GitHub-hosted runner image is mutable even though both actions are pinned
  by full commit.
- The ledger covers the current Gen-0 repository/build closure. Future libc,
  IO, store, thread, float, or syscall primitives are unapproved until added
  per symbol/address.
- “Empty ledger” means no persistent target/runtime extern assumptions. Seed
  provenance and independently reproducible build attestation remain separate
  bootstrap obligations.
