# Trusted-extern ledger

The machine-readable ledger is
[`trusted-externs.json`](trusted-externs.json); `check-trusted-externs` validates
it with [`scripts/CheckTrustedExterns.lean`](../scripts/CheckTrustedExterns.lean).

**Status, 2026-09-29.** The required checks were removed while the compiler
is rebuilt ([CI guide](ci.md)), and the Ixby backend left main (branch
`jcb/ixby-archive`). `check-trusted-externs` no longer runs. The integrity
pins in `trusted-externs.json` still name removed files; they are refreshed
when the audit returns as a gate.

This document separates four things that are easy to blur:

1. a native semantic boundary whose result Compilatr.ix uses;
2. the Gen-0 seed/build/runtime supply chain used to construct and test it;
3. a target specification or emitter assumption not yet connected by proof;
4. interpreter oracles that are mathematical models, not linked native code.

Only the first category is a target-language trusted extern. A specification
assumption is nevertheless part of a native-correctness claim until its
reference bridge lands. The other categories still matter to bootstrap and
test confidence, so they are accounted for without pretending they are
`@[extern]` declarations.

## Change-control rule

Every native interface, whether project-local or supplied by an external Lake
package, must have an entry. For a native dependency, every `@[extern]` symbol
anywhere in its pinned source tree is listed — including sibling modules this
repository does not import and exports it does not call. Project-local Lean
extern declarations and C `LEAN_EXPORT`s are exact, separately checked
inventories. Every symbol records its shipping module and current reachability;
each interface names the semantics assumed, owner, evidence, proof effect, and
an observable retirement condition.

Target semantics, encoder, and object-writer assumptions follow the same discipline: each
entry states the exact scope, proof effect, independent evidence, and staged
retirement theorem. They add no Lean axiom merely by being recorded, but a
native-execution claim may not silently omit them.

The checker deliberately fails closed on changes to:

- Lake dependencies and revisions;
- the Lean source inventory itself, derived from the controlled
  `lakefile.lean` `lean_lib`/`lean_exe` declarations (unsupported syntax, a
  missing root, or an empty root set is a hard failure, so a new top-level
  module cannot escape the scan);
- external import roots and qualified native entry points used in project
  sources;
- the complete extern inventory of every `.lean` file in each pinned package
  source tree, covering `@[extern ...] opaque`/`def` declarations and
  post-hoc `attribute [extern ...]` commands, plus each symbol's
  imported/unimported reachability claim (checked against actual imports);
- the exact project-local Lean extern inventory, each Lake-referenced C source,
  its pinned SHA-256, and its exact `LEAN_EXPORT` inventory;
- declaration-level `axiom`, standalone `sorry`, or `native_decide` tokens in
  the checked project sources (a conservative lexer excludes comments and
  literals and retains line locations);
- every package/version and the complete checksum-bearing Cargo lockfile;
- every locked Nix flake node and the build-selection files, including
  `.envrc` (it injects `NIX_CONFIG` for direnv users);
- the integrity-pinned independent x86 decoder and ELF object/link checks used
  as E0 evidence, including their native harness;
- the fresh-process source-coverage, source-recursion, source-call-reuse, and
  source-unique-reuse checkers and their reviewed address, observation, and
  rejection matrices;
- every `uses:` reference in every CI workflow file: a reference not pinned
  to a full 40-hex commit is rejected outright, and the pinned inventory must
  match the ledger.

Updating a dependency therefore requires reviewing and updating this ledger,
not merely refreshing a lockfile. An entry may only be removed when its exit
criteria are met and the coverage check confirms that its boundary vanished.

All repository check scripts are Lean executables. The trust auditor uses
the pinned Lake TOML parser and GNU `sha256sum`; the independent encoder
and object checks invoke GNU binutils
and, on x86-64 Linux, the existing native C harness. These remain seed/build
tools and introduce no project native interface or proof axiom. The
support modules, executable scripts, native harness, and source matrices
have reviewed integrity pins.

The ledger also pins benchmark adapters, runner/checkers, manifest, and
comparison toolchains. Clock, allocation, GC, process-memory, compiler, and
runtime measurements belong to build/measurement trust, separately from
production source/compiler proof assumptions.

Compiler comparisons and measurement runners live in an optional package
outside the root flake, being rebuilt for the new benchmark ladder
([benchmark design](benchmark-plan.md)). CakeML and CompCert are never
dependencies of the root flake checks.

`lake exe check-tools-tests` exercises the auditor on isolated temporary
copies. It checks source literals/comments, unrecognized extern attributes,
new executable roots, project/dependency extern drift, imports and native
entry points, integrity changes, malformed/duplicate Cargo metadata, and CI
action drift. The Nix trust-ledger check runs these regressions too.

The `CompilatrixTests` Lake root keeps every test and fence inside the
audited source inventory, and the proof aggregate `CompilatrixTests.Proofs`
imports every fence. The [CI guide](ci.md) records the current check surface
and its coverage changes.

The pinned upload/download actions transfer the producing workflow run's
compiled runtime artifact and diagnostic logs. Downloads use its artifact ID
and reject digest mismatch; a separate SHA-256 and expected Nix output-path
check precede execution. Pinned Lean shared libraries supply the same CI
runtime symbols previously linked into each executable. These changes affect
build/runtime packaging and add no target-language native interface.

## Active native interface: BLAKE3 Rust

| Field | Ledger value |
| --- | --- |
| Owner | Compilatr.ix maintainers |
| Project entry points | `Blake3.Rust.hash` in `Compilatrix/Ixon/Hash.lean`; `Blake3.Rust.Hasher` in the v3 typechecker's node/context hashing |
| Assumed semantics | Standard BLAKE3 XOF over exactly the input bytes; a 32-byte request is the standard 256-bit digest |
| Logical/proof status | Assumption: no Lean refinement theorem connects returned bytes to a pure BLAKE3 specification. Canonical-address identity is conditional on an explicit pairwise `Address.Blake3NoCollision` premise; no global hash-injectivity axiom is asserted. Theorems whose premise is a successful addressed check (Ixon v3 ingress, catalog admission, typing and claim binding) expose the exact native hash dependency, pinned in the `CompilatrixTests/Fences/IxonV3*.lean` fences. |
| Evidence | Official empty-input vector, output length, determinism and input-sensitivity checks, and the frozen Ixon v3 constant, environment, catalog and claim fixtures with independently recorded addresses |
| Primary pin | Blake3.lean `c32002eeed36c520dfb73de32ef53483652e3aa5` |
| Rust implementation | `blake3` 1.8.7; `lean-ffi` `163a661847d8171a685570ed12b4c03bfa092778` |
| Retirement | Pure Lean BLAKE3 plus a refinement theorem and official corpus compatibility, compiled by our backend |

The Nix build shares the root Lean 4.34.0 toolchain with Blake3's Lean modules
and Rust FFI header generation. It rejects differing root and dependency
`lean-toolchain` pins. The Lean 4.34.0 update moves Blake3.lean from
`c9b2273f` to `c32002ee`. That revision updates the `blake3` crate and C
sources to 1.8.7 and lean-ffi to `163a6618`, and refreshes the Cargo lock.
The lock now resolves two `shlex` releases, which the ledger records as a
version list. The package precompiles its Lean libraries, so importing
elaborators load the same native objects as shared libraries. It also adds a
pure Lean `Blake3.Pure` module with no extern declarations, which Compilatr.ix
does not import. The native symbol set and the Rust entry points are unchanged
apart from the reported version string.

The v3 checker uses incremental `Hasher.init`, `update` and
`finalizeWithLength` for tagged node and context preimages. These call the
same three active native symbols as the existing hash entry point. The
32-byte output bound is discharged by a kernel proof; no additional native
reflection axiom is introduced. Keyed and derive-key operations remain unused.

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

## Ix frontend / Ixon v3 source boundary

The [v3 source adapter](ixon-v3.md) is pinned independently to ix
`0a31c8dbc63755924c645bf1afedc563e395e88a`. It preserves independent usage,
ownership, relative locality, arrow results, and borrow lets. Pure resource
algorithms and selected state invariants are adapted from that snapshot;
canonical bytes, source roots, profile identities and native resource claim
framing are checked against frozen producer fixtures. The combined validator
now executes the pinned anonymous erased typechecker on the same raw bytes,
fixes literal primitives, and checks every source key. Pure integer codecs,
ordered universe maps and explicit hash-length proofs avoid additional native
interfaces or reflection axioms. Eight new exact fences retain the existing
BLAKE3 axiom basis. Four frozen primitive closures, canonical recursors and
adversarial cases run in the required suite. A whole-checker semantic soundness
theorem, v3 backend simulation and IxVM resource proofs remain outside this boundary.
The old v2 compiler entry points keep their original proof and fixture scope.

Catalog-v2 admission additionally binds manifest version 2, object format 3
and erased-lean-v1 (validator 1) to original manifest/piece bytes. It verifies
roots, file hashes, counts, aggregate bounds, closed union assumptions and
actual union typing. Chunked membership requires complete sorted address
witnesses checked against each committed member root and count; first-owner
assignment and full union coverage are checked explicitly. Producer labels,
pins and preimage hashes are metadata, not proof. Four further exact fences
preserve the same axiom basis. The 445 catalog assertions include producer
fat and independently Rust-verified chunk fixtures, corruptions, exact bounds
and filesystem/CLI tests. Validator 1 does not select a resource profile.

## Aiur logical-trace boundary

The [Aiur foundation](aiur-backend.md) pins eleven pure upstream Lean modules
at `a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03`. It introduces no native Aiur
interface or new axiom. The checked logical-trace API retains field-weighted
balance, activity, a consumer bound, and one coherent witness heap. A mixed
static-order/counter/rank certificate yields finite rooted derivations.

The row certificate remains a premise until bytecode checking and AIR
extraction establish its facts. The logical-trace API alone does not identify
those rows with the keyed circuit or establish Ixon/DSL source preservation.
Its 33 exact axiom assertions use only the
ordinary logical basis, and its source-inventory and regression gates are
required. The ledger records this scope as `aiur-logical-trace-v0`.

The [Aiur bytecode wire boundary](aiur-wire.md) adds complete canonical
`aiur-bytecode/1` preimages, bounded readers, round-trip/canonicality and
representable-domain injectivity proofs, and addressed ingress. Its 33 new
exact axiom assertions keep pure codec and component facts on ordinary logic;
five addressed wrappers inherit the same native BLAKE3 exception already
used by other content-addressed IRs. Root-based artifact recovery requires
an explicit pairwise collision premise. No new native interface is added.

Component ingress retains the exact pinned checker result after bounding
declared allocations and an analysis work score. It does not establish the
checker-to-AIR theorem or validate arbitrary bytecode/circuit semantics.
Four handwritten golden fixtures, 308 runtime assertions, and fresh-process
replay/corruption tests guard the wire contract. The production IxVM export,
constraint dump, descriptor/key binding, and source preservation remain
separate obligations under `aiur-bytecode-wire-v1`.

The [witness-heap execution model](aiur-semantics.md) supplies concrete
semantics for all 34 pinned opcodes and four controls. Checked local rows,
the validated trace, and its static row certificate yield finite executions
against one heap and an explicit allowed-advice predicate. Thirty-nine new
exact fences use only ordinary logic; no native interface or axiom is added.
The 276 execution regressions and kernel examples remain in the Aiur gate.

The [static assignment checker](aiur-static.md) extends this boundary with
checked construction of that certificate from ordinary ranks and logical
rows. Counter columns/directions come from the exact checked program; every
provider dependency is checked. It adds 116 runtime assertions and 39 exact
fences while preserving all 2177 prior assertions. Thirty-eight cones use
ordinary logic; the addressed adapter inherits the existing BLAKE3 axiom
through ingress evidence. No new native axiom or interface is introduced.

The [universal counter-analyzer proof](aiur-counter-analysis.md) connects the
actual pinned search and checker to every successful local body, with
arbitrary replies and advice. It proves all four normalized directions and
excludes short self-call cycles. Its 19 kernel regressions and 48 exact
ordinary-logic fences preserve all 2216 prior assertions. It adds no new
axiom or native interface and leaves executable validation unchanged.

The [memory AIR extraction](aiur-memory-air.md) proves selected-pointer
uniqueness and one coherent heap from the four modeled memory polynomials,
distinct bucket identities, and table heights below the characteristic.
It handles arbitrary starting pointers and field wraparound. Exact lookup
weight and payload theorems connect the physical memory channel to the
logical cell. Activity additionally requires Boolean selectors, which the
bounded table checker checks; deriving Booleanity from the polynomial alone
remains open. Its 52 runtime assertions, 16 kernel regressions, and 46 exact
ordinary-logic fences preserve all 2264 prior assertions. Five frozen graphs
from the actual pinned Rust builder are compared in a fresh process, with
eight mutation rejections. This fixture evidence establishes no universal
Rust theorem or full IxVM assignment/key binding.

The [rank AIR extraction](aiur-rank-air.md) derives scalar-u16 bounds from
normalized exact-message balance and fixed-table providers, then derives
strict natural rank increase from the ordered call's complete physical
message. The demand bound remains explicit; field multiplicities need not
be natural counts. Rank is retained through matching, and the local checked
edge theorem does not infer a whole static certificate after erasing that
field. Its 71 runtime assertions, 22 kernel regressions, and 63 ordinary-logic
fences preserve all 2310 prior assertions. Six actual Rust function fixtures
and all 65,536 fixed-table row pairs are checked, with 14 mutation rejections.
The optional producer includes the pinned Rust module tree unchanged; it
adds no production dependency, native interface, or axiom. Selector facts,
the full rank-preserving projection, and assignment/key binding remain open.

The ledger records this model as `aiur-witness-bytecode-v0`. Its logical
gadget channels are not Rust AIR channels. Primitive conformance, extraction
from the keyed AIR, and refinement to the honest allocator/evaluator remain
obligations. `ioSetInfo` and `ioWrite`
have no constrained effect in this model, and hints retain arbitrary allowed
answers until constrained code checks them. This is a specification boundary,
not a new cryptographic or native trust assumption.

## Target specification boundaries: x86-64 v0

[E1](x86-encoded-instructions.md) proves every emitted local instruction
form. [E2](x86-stream-objects.md) now certifies complete production text and
independent ELF interpretation, and the N2 source endpoint consumes actual
object execution. The JSON retains stable boundary identifiers and records
exactly which portions are discharged.

The [indexed stream checker](stream-checking.md) preserves this boundary:
bounded decoding and cached canonical positions are proved exactly equal
to the original decoder and stream checker on all inputs. Production
emission and relocation validation use the same `Stream.Valid` certificate.
Four additional public fences retain the ordinary logical axiom basis.

| Boundary | Current scope | Evidence and remaining work |
| --- | --- | --- |
| Local ISA semantics | Agreement of the local byte machine with actual x86-64, including canonical addresses, unified code fetch, memory permissions, flags, faults, and the caller ABI. Compiler-contract traps must be proved unreachable; they are not hardware exceptions. | E1 and E2 prove local-to-local agreement. The [S0 readiness decision](x86-reference-model.md) pins the Sail snapshot; reference execution comparison, the Lean adapter, and S2 agreement remain pending. |
| Encoder stream/layout | Discharged for successful certified production emission. Raw `Encode.encode`/`Program.encode` clients must validate their output or prove the same facts. | `Stream.check_sound` checks every boundary, canonical position, target and relocation. Complete-stream proofs cover call-free execution and internal calls under concrete `SafeTrace` conditions, including residual return-slot bytes. `ELFLink` proves checked PC32 application and runtime CALL transfer. External procedure bodies still require their semantic/ABI contracts. |
| ELF serialization and system loading | Independent interpretation is discharged for successful `ELF.writeChecked` output. Raw `ELF.write` clients lack that certificate. Actual system linker/loader behavior remains assumed. | `ELFRead` independently parses actual fields; `ELF.check_sound` certifies text, bounded/aligned/nonoverlapping sections, export placement, symbols, relocations, non-executable stack and exact provenance. `ObjectEval` begins from the parsed export and text. A real loader must implement the proved PC32 rule, map immutable executable text, resolve named procedures and enter with the stated ABI. |

The reviewed format references are the [generic ABI ELF specification](https://gabi.xinuos.com/elf.pdf)
and [x86-64 psABI](https://refspecs.linuxfoundation.org/elf/x86_64-SysV-psABI.pdf).
The existing provenance note uses the Linux/GNU four-byte convention for
ELF64 notes, explicitly supported by [GNU binutils](https://sourceware.org/pipermail/binutils-cvs/2017-November/046965.html).
It does not claim generic ELF64 eight-byte note alignment.

The independent instruction and ELF readers import neither corresponding
writer. All production object emitters validate the actual outputs and
retain proof fields. This is fail-closed translation validation, with no
claim of completeness for the unchecked encoder or writer. The AST still
excludes division, floating point, SIMD, atomics, indirect calls, syscalls,
TLS, high-byte registers, RSP SIB indices, and byte-width two-operand IMUL.

E2 adds 23 public axiom fences. Its generic stream/object laws use ordinary
logical axioms; the indexed N2 source endpoint retains its existing native
BLAKE3 dependency. The source argument, sharing/oracle, successful-application
and bounded-ABI premises remain explicit, along with successful certified
emission and an initial readable caller return slot outside the arena.
The proof derives preservation of that slot and actual physical return.

The integrity-pinned stream/object gate checks 14 complete streams, 50
branch objects, 15 stream corruptions, 1,010 object mutations/truncations,
10 relocation cases, six stack contracts and a physical caller-slot fault.
It also executes one actual source-selected N2 object pair for all eight
runtime inputs (6,512 byte steps), checking registers, every arena byte,
reversed pointer graphs and complete reclamation. Existing GNU readelf,
objdump, fresh-artifact and linked-native checks remain independent evidence.

## Seed, runtime, and build trust

These entries explain what can affect a Gen-0 build without mislabeling it as
a project FFI symbol.

| Entry | Current role | Retirement/containment |
| --- | --- | --- |
| Lean 4.34.0 seed/runtime | Elaborates, kernel-checks, compiles, executes `#guard`s, and hosts compiled tests | Gen-1 self-host plus address-exact diverse double compilation; production checking moves to the public lean4ix/ix verified checker |
| GMP 6.3.0 | Lean runtime arbitrary-precision arithmetic; direct Nix build input | Verified limb bignums refining `Nat`/`Int`, compiled in the no-runtime fragment after M3 |
| Host C ABI/runtime | glibc 2.40-66 on the x86_64-linux baseline, plus compiler runtime; hosts Lean/Rust and implements the ledgered `open`/`fstat`/`fsync`/`close` durability shim | Gen 1 removes upstream runtime; allocator/memcpy and libc surface retire to verified `.ix` code plus a syscall model |
| Locked Nix supply chain | nixpkgs, lean4-nix, flake-parts, crane, fenix/Rust, host C compiler/linker, GNU binutils readelf/objdump, rsync, binary substitution | Locked hashes now; later diverse reproduction and address-exact output comparison remove it from the semantic TCB |
| GitHub runner/actions | Runs the locked flake automatically | CI is advisory; release attestation must reproduce the flake independently |

The recorded GMP/glibc versions describe the inspected x86_64-linux closure.
Other configured systems use their corresponding locked Nix platform closure;
the ledger does not claim that Darwin uses glibc.

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

