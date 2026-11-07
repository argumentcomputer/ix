# Trusted-extern ledger

The machine-readable ledger is
[`trusted-externs.json`](trusted-externs.json); `nix flake check` validates
it with [`scripts/CheckTrustedExterns.lean`](../scripts/CheckTrustedExterns.lean).

**Status, 2026-09-29.** The inventory was reset for the rebuilt compiler.
Removed with the legacy pipeline: the durable-filesystem native interface,
the IxIR and Ixby specification assumptions, the modeled IxIR oracles, the
hosted CI actions and runner, and the comparison-runtime pins. All remain
on branch `jcb/ixby-archive`. `nix flake check` runs the audit again.

This document separates four things that are easy to blur:

1. a native semantic boundary whose result IxCC uses;
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
- every `uses:` reference in any CI workflow file: a reference not pinned
  to a full 40-hex commit is rejected outright, and the pinned inventory must
  match the ledger. The inventory is empty while hosted workflows are removed.

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

Clock, allocation, GC, process-memory, compiler and runtime measurements
belong to build and measurement trust, separately from production
source/compiler proof assumptions.

Compiler comparisons and measurement runners live in an optional package
outside the root flake, being rebuilt for the new benchmark ladder
([benchmark design](benchmark-plan.md)). CakeML and CompCert are never
dependencies of the root flake checks.

`lake exe check-tools-tests` exercises the auditor on isolated temporary
copies. It checks source literals/comments, unrecognized extern attributes,
new executable roots, project/dependency extern drift, imports and native
entry points, integrity changes, malformed/duplicate Cargo metadata, and CI
action drift. The Nix trust-ledger check runs these regressions too.

The `IxCCTests` Lake root keeps every test and fence inside the
audited source inventory, and the proof aggregate `IxCCTests.Proofs`
imports every fence. The [CI guide](ci.md) records the current check surface
and its coverage changes.

## Active native interface: BLAKE3 Rust

| Field | Ledger value |
| --- | --- |
| Owner | IxCC maintainers |
| Project entry points | `Blake3.Rust.hash` in `IxCC/Ixon/Hash.lean`; `Blake3.Rust.Hasher` in the v3 typechecker's node/context hashing |
| Assumed semantics | Standard BLAKE3 XOF over exactly the input bytes; a 32-byte request is the standard 256-bit digest |
| Logical/proof status | Assumption: no Lean refinement theorem connects returned bytes to a pure BLAKE3 specification. Canonical-address identity is conditional on an explicit pairwise `Address.Blake3NoCollision` premise; no global hash-injectivity axiom is asserted. Theorems whose premise is a successful addressed check (Ixon v3 ingress, catalog admission, typing and claim binding) expose the exact native hash dependency, pinned in the `IxCCTests/Fences/IxonV3*.lean` fences. |
| Evidence | Official empty-input vector, output length, determinism and input-sensitivity checks, and the frozen Ixon v3 constant, environment, catalog and claim fixtures with independently recorded addresses |
| Primary pin | Blake3.lean `3f8b805614a0bae1c033469ff893a8f0ee85f601` |
| Rust implementation | `blake3` 1.8.7; `lean-ffi` `163a661847d8171a685570ed12b4c03bfa092778` |
| Retirement | Pure Lean BLAKE3 plus a refinement theorem and official corpus compatibility, compiled by our backend |

The actual compiler composition results in `Recheck/Proof/Compile.lean`
retain this same native hash dependency through their ingress/producer premises.
Seven required exact fences in `IxCCTests/Fences/Compile.lean` record
the three standard logical axioms plus
`Blake3.HasherOps.hash._native.native_decide.ax_1`. No axiom declaration,
native symbol or dependency was added. `Recheck.run` and `Recheck.sound` retain
their original exact fences. The compiler bridge is SrcEval-relative and does
not discharge the source-model or resource-profile compatibility obligations.

The Nix build shares the root Lean 4.34.1 toolchain with Blake3's Lean modules
and Rust FFI header generation. It rejects differing root and dependency
`lean-toolchain` pins. The Lean 4.34.0 update moved Blake3.lean from
`c9b2273f` to `c32002ee`. That revision updates the `blake3` crate and C
sources to 1.8.7 and lean-ffi to `163a6618`, and refreshes the Cargo lock.
The lock now resolves two `shlex` releases, which the ledger records as a
version list. The package precompiles its Lean libraries, so importing
elaborators load the same native objects as shared libraries. It also adds a
pure Lean `Blake3.Pure` module with no extern declarations, which IxCC
does not import. The native symbol set and the Rust entry points are unchanged
apart from the reported version string. The Lean 4.34.1 update moves
Blake3.lean from `c32002ee` to `3f8b8056`, the revision ix's certified line
pins. It changes only the package's `lean-toolchain`, its `lean4-nix` lock and
its CI workflows; the Lean sources, Rust sources and Cargo lock are
unchanged.

The v3 checker uses incremental `Hasher.init`, `update` and
`finalizeWithLength` for tagged node and context preimages. These call the
same three active native symbols as the existing hash entry point. The
32-byte output bound is discharged by a kernel proof; no additional native
reflection axiom is introduced. Keyed and derive-key operations remain unused.

The audit enumerates extern declarations across the entire pinned package
source tree — every `.lean` file, in `@[extern ...] opaque`/`def` and
post-hoc `attribute [extern ...]` form — not just the imported entry module.
The tree ships twelve C-ABI symbols across two backend modules. IxCC
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

## Ix frontend / Ixon v4 source boundary

The [source adapter](ixon-v4.md) reads Ixon v4 through ix's pure codec (the
pure Lean dependency below) and keeps the data model, resource algorithms and
erased checker adapted from ix `0a31c8dbc63755924c645bf1afedc563e395e88a`
(Ixon v3), with the checker's primitive table and the resource profile and
claim framing moved to ix `f829b76044a44a61023d0983516137147bbb12a7`. It
preserves independent usage, ownership, relative locality, arrow results, and
borrow lets. Canonical bytes, source roots, profile identities and native
resource claim framing are checked against ix's frozen v4 fixture package.
Ingress authenticates every object and the constant root with pure BLAKE3
(`Blake3.Pure`); the erased checker's internal hashing and the resource
commitments keep the Rust BLAKE3 interface above. The combined validator
executes the pinned anonymous erased typechecker on the same raw bytes, fixes
literal primitives, and checks every source key. Explicit hash-length proofs
avoid reflection axioms. Eight exact fences retain the existing BLAKE3 axiom
basis. Four frozen primitive closures, canonical recursors and adversarial
cases run in the required suite. A whole-checker semantic soundness theorem,
backend simulation and IxVM resource proofs remain outside this boundary.

Catalog-v2 admission additionally binds manifest version 2, object format 4
and erased-lean-v1 (validator 1) to original manifest/piece bytes. It verifies
roots, file hashes, counts, aggregate bounds, closed union assumptions and
actual union typing. Chunked membership requires complete sorted address
witnesses checked against each committed member root and count; first-owner
assignment and full union coverage are checked explicitly. Producer labels,
pins and preimage hashes are metadata, not proof. Four further exact fences
preserve the same axiom basis. The 445 catalog assertions include producer
fat and independently Rust-verified chunk fixtures, corruptions, exact bounds
and filesystem/CLI tests. Validator 1 does not select a resource profile.

The required ownership consumer regression retains authentic historical
cb68d94c annotated/plain recursion bytes under
`fixtures/ownership/historical/annotated-recursion-cb68/`. Its pinned inventory
includes the source twins, raw named/anonymous bytes and sidecars, original
profile, address receipts and independent literal reference results. Tests
verify those hashes before ingress and compare 36 complete Src/Fir/Own
observations. A test-only adapter accepts the historical plain sidecar's
absent or empty checked list only when no profile is present; malformed and
nonempty orphan claims are refused. Production paired-key parsing is unchanged.
The annotated erased contract retains its explicit plain-RC domain refusal.
These fixtures and the valid-neighbor resource/csimp controls add no native
interface, symbol, dependency, build seed, specification assumption or axiom.
Historical producer acceptance remains separate from the final producer review
and fixture refreeze.

## Pure Lean dependencies

`lean_dependencies` records Lake dependencies that contain no native code, so
they are not trusted externs, but whose behaviour IxCC relies on. Each
entry pins the Lake package and revision (`lake-manifest.json`), the flake
input with the same revision (Nix), the modules our sources import from it,
and the SHA-256 of every file of their import closure. The checker requires
every import of the project's sources that names neither a project module nor
a toolchain module to be such a recorded module; checks each closure file's
hash; rejects a closure file that declares a native symbol, uses
`implemented_by`, `axiom`, `sorry` or `native_decide`, or imports a module
outside the closure or the toolchain; and requires the Lake and flake pins to
agree.

The one entry, `ix-kernel-ixon-v4-codec`, is ix's `IxKernel/` package at
`f829b760`, of which IxCC imports `Ix.Ixon.Canonical` and
`Ix.Ixon.Codec` (an 11-module closure importing only `Init`; its public roots
use `propext` and `Quot.sound`). It is the ingress decoder and encoder.
The resource-selection checker also uses its pure framing operations on the
recheck path, with pure BLAKE3 for the effective profile's identity. The
rechecker receives the raw profile bytes and pair records and validates them
against its Src declarations; it does not trust an ix acceptance Boolean.
A codec defect can make ingress reject a closure or read a different program
than ix compiled, which `Recheck.run` then checks as given. No whole-kernel
semantic theorem follows from this codec dependency.
Nix packages the same 11 sources under the same package name with a codec-only
library (`nix/build.nix`), so the kernel is never built; the
`trusted-extern-ledger` check reads the pinned source (`ix-src`).

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

[E1](x86-encoded-instructions.md) proves every row of the x86 instruction
table: one declarative row supplies the typed semantics, the byte semantics
and the encoding, and a separate decoder finds rows through a kernel-checked
injective index. [E2](x86-stream-objects.md) now certifies complete
production text and independent ELF interpretation, and the N2 source
endpoint consumes actual object execution. The JSON retains stable boundary
identifiers and records exactly which portions are discharged.

Because the typed and byte machines share each row's semantic function, E1
no longer checks one semantics against another; a wrong semantic function or
opcode in a row would pass every proof. The required `x86-hardware` check
tests the table against the host processor. It enumerates `Op.rows` and runs
every generated case natively through
[`hw_diff_harness.c`](../fixtures/x86/hw_diff_harness.c): each non-control
row with each kind combination of its slots, addressing shapes, immediate
edges, shift counts, `div` scenarios, fused producer/consumer pairs,
branches after every producer form, all conditions and the control recipes,
53,279 cases in total. It compares exit, registers, model-defined flags,
changed memory and faults (memory faults as SIGSEGV or SIGBUS, `#DE` as
SIGFPE) with `ByteEval`, and requires LLVM's `llvm-mc` to decode each case to the same
instruction lengths, mnemonics and encodings. This is test evidence, not a
proof of faithfulness: operand values the generator does not reach and
flags the model leaves undefined are not compared. The Sail agreement (S2)
remains the proof route.

The backend gate `check-backend` links each object it emits with
[`backend_driver.c`](../fixtures/x86/backend_driver.c), an untrusted C
driver standing in for the runtime driver of note 04 §6: it maps a private
region (at the Lean test region's address for generated programs), sets up
the context block as `cx_init` would, calls the exported wrapper with
sentinels in the callee-saved registers, and prints `rax:rdx` and whether
the sentinels and `rsp` survived. It is integrity-pinned test code; no
production path depends on it.

The runtime driver of note 04 §6 is
[`runtime_driver.c`](../fixtures/x86/runtime_driver.c) (M1.F6), untrusted
and integrity-pinned. It links with an object compiled from `Rt.lower`'s
output, which exports `cx_init` and a SysV wrapper per root, maps a
private region (`--region`, default 64 MiB) and a separate stack for the
program (`--stack`, default 8 MiB, above a guard page), and for each input
stores `stack_budget` at `region + 16`, where every export wrapper reads it,
and calls `cx_init(region, size, stack_budget)` and the root, both on that
stack with sentinels in the callee-saved registers, printing `rax:rdx` and
whether the sentinels and `rsp` survived. Its contract: the region is
private, writable, untouched between `cx_init` and the root's return, and
disjoint from `.rodata` and the stack; `stack_budget` is the stack size less
4 KiB, which leaves room above the guard page for the wrapper frame and the
64-byte slack of the largest frameless leaf (so a deep recursion ends in
status 2, not a fault). In test mode it decodes the result with a C mirror
of `Rt.readback` and dumps the object area, and `tests-rt` checks the C
decoder against `Rt.readback` of the dump. `native_harness.c` stays only as
`check-x86-object`'s harness for the legacy `callRuntime` fixture (which
still needs its `ixcc_rt_allocate` stub) until `Instr.callRuntime`
retires.

`Recheck.Readback` adds bounded structural signature discovery for ground
first-order constructor results. Successful discovery certifies closed
indices and checked source-instance/emitted-layout provenance; its three
exact fences use only `propext`. It adds no source-typing or SrcEval adequacy
claim. `Rt.Rc.Layout` and `Rt.Rc.Readback` add ten header/observation fences
using the existing logical basis. Those header/readback laws are inputs to
the bounded recycling runtime below; neither extension adds a native
interface or changes this driver.

`Own.Plain` and `Own.Rc` add a conservative executable plain-RC checker and
abstract semantics. The checker binds the complete untrusted function map to
its canonical producer. The separate refinement and heap-shape proofs derive
full result values, exact ownership counts and final reclamation from concrete
input denotations, balanced counts and older-field ordering. Their public
theorems have exact fences in `OwnPlain` and `OwnRc`, with at most `propext`,
`Classical.choice` and `Quot.sound`. They add no axiom, native interface or
trusted allocator. The promoted `Cfg.Rc` and `Rt.Rc.Procs` path now composes
these invariants through actual initialization, allocation, count changes,
iterative release, source control/calls, layout and the existing backend.
`Recheck.RcReplay.run` checks the complete serialized ownership/backend
certificate and emits the actual public object. Its `sound` theorem retains
successful replay, `X86.Driver.Ok`, the source `GoesWrong` qualification and
SrcEval as semantic anchor, with complete constructor-tree observations.
The general source-adequacy and selected-producer obligations remain open.

The public `cx_drop` export receives the original owned result word unchanged
through its `.word` argument representation. `Returned.release_public` derives
release from the actual physical return invariant and restores allocator
readiness; successful readback alone is not ownership evidence. With zero
external owners, ordered-heap balance proves complete reclamation.
`recycled_entry` starts the next numeric root on that reached heap without
resetting bump/free-list history, and `drop_sim_linked` supplies the emitted
drop ABI simulation under the established `EntryBase` contract. These are
operation-composition results. They do not assert unconditional ownership for
every successful arbitrary `DriverSession`: source-stuck behavior remains
qualified, and general backend session iteration needs the whole-call budget
word frame as well.

The independent C harnesses
[`rc-runtime-driver.c`](../fixtures/x86/rc-runtime-driver.c) and
[`rc-reuse-driver.c`](../fixtures/x86/rc-reuse-driver.c) reuse the unchanged
runtime driver's trampoline and complete decoder. They are test evidence,
not allocator externs. The primitive harness writes synthetic fixture fields
to test exact procedure behavior; the reuse harness initializes once and
makes no allocator metadata writes afterward. The compiled gates preserve
4,393 primitive C assertions, 40 codec refusals, 15 complete-replay refusals,
25 standalone full-value checks and 168 same-arena calls/drops with 114,820
independent C assertions, full Lean readback and exact reclaimed-address sets.
The separately required `tests-cfg-rc` retains four complete abstract-Cfg
value/heap cases, bounded timeout checks and 12 bridge ownership/count controls;
its pure proof aggregate retains all 29 original marker/map/scope/bounds examples.
`tests-pipeline-rc` additionally compares complete values across actual RC
pipeline stages with independent list/pair formulas. Its allocation/inc/dec/free
counter is a test-side observer of production `Cfg.Rc.step`, differential-tested
against `Cfg.Rc.run`; it is neither a new trusted evaluator nor a native cost
theorem. The native modes retain independent C and Lean observations, reject
object-only text corruption before link even when its bundle is rehashed, and
exercise real-source root heap exhaustion separately from initializer refusal,
with successful same-code neighbors. Counts stop before caller output-drop;
physical reclamation remains covered by the existing native recycling gate.
These tests add no driver assumption, extern or trusted allocator.
The real-source fixture records its historical producer; final G1/producer
review and refreeze are still separate from these accepted local results.

**The driver model (specification assumption
`x86-phase1-runtime-driver-model`).** `Recheck.sound` and the bounded
`Recheck.RcReplay.sound` are theorems about
`X86.Linked` ([`Linked.lean`](../IxCC/X86/Linked.lean)): the
object's execution from a `X86.Driver`
([`Driver.lean`](../IxCC/X86/Driver.lean)) that calls `cx_init` and
then the root's export, each at the address `ELF.symbol?` finds for its
symbol in the parsed object, and observes the root's result by
`Rt.readback`. Reading it as a statement about the native executable
assumes that `runtime_driver.c` and the system linker set up those calls
as the model does:
- the text at `base`; one region of `size` bytes at `region`, its bytes
  before the first call arbitrary except the stack budget at
  `region + 16` (`ctx − 48`), which the driver stores before `cx_init`;
- the call stack (`budget + 56` bytes below `sp`, and the return slot)
  apart from the region;
- each call entered at its symbol's address with `rsp = sp`, the same
  return address outside the text, `rdi = region` and the arguments in
  `rsi`…`r9`, any other registers and flags, the root's call starting from
  the bytes `cx_init` left;
- the observation: status 0 and the value read back at the root's type
  over the region from `region + 16` with fuel `size / 8` (the C decoder
  reads only that part), other statuses the wrapper's resource failures;
  arguments of 2⁶⁴ or more cannot be passed.

The model maps only the region and the call stack. A real process maps
more, so the assumption includes that a run the model shows non-faulting
touches only modelled memory. `Driver.Ok`, the numeric contract, is a
hypothesis of the theorem, satisfiable for every accepted artifact
(`Recheck.driver_exists`), not part of this assumption. The reading also
rests on `x86-v0-local-semantics` and `x86-v0-elf-writer`.

The same specification entry records the distinct `X86.DriverSession`
protocol: initialize once; call a numeric root at exact arity; observe the
complete result while live; call `cx_drop` with that original raw word; then
continue from the released bytes, repeating only return-slot setup. The
existing `X86.Linked.call` theorem initializes per root call, so it is not
definitionally that session protocol. Native session evidence and the proved
release/reentry operations complement the single-call theorem without adding
a trusted allocator, new extern or Lean axiom.

The benchmark runner's entry profile
([`benchmarks/runner/entry/`](../benchmarks/runner/entry/): the timing
driver, one adapter per row, and tagged C twins of `ackermann`, `tak`,
`collatz`, `prime-count`, `even-odd` and `sfib`)
is untrusted measurement code, integrity-pinned so that a change to how a
row is built or timed is reviewed with the ledger. Its ixcc adapter
stores the stack budget at `region + 16` as the runtime driver does, calls
`cx_init` once and then the root's SysV wrapper directly, under the
runtime driver's contract (a private region untouched by C, a stack budget
that leaves at least 1 MiB below the thread's stack limit); it checks the
status and the Nat tag of every result. No check, proof or production
artifact depends on these files, and the runner is outside the root flake.

The [indexed stream checker](stream-checking.md) preserves this boundary:
bounded decoding and cached canonical positions are proved exactly equal
to the original decoder and stream checker on all inputs. Production
emission and relocation validation use the same `Stream.Valid` certificate.
Four additional public fences retain the ordinary logical axiom basis.

| Boundary | Current scope | Evidence and remaining work |
| --- | --- | --- |
| Local ISA semantics | Agreement of the local byte machine with actual x86-64, including canonical addresses, unified code fetch, memory permissions, flags, faults, and the caller ABI. Compiler-contract traps must be proved unreachable; they are not hardware exceptions. | E1 and E2 prove local-to-local agreement. The [S0 readiness decision](x86-reference-model.md) pins the Sail snapshot; reference execution comparison, the Lean adapter, and S2 agreement remain pending. |
| Encoder stream/layout | Discharged for successful certified production emission. Raw `Encode.encode`/`Program.encode` clients must validate their output or prove the same facts. | `Stream.check_sound` checks every boundary, canonical position, target and relocation. Complete-stream proofs cover call-free execution and internal calls under concrete `SafeTrace` conditions, including residual return-slot bytes. `ELFLink` proves checked PC32 application and runtime CALL transfer. External procedure bodies still require their semantic/ABI contracts. |
| Runtime driver model | `X86.Driver`/`X86.Linked` model initialization and the root call for accepted scalar and bounded RC objects. The same entry describes `DriverSession`'s separate owned raw-word drop protocol; it does not upgrade the one-call theorem to arbitrary-session adequacy. | Existing pipeline gates plus `tests-rt-rc`, `tests-rc-certificate` and `tests-driver-session` check complete values, ABI, reclamation and same-region reuse. Process start/linker correspondence, source adequacy and general whole-call session framing remain explicit. |
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
branch objects, 15 stream corruptions, 1,002 object mutations/truncations,
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
| Lean 4.34.1 seed/runtime | Elaborates, kernel-checks, compiles, executes `#guard`s, and hosts compiled tests | Gen-1 self-host plus address-exact diverse double compilation; production checking moves to the public lean4ix/ix verified checker |
| GMP 6.3.0 | Lean runtime arbitrary-precision arithmetic; direct Nix build input | Verified limb bignums refining `Nat`/`Int`, compiled by IxCC |
| Host C ABI/runtime | glibc 2.40-66 on the x86_64-linux baseline, plus compiler runtime; hosts Lean/Rust and the native x86 test harness | Gen 1 removes upstream runtime; allocator/memcpy and libc surface retire to verified `.ix` code plus a syscall model |
| Locked Nix supply chain | nixpkgs, lean4-nix, flake-parts, crane, fenix/Rust, host C compiler/linker, GNU binutils readelf/objdump, rsync, binary substitution | Locked hashes now; later diverse reproduction and address-exact output comparison remove it from the semantic TCB |

The recorded GMP/glibc versions describe the inspected x86_64-linux closure.
Other configured systems use their corresponding locked Nix platform closure;
the ledger does not claim that Darwin uses glibc.

## Known limitations

- BLAKE3 has conformance tests, not a refinement proof or collision-resistance
  formalization. Address-identity theorems expose the required pairwise
  no-collision condition as a premise rather than hiding it in the TCB.
- The ledger covers the current Gen-0 repository/build closure. Future libc,
  IO, store, thread, float, or syscall primitives are unapproved until added
  per symbol/address.
- “Empty ledger” means no persistent target/runtime extern assumptions. Seed
  provenance and independently reproducible build attestation remain separate
  bootstrap obligations.
