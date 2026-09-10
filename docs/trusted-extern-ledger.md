# Trusted-extern ledger

Last reviewed: 2026-09-06. The machine-readable ledger is
[`trusted-externs.json`](trusted-externs.json); `nix flake check` validates
it with [`scripts/CheckTrustedExterns.lean`](../scripts/CheckTrustedExterns.lean).

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
the pinned Lake TOML parser and GNU `sha256sum`; the independent encoder,
object, and [source-coverage](source-coverage.md) checks invoke GNU binutils
and, on x86-64 Linux, the existing native C harness. These remain seed/build
tools and introduce no project native interface or proof axiom. The
support modules, executable scripts, native harness, and source matrices
have reviewed integrity pins.

C3's [upstream native gate](source-native-upstream.md) adds independent residual
text/ELF reconstruction and closed Nat source/physical/object observations. Its
execution theorem requires an explicit supplied-state call/stack certificate;
the general N3/F1 contracts and reference ISA/loader assumptions remain open.
The six new axiom fences introduce no new axiom or production foreign symbol.
The ledger also pins the benchmark adapters, runner/checkers, manifest, and
comparison toolchains. Clock, allocation, GC, process-memory, compiler, and
runtime observations are recorded as measurement/build trust, separate from
production source/compiler proof assumptions.

The [source-recursion checker](../scripts/CheckSourceRecursion.lean) imports
only the shared check helpers. It compares two fresh compiler processes,
checks the reviewed eight-case matrix and HPT identities, verifies common
lowering/sidecar links, and independently checks terminal allocation balances,
reclaimed heaps, and comparative physical allocation/free laws and RC/peak
bounds in both phases. It rejects RC and peak-counter corruption that preserves
all earlier allocation/free checks. It adds no external oracle. D1's five,
D2's seven, R2's nine, R3's twelve, and R4's seventeen theorem fences retain the
ordinary Lean basis and the existing BLAKE3 assumption at the addressed
wrapper, composed physical, shared-resource, and comparative boundaries;
neither the native-interface inventory nor the three
specification assumptions changes.

The [source-call-reuse checker](../scripts/CheckSourceCallReuse.lean) adds the
reviewed nine-map and 35 policy/rejection matrix, complete fresh-process
artifacts, and independent reservation, allocation, reclamation, and RC/peak
checks for all selected prefixes. Seven deliberate corruptions exercise the
policy, reservation, and cost checks. It imports only shared check helpers;
its source and reviewed report are integrity-pinned. R5 adds 25 theorem fences
for explicit v0/v1 policy behavior, suspended credit ownership, actual compiler
simulation, checked source-map specialization, and composed source/resource/
cost endpoints. Their axiom sets retain the ordinary Lean basis and the
existing addressed-BLAKE3 exception. The new provenance hashes canonical
IxIR₁-plus-policy metadata; diagnostic IxIR₂ JSON has no wire or cache role.
The native and specification-assumption inventories remain unchanged.

The [source-unique-reuse checker](../scripts/CheckSourceUniqueReuse.lean)
reconstructs canonical source, recursor-mode, IxIR₁ graph, and policy preimages
using only shared check helpers and the existing BLAKE3 binding. It checks all
seven fresh-process cases, full constructor identity and unit unique ownership,
every reservation prefix, exact no-RC costs, and complete release. Forty-three
source/boundary checks and twelve deliberate artifact corruptions accompany
the reviewed report. Its source and report are integrity-pinned. Twenty-four
new theorem fences cover the checked source specialization, consuming emission,
actual target steps, all-prefix resources, full reclamation, comparative costs,
and composed source endpoint. They retain the ordinary Lean axiom basis and
the existing BLAKE3 assumption; no native interface or specification assumption
is added. The new provenance remains an IxIR₁-plus-policy identity.

`lake exe check-tools-tests` exercises the auditor on isolated temporary
copies. It checks source literals/comments, unrecognized extern attributes,
new executable roots, project/dependency extern drift, imports and native
entry points, integrity changes, malformed/duplicate Cargo metadata, and CI
action drift. The Nix trust-ledger check runs these regressions too.

## Active native interface: BLAKE3 Rust

| Field | Ledger value |
| --- | --- |
| Owner | Compilatr.ix maintainers |
| Project entry point | `Blake3.Rust.hash` in `Compilatrix/Ixon/Hash.lean` |
| Assumed semantics | Standard BLAKE3 XOF over exactly the input bytes; a 32-byte request is the standard 256-bit digest |
| Logical/proof status | Assumption: no Lean refinement theorem currently connects returned bytes to a pure BLAKE3 specification. Canonical-address identity is conditional on an explicit pairwise `Address.Blake3NoCollision` premise; no global hash-injectivity axiom is asserted. Generic evaluator readdressing, HPT evaluator and case-binder-field concretization, owner-sensitive case pruning, exact scalar fetch forwarding, local PAP/application refinement, and the rooted-restriction fuel induction are hash-independent and stay in the ordinary logical axiom set. Production addressed-lowering corollaries, checked HPT cache/summary/consumer results, and the public reachability theorems that validate an exact input digest consume native hashes, so `Compilatrix/Fence.lean` pins their exact additional `Blake3.HasherOps.hash._native.native_decide.ax_1✝` dependency. |
| Evidence | Official empty-input vector, output length, determinism/input-sensitivity checks, a full constant-address fixture, complete IxIR₀/IxIR₁ declaration byte+address fixtures, frozen dependency-chain/nested-lambda/constructor-wrapper readdressing digests, executable semantic audits, a protected-source-identity collision regression, the frozen ledger-oracle cyclic block/member digests, and five version-3 HPT cache keys plus five checked recursively field-aware summary addresses exercised through deterministic production, persistent canonical record/store ingress, record-streamed filesystem parity with the pure codec, malformed-stream rejection, dependency-cone rebuilding, file-backed corruption recovery, depth-two fetch/case refinement, checked case-binder field recovery through the ordinary checker and deterministic producer, checked finite-constructor case pruning, PAP fusion across all saturation classes, exact scalar fetch forwarding after allocation and reuse, and checked rooted declaration/SCC removal with exported-root and dynamic-apply fallbacks through deterministic one-rebuild regressions in `Tests.lean` |
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

The proof fence separates the semantic transport from this boundary. Generic
`Readdress.evalTransportAt` and `Readdress.runMain_mapAddresses` depend only on
the ordinary logical axioms. The indexed production theorems for protected
source identities, exact runs, addressed forward simulation, all three dynamic
error exclusions, and cost counters additionally expose the native hash axiom
above because their premise is an actual successful production post-pass. This
is a mechanically checked trust effect, not an implicit claim that BLAKE3 has
been verified in Lean.

The HPT certificate checker uses two additional versioned native-digest
domains for cache-query and summary identities. The current `/3` domains are
the explicit address roll for recursively nested field facts; earlier digest
domains are not reinterpreted. Persistent artifact records and sorted store
containers have separate, independently versioned
`hpt-cache-record/2` and `hpt-cache-store/1` framing domains. Success theorems
expose the candidate post-fixpoint gate, exact
returned content-address audit, and accepted-row evaluator soundness; their
axiom cones are pinned beside the addressed-lowering cones. The generic
evaluator concretization itself remains inside the ordinary logical axiom set,
while composing it with a successfully materialized certificate exposes the
native hash axiom. The five-key and five-summary frozen fixture includes a
genuine recursive SCC and verifies that widening one leaf changes its summary
and dependent query while leaving an unrelated detailed-constructor summary
unchanged. Its allocation→fetch branch checks a scalar field fact against
concrete storage and projection. A separate depth-two fixture checks recursive
allocation, double fetch, nested cases, exact/one-below depth limits, cache
codec roundtrips, and conservative shallow-budget production. Case transfer
filters matching constructors by
tag and exact arity, reverses source-order fields into evaluator binder order,
joins matching alternatives pointwise, widens identity-only and unknown
matches, and recovers Nat-successor predecessors as scalar. The constructor
and Nat case-binder concretization lemmas remain in the ordinary logical axiom
set; the recursive field order and root/field conversion lemmas are likewise
pinned separately. A dedicated checker/producer regression covers
precise and multi-shape fields, wrong-tag filtering, widening, alias-forgotten
fields, Nat peeling, and the concrete projected result. A separate alias/reuse
regression rejects a stale exact-constructor claim and observes the
conservatively accepted concrete result. The deterministic SCC-local producer
remains outside this boundary:
its returned `Production` stores proof that the ordinary checker accepted the
exact candidate/result pair. Precision, repeatability, exact and one-below
round/field/depth limits, and independent shape/field-budget fallbacks are
compiled tests; the post-fixpoint, audit, and evaluator projections from `Production`
are axiom-fenced with the same native exception. The persistent scheduler's
`Cache.Production` stores the same ordinary-checker equality, and all three
projections plus the pipeline corollary are separately fenced. Canonical
record/store roundtrips, cold/warm schedules, malformed-record repair,
dependency-cone rekeying, duplicate/noncanonical/outer corruption rejection,
exact cache budgets, record-streamed pure-codec parity and malformed framing
rejection, metadata-indexed lazy chunk reads, stale-corruption isolation,
selected-chunk repair, power-loss-durable sibling staging, ignored orphan
transactions, and temporary-file/directory ingress are compiled tests. The first
consumer's one-root, recursive, and self-call-aware main local-post-fixpoint
theorems likewise stay in the ordinary axiom set, while their checked,
directly produced, and cached pipeline specializations expose exactly the same
native digest exception. Its compiled precise/top fixtures remove one root
branch and two branches nested across separate alternative bodies, preserve
concrete execution, and confirm that an accepted universal row does not prune;
a terminating Nat-peeling fixture reaches its rewritten base case through
three dynamic self calls. A checked artifact-main fixture also crosses the
pipeline API and preserves the exact finite-fuel self-loop result.

The rooted-reachability checker adds the
`compilatrix/ixir1/reachability-input/1\0` domain for the exact rewritten
declaration rows and main. Its evaluator restriction induction does not reason
about hashes, but the public `runMain_filterEntries_eq_of_validate` and
`runMain_run_eq` theorem cones unfold the digest-bearing validation boundary
and therefore expose the same native hash axiom. Both are pinned in the proof
fence. Compiled fixtures remove a dead two-function SCC, retain it through an
exported member root, follow direct-call and PAP edges, reject stale and
non-closed certificates, preserve execution through the one rebuild, and
retain the complete declaration set around reachable dynamic apply. A separate
usage-checked Ixon compilation fixture removes five of six emitted stored
functions while preserving its exact shared constructor result.

The fail-soft O1 outcome now composes with the validated compilation semantic
spine. Its produced and cached successful-run/reclamation wrappers, and the
produced artifact's forward simulation, progress, memory-error exclusion,
reclamation, and allocation/free endpoints, are pinned in
`Compilatrix/Fence.lean`. Each cone exposes the ordinary logical axioms plus
the same native BLAKE3 exception already required by checked HPT production
and the final content-address rebuild; the attachment introduces no new
trusted primitive.

## Active native interface: durable filesystem synchronization

| Field | Ledger value |
| --- | --- |
| Owner | Compilatr.ix maintainers |
| Project entry points | `Compilatrix.DurableSync.file` and `.directory`, used only by `IxIR1.HPT.CacheIO`, `IxIR1.HPT.CacheDirIO`, and compiled boundary tests |
| Assumed semantics | On the x86_64-linux baseline, successful type-checked `fsync` calls make the regular staged file or directory-entry set stable according to the kernel/filesystem/device contract. Apple regular files request `F_FULLFSYNC` first and fall back to `fsync` only when unsupported; Apple directories use `fsync` |
| Logical/proof status | Operational availability/durability boundary only. Cache bytes still cross bounded decoding, address checks, and the ordinary HPT certificate checker; no theorem assumes the barrier's result |
| Evidence | Exact Lean-extern and C-export inventories, pinned C-source SHA-256, traced Lake object build, compiled successful file/directory calls, wrong-kind rejection, byte-exact snapshot replacement, independently durable chunk repair, and transaction cleanup |
| Retirement | An upstream durable Lean filesystem API or the verified runtime/syscall boundary, preserving the same staged-file/rename/directory ordering and passing controlled power-cut recovery tests |

Lean's portable filesystem API exposes buffered handle flush but no stable-file
or directory-entry barrier. `native/hpt_cache_sync.c` is therefore a narrow
two-symbol boundary. It retries interrupted opens and synchronization calls,
rejects symlinks and wrong file kinds, propagates synchronization and close
errors through Lean `IO.Error`, and contains no cache parsing or path-selection
policy.

`HPTCacheIO` first streams and verifies the staged cache, synchronizes that
regular file and its transaction directory, atomically renames it into the
destination parent, synchronizes the destination and source directories,
removes the empty transaction directory, and synchronizes the parent again.
`HPTCacheDirIO` reuses the exact protocol for each rebuilt singleton chunk and
also synchronizes a newly created cache directory and its parent before use.
On a synchronization failure after rename, the new destination may already be
visible, but the API returns an error and makes no false durable-commit claim.
The old-or-new atomicity and persistence statement remains conditional on the
filesystem and hardware honoring their successful barrier results; controlled
power-cut testing is still desirable platform evidence.

Schema 2 of the JSON ledger distinguishes this project-owned interface from
dependency-owned BLAKE3. The checker requires exact equality for the complete
local Lean `@[extern]` inventory and the C `LEAN_EXPORT` inventory, derives the
C source set from the integrity-pinned Lake configuration, and checks the
source hash. A dependency symbol can therefore no longer accidentally cover an
unreviewed local extern with the same foreign name.

## Target specification boundaries: x86-64 v0

[E1](x86-encoded-instructions.md) proves every emitted local instruction
form. [E2](x86-stream-objects.md) now certifies complete production text and
independent ELF interpretation, and the N2 source endpoint consumes actual
object execution. The JSON retains stable boundary identifiers and records
exactly which portions are discharged.

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
| Lean 4.33.0 seed/runtime | Elaborates, kernel-checks, compiles, executes `#guard`s, and hosts compiled tests | Gen-1 self-host plus address-exact diverse double compilation; production checking moves to the public lean4ix/ix verified checker |
| GMP 6.3.0 | Lean runtime arbitrary-precision arithmetic; direct Nix build input | Verified limb bignums refining `Nat`/`Int`, compiled in the no-runtime fragment after M3 |
| Host C ABI/runtime | glibc 2.40-66 on the x86_64-linux baseline, plus compiler runtime; hosts Lean/Rust and implements the ledgered `open`/`fstat`/`fsync`/`close` durability shim | Gen 1 removes upstream runtime; allocator/memcpy and libc surface retire to verified `.ix` code plus a syscall model |
| Locked Nix supply chain | nixpkgs, lean4-nix, flake-parts, crane, fenix/Rust, host C compiler/linker, GNU binutils readelf/objdump, rsync, binary substitution | Locked hashes now; later diverse reproduction and address-exact output comparison remove it from the semantic TCB |
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
- The Ixon→IxIR₀ erasure fixture configures a two-argument source axiom
  and target extern that both return literal `42` on the pinned arguments.

Neither is linked foreign code or production-approved. They test the formal
hook through which a future per-address ledger entry will connect to the IR.
The IxIR₀ model now has an exact address-adapter proof:
`Readdress.Oracle.Readdressable.examples_of_run_eq_ok` derives its coherence
from the successful whole-program audit's bidirectional isolation of reserved,
stable, and declaration/main external identities. The compiled
`ReaddressOracleFixtures.ledgerCycleOk` fixture pins a genuine mutual block and
both member digests, calls the modeled extern, and returns literal `42` before
and after readdressing. `mainExternalCaptureRejected` separately ensures an
external identity mentioned only by main cannot be captured by a derived
member key. These theorem cones are pinned in `Compilatrix/Fence.lean`.

IxIR₁ extern declarations keep explicit identity entries in `ReaddressAll`;
direct undeclared extern references are outside the producer map. Its Nat-add
fixture therefore uses the generic oracle-pullback transport without an
address-specific adapter instance. The JSON ledger records these two distinct
coherence statuses and the checker requires status and evidence for every
modeled oracle.

Erasure may represent explicitly configured source opaque/partial/axiom
declarations as `IxIR0.Decl.extern`. The proof-producing validator checks the
resolved kind, configured source arity, and exact target declaration, while
the simulation theorem separately requires `OracleRelAt` for each configured
address. Lowering or structurally certifying a declaration does **not**
authorize an implementation. Production execution still requires a
per-address ledger entry and its source/target oracle correspondence proof;
the composed pipeline currently supplies no such extern configuration.

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

## Bounded native unique reversal

The checked native selector and its byte-memory proof add no native interface
or axiom. Nine new fences cover little-endian memory, the complete emitted
main/release runs, finite owned graphs, source/value/cost composition, concrete
witnesses, and prefix trap exclusion. The memory/execution proof uses ordinary
logical axioms; indexed source statements retain the existing addressed-artifact
BLAKE3 dependency.

The source-native-unique gate independently checks eight source-produced ELF
pairs and linked C runs, with exact graph/ABI/role provenance, arena-cell counts,
full reclamation, and twelve native corruption regressions. Its checker,
shared source-checking helper, native C harness, and reviewed matrix have
integrity pins. The C code is a test harness that provisions the arena and
checks generated code; it is not a new Lean FFI or semantic oracle. The existing
ISA and system linker/loader assumptions remain active; E2 now certifies
production text and independent ELF interpretation.

## Native runtime input

The [N2 endpoint](source-native-runtime.md) compiles a parameterized source
function and selects one reversal/release pair for all admitted runtime lists.
Sixteen fences cover source application, physical execution, canonical input,
native validation/execution, prefix trap exclusion, unchanged-memory length and
capacity rejection, cross-layer costs, and exact Nat-to-Word conversion. Native
memory/execution proofs retain only ordinary logical axioms; addressed source
certificates retain the existing BLAKE3 dependency. The efficient input-word
builder is definitionally equal to the original allocation update.

The independent runtime gate reconstructs function/ABI/policy preimages,
compares two complete fresh artifact sets, decodes one ELF pair, and links it
once for eight inputs in one process. It checks full release and 203 malformed
calls without arena writes, plus 20 artifact/observation corruption regressions
for each of the baseline and checked counter-folding variants. Its checker,
native harness, and both reviewed reports are integrity-pinned. Counter folding
adds complete-state equality, body execution and instruction-count fences using
the existing logical axioms; source-to-object composition retains its existing
hash dependency. It introduces no FFI or new runtime/ISA assumption. The
test harness provisions caller input; it is not a new Lean FFI or modeled
oracle. [E2](x86-stream-objects.md) now composes the source theorem through
actual object text, including parsed provenance, physical returns and complete
reclamation. Reference-ISA agreement and system linker/loader assumptions
remain under the scoped specification entries above.

## Closed borrowed calls

[B1](source-borrow.md) adds no FFI, modeled oracle, target runtime, or axiom.
Six core fences for reconstructed CFG validation, actual finite execution,
result/resource agreement, and fallback use `propext` and `Quot.sound`.
Four indexed source fences retain the existing logical and BLAKE3 basis.
The semantic selector derives bounded source and physical replay certificates
internally; it does not assume an unproved open-function simulation.

The independent source-borrow gate reconstructs all changed functions and
owned wrappers and replays complete physical traces using its own small
interpreter. It verifies eighteen source cases, three checked source
fallbacks, twelve ownership/resource negatives, and thirteen corruptions.
The checker, its two helpers, and the source-root matrix are integrity-pinned.
Internal borrowed labels are collision-checked transient names, not a new
content-addressed IxIR₂ format. The family is not natively selectable, so no
ISA, encoder, ELF, or native runtime assumption is widened by this package.

## Borrowed runtime arguments

[B2](source-borrow-runtime.md) adds fifteen fences. Ten core/source-shape/input
interfaces use only the existing logical axioms; five indexed source selection
and preservation interfaces also retain the existing BLAKE3 dependency.
Structural checking derives source application and function/continuation
simulation for every admitted runtime heap. Release fuel comes from proved
root ownership and allocation order. No input replay, new native reflection
axiom, FFI, oracle, or target runtime is introduced.

The independent runtime-borrow gate checks nine compiled source functions,
144 direct/PAP comparisons, nine aliased lenders, complete fresh artifact
agreement, four checked fallback policies, and twenty rejected corruptions.
Its script, new helper, and reviewed source/export matrix are integrity-pinned.
The shared execution helper's reviewed pin changes to admit explicit initial
caller heaps; B1 retains its empty-main wrapper and regression gate. The same
native selector rejects both shared artifacts, so all ISA, encoder, and object
assumptions retain their previous scope.
