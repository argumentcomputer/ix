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

## Active target specification assumptions: x86-64 v0

| Boundary | Current assumption | Evidence | Retirement |
| --- | --- | --- | --- |
| Local typed semantics | Under compiler ABI invariants, the closed sequential v0 model agrees with x86-64 for its modeled registers, canonical permissioned little-endian memory addresses, stack/call behavior, local compare-branches, and architectural faults. Its symbolic PC token is not yet a byte RIP; top-level return is a harness halt. Misalignment, stack-mismatch, corrupt-return, and callee-saved-clobber outcomes are compiler-contract failures, not claimed hardware exceptions. | Typed exclusion theorem and axiom fence; executable arithmetic, memory, stack/spill, direct-call, ABI, runtime-call, mapping-fault, and alignment fixtures; plus the kernel-checked `selectScalarMoveRefines` validator-to-selector bridge, whose leaf preserves arbitrary input `rsp`; [Intel SDM version 092](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html) and [AMD64 APM Volume 3 revision 3.37](https://docs.amd.com/v/u/en-US/24594_3.37) as reviewed references. | ISA stage S2 proves per-form decode/execution equivalence to the pinned upstream reference, including RIP, canonical-address checks, flags, memory, faults, and harness observation; selector/ABI proofs make contract traps unreachable. |
| E0 encoder | Each total encoder case emits the intended instruction; rel32 block patches are relative to the following instruction; runtime calls carry PC32 relocation records with addend -4. | Byte-exact Lean goldens plus integrity-pinned `scripts/CheckX86Encoder.lean`, decoded independently by GNU objdump from locked nixpkgs. | E1/E2 prove per-form encoding and complete stream/relocation agreement. |
| ELF64 object writer | The serialized ET_REL/EM_X86_64 headers, sections, symbols, PC32 relocations, non-executable-stack marker, and mandatory provenance note have the intended System V linker interpretation. | Lean structural guards; deterministic duplicate generation; GNU readelf/objdump inspection; and, on x86_64-linux, warning-fatal host link plus native execution of seven fixtures. Three cases compile synthetic Ixon through the actual validated pipeline and selector: zero, 42, and UInt64 max. They compare every intermediate scalar observation, fresh-process object bytes, frozen source/IR₁ address roots, and the actual IxIR₁-policy provenance note; overflow must fail before writing an object. The reviewed formats are the [generic ABI ELF specification](https://gabi.xinuos.com/elf.pdf) and [x86-64 psABI](https://refspecs.linuxfoundation.org/elf/x86_64-SysV-psABI.pdf). | E2 proves serialization and linker-input interpretation, including relocation resolution, exported entry placement, and the provenance commitment. |

The syntax, local semantics, scalar selector, E0 encoder, and object writer are
mechanically separated in `Compilatrix/X86/Basic.lean`, `Eval.lean`,
`Select.lean`, `Encode.lean`, and `ELF.lean`; neither selection nor encoding can
inject a raw byte instruction into the typed AST. The AST
has no constructors for scalar hardware division, floating point, SIMD,
atomics, indirect calls, raw syscalls, or TLS. It also excludes the x86
high-byte register ambiguity, `rsp` as a SIB index, and the unavailable
two-operand byte `imul` form. `Program.inV0` proves this containment for every
typed program without an ISA axiom.

These entries are candid staging boundaries, not completed verification
claims. No existing IxIR₂ compiler theorem depends on encoded bytes, and no
native correctness theorem yet relates the local symbolic PC to final byte
addresses. The first native wedge must carry all three assumptions until the
corresponding bridge theorem retires them.

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
