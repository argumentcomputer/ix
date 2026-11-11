# Trusted-extern ledger

The machine-readable ledger is
[`trusted-externs.json`](trusted-externs.json); the `ixcc-trusted-extern-ledger`
check of ix's flake validates it with
[`IxCCTests/Scripts/CheckTrustedExterns.lean`](../IxCCTests/Scripts/CheckTrustedExterns.lean).

**Status, 2026-09-29.** The inventory was reset for the rebuilt compiler.
Removed with the legacy pipeline: the durable-filesystem native interface,
the IxIR and Ixby specification assumptions, the modeled IxIR oracles, the
hosted CI actions and runner, and the comparison-runtime pins. All remain
on branch `jcb/ixby-archive` of the pre-merge `argumentcomputer/Compilatr.ix` repository.
`nix flake check` runs the audit again.

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
- declaration-level `axiom`, standalone `sorry`, and every spelling of native
  evaluation the lexer can see in the checked project sources and the pure
  Lean dependency's closure: `native_decide`, `decide +native` (also after
  other flags, as in `decide +kernel +native`), a configuration field
  `native := true` (`decide (config := { native := true })`), and the names
  `ofReduceBool`, `ofReduceNat`, `trustCompiler` (bare or under `Lean.`) and
  `Lean.reduceBool`/`Lean.reduceNat`. A conservative lexer excludes comments
  and literals and retains line locations. The bare names `reduceBool` and
  `reduceNat` are accepted, because the erased checker's primitive table uses
  them as field names, and so is a variable or field named `native` in any
  other position. The one native axiom the fences permit, Blake3's
  `native_decide`, is inside the Blake3 package, which this scan does not
  read (its externs are inventoried instead);
- every `@[csimp]` theorem (and `attribute [csimp]` command) in the project's
  audited sources and in each pure Lean dependency's closure: each must be
  stated as `: @f = @g :=` and listed with its file and replacement pair
  (`csimp_theorems`, top level and per dependency), since it changes the code
  compiled for every call of `f`;
- every package/version and the complete checksum-bearing Cargo lockfile;
- the integrity pins (below): the SHA-256 of every file the integrity rule
  covers, among them IxCC's build-selection files (`lakefile.lean`,
  `lake-manifest.json`, `lean-toolchain`, `nix/*`), its checkers, scripts and
  native harnesses and its fixtures, and of the repository files listed in
  `integrity.repository_files` (`.github/workflows/ixcc.yml`);
- the revision of every locked Nix flake node of the repository's
  `flake.lock`, and, inside a larger repository, that the repository's
  `lean-toolchain` (whose Lean ix's flake builds IxCC with) equals IxCC's;
- the required-check inventory (below): the attributes of `nix/checks.nix`
  against `required_checks`;
- every `uses:` reference in the CI workflows in scope (below), followed
  through the repository's own local actions and reusable workflows
  (`./path` or `$/path`, which must stay inside the repository): a remote
  reference not pinned to a full 40-hex commit is rejected outright, and the
  pinned inventory must match the ledger.

ix's `flake.nix` is not pinned. It selects the toolchain (the repository's
`lean-toolchain`, checked above), passes ix's Blake3 build (its `blake3` and
`blake3-lean` nodes are pinned in `flake.lock`, and the Blake3 entry below
ties them to the Lake pin) and exposes `nix/checks.nix`'s checks as
`ixcc-*`. What it exposes is checked by `ixcc.yml` (below), not by this
audit.

### Integrity pins

`integrity.rule` states which project files are pinned, and the audit fails
unless `integrity.tracked_files` pins exactly those: a covered file without a
pin fails, and so does a pin of a file the rule does not cover. A file is
covered when its path relative to `IxCC/` matches an `include` glob and no
`exclude` glob (`*` within a path segment, `**` for any number of segments);
hidden files and directories (`.gitignore`, `.lake`) are never covered. The
rule covers everything that can change what a check builds, runs or compares
against:

- the Lake and toolchain files (`lakefile.lean`, `lake-manifest.json`,
  `lean-toolchain`) and the root modules `IxCC.lean`, `IxCCTests.lean` and
  `IxCCGrounding.lean`;
- every file under `IxCCGrounding/` (the grounding library: its laws,
  relation, lemmas, check and axiom fence);
- every file under `IxCC/` (the production library, the repository checkers
  in `IxCC/Tools` and the vendored Aiur reference), `IxCCTests/` (tests,
  fences, executable scripts such as `Scripts/X86ObjectFixture.lean` and
  `Scripts/Census.lean`), `fixtures/` (closures, catalogs, goldens, and the C test
  harnesses such as `fixtures/x86/exports_harness.c` and
  `unwind_harness.c`), `nix/` and `tools/`;
- the benchmark runner's C entry points (`benchmarks/runner/entry/*.c`) and
  `benchmarks/toolchains.json`, and the specifications the Aiur checks and the
  Ixon boundary cite (`docs/aiur-*.md` other than `aiur-backend.md`,
  `docs/ixon-v4.md`, `docs/x86-reference-model.json`);
- except anything under a `target/` directory (Cargo output of the manual
  reference tools).

Not pinned: the rest of `docs/` (including this ledger, `trusted-externs.json`),
`README.md`, `AGENTS.md`, `.gitignore`, and the rest of `benchmarks/` (the
optional measurement package, its fixtures and records). These describe or
measure; no required check reads them. Also not pinned: `lib/`, the Lean
source that programs are compiled *with* (`lib/IxccExe.lean`, the numeric
state machines' parsing and rendering). It is not IxCC and not trusted: IxCC
compiles it like the rest of a program, so the compiler's theorem covers it.
What the gates compile is its copy at the head of
`fixtures/corpus/phase1-machines/src/Machines.lean`, which the rule pins, and
`tests-exe` requires the two to be equal byte for byte. No Lake target, Nix
source set or module manifest takes `lib/` as an IxCC module (nothing imports
it).

`integrity.repository_files` pins files of the enclosing repository by path
relative to its root. Every configured workflow file must be listed, so
inside ix `.github/workflows/ixcc.yml` is pinned in full, not only its
`uses:` lines.

### Required checks

`required_checks` lists IxCC's required checks: exactly the attribute names
`nix/checks.nix` binds in its attribute sets (a lexer for that file's form
reads them, and refuses a binding it cannot account for). ix's flake exposes
each as `ixcc-<name>`, and `.github/workflows/ixcc.yml` builds the flake's
evaluated `ixcc-*` checks only if they are exactly `required_checks` with that
prefix. So dropping or adding a check in `nix/checks.nix` fails this audit,
dropping one in ix's `flake.nix` fails `ixcc.yml`, and narrowing what
`ixcc.yml` runs changes its pinned hash. What remains outside: an edit to
`ixcc.yml` that also stops it running `ixcc-trusted-extern-ledger` is caught
only by review of that file, which the ledger's pin makes a ledger change,
and CI Jobs' and Merge tests' calls of `ixcc.yml` are ix's and unaudited.

Standalone, the project is its repository: its `flake.lock` and
`.github/workflows` are checked. Inside a larger repository, the optional
`policy.repository` object names it: `root` is the repository root relative to
the project (`..` for `ix/IxCC`), whose `flake.lock` is checked, and
`workflows` (repository-relative files or directories, default
`.github/workflows`) scopes the workflows whose actions this ledger
inventories. `check-trusted-externs --repository-root DIR --flake-lock FILE`
overrides both, for a copy of the project taken out of its repository.

Inside ix the ledger names the repository (`root: ".."`), so ix's
`flake.lock` is checked, and scopes the workflow audit to
`.github/workflows/ixcc.yml`, the reusable workflow that runs IxCC's checks
and that IxCC owns; its three remote actions are pinned and listed in
`ci_actions`, and its full text is pinned in `integrity.repository_files`.
ix's other workflows, including the jobs that call `ixcc.yml`, are outside
the scope: they track `argumentcomputer/ci-workflows@main` and
`argumentcomputer/lean-update@dev` by branch, by ix's choice, which this audit
would reject. A change to `flake.lock` (for example a toolchain or
`lean4-nix` update) fails the audit until the node inventory is reviewed here.
The Nix check runs on a copy of the workspace that keeps this layout
(`nix/sources.nix`, `ledgerWorkspace`: IxCC, the codec closure, the
repository's `flake.lock` and `lean-toolchain`, the scoped workflows and the
pinned repository files).

Updating a dependency therefore requires reviewing and updating this ledger,
not merely refreshing a lockfile. An entry may only be removed when its exit
criteria are met and the coverage check confirms that its boundary vanished.

### Routine updates

ix's update automation changes pinned inputs, so each such pull request fails
`ixcc-trusted-extern-ledger` until the ledger is updated in the same pull
request:

| Update | What changes | Ledger fields |
| --- | --- | --- |
| `update-rust.yml` (weekly Rust toolchain; runs `nix flake update`) | `flake.lock` revisions; ix's `flake.nix` (not pinned) | `integrity.flake_nodes`; `seed_and_build_trust` `gmp-seed.version` by hand if nixpkgs' GMP moved (the Nix check passes Nix's GMP version) |
| `update.yml` (Lean release; moves `lean4-nix`) | the `lean-toolchain` files, `flake.lock`, possibly `lake-manifest.json` | `integrity.flake_nodes`; the hashes of `lean-toolchain` and of any changed `lake-manifest.json`; `seed_and_build_trust` `lean-seed-runtime.version` by hand |
| Dependabot `github-actions` bump of `ixcc.yml` | an action commit in `ixcc.yml` | `ci_actions[].commit` (and `.version` by hand, from the `# vX` comment); `integrity.repository_files` for `ixcc.yml` |
| Any edit of a covered IxCC file or of `ixcc.yml` | its hash | `integrity.tracked_files` or `integrity.repository_files` |

The mechanical fields (every integrity hash, the flake node revisions and the
`ci_actions` commits) are re-recorded by the checker itself, which prints them
as the tree stands (it never edits the ledger), and a `jq` program that merges
them while keeping each object's order. From `IxCC/`, in ix's development
shell:

```sh
lake build check-trusted-externs
mkdir -p plans
.lake/build/bin/check-trusted-externs --record > plans/ledger-pins.json
jq --indent 2 --slurpfile pins plans/ledger-pins.json -f tools/record-ledger-pins.jq \
  docs/trusted-externs.json > plans/trusted-externs.json
mv plans/trusted-externs.json docs/trusted-externs.json
git diff docs/trusted-externs.json   # review every changed pin against the diff it records
.lake/build/bin/check-trusted-externs
```

Then edit by hand what the audit still names (a seed version, a new action
repository, a symbol, a closure hash of the IxCK codec, a csimp theorem), set
`last_reviewed`, and commit the ledger with the change. `--record` leaves the
IxCK closure's hashes (`lean_dependencies[].closure`) alone: a change to
those 98 files is a dependency review, edited by hand, not a routine update.

All repository check scripts are Lean executables. The trust auditor uses
the pinned Lake TOML parser and GNU `sha256sum`; the independent encoder
and object checks invoke GNU binutils
and, on x86-64 Linux, the C test harnesses of `fixtures/x86` and the system
linker (`x86-elf-object`, `x86-hardware` only). These remain seed/build
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
copies. It checks source literals/comments, every spelling of native
evaluation above (and that kernel decision and fields named `native` pass),
unrecognized extern attributes, new executable roots, project/dependency
extern drift, imports and native entry points, integrity changes, the
integrity rule (a covered file without a pin, a pin outside the rule, its
globs), pinned repository files (an edited or unpinned `ixcc.yml`, and a
narrowed check filter in it), the required-check inventory (a check renamed in
`nix/checks.nix`, a listed check it lacks, and the Nix lexer's strings,
antiquotations and refusals), the repository's toolchain, malformed/duplicate
Cargo metadata, CI action drift (including scoped repository workflows and
their local actions), an overriding `flake.lock`, path-pinned pure Lean
dependencies, and unlisted, dropped, malformed or attribute-only `@[csimp]`
theorems. The Nix trust-ledger check runs these regressions too.

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

IxCC's addresses do not use this backend: `IxCC.Ixon.Address.blake3` is pure
BLAKE3 (`Address.blake3Pure`), so the actual compiler composition results in
`Recheck/Proof/Compile.lean` and every byte-level theorem rest on the three
standard axioms; the 46 fences that used to list
`Blake3.HasherOps.hash._native.native_decide.ax_1` (a `native_decide` proof of
`32 < 2 ^ System.Platform.numBits` inside `HasherOps.hash`) now list only those.
The backend's one remaining user is the erased checker's incremental hasher
(`Blake3.Rust.Hasher`) for its internal hash-consing keys, with explicit length
proofs. `Recheck.run` and `Recheck.sound` retain
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
erased checker adapted from an earlier ix (Ixon v3, a revision outside this
repository's history), with the checker's primitive table following this
repository's `Ix/PrimAddrs.lean` and the resource profile and claim framing
following ix's Ixon v4. It
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
annotated/plain recursion bytes (a dated record of an earlier ix, outside
this repository's history, kept as data: DO-18) under
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
entry names the Lake package, the modules our sources import from it, and the
SHA-256 of every file of their import closure. Each is a package of the
enclosing workspace (`source_kind: workspace_path`), at `pins.workspace_path`
relative to the project (`../IxCK` inside ix): the manifest must record it by
that path, and the directory must hold that package's `lakefile.lean`. The
closure hashes, not a revision, fix the audited source; a git-pinned
dependency is refused. The checker requires
every import of the project's sources that names neither a project module nor
a toolchain module to be such a recorded module; checks each closure file's
hash; rejects a closure file that declares a native symbol or an axiom (a
constructor named `axiom` is not one), uses `sorry` or `native_decide`, or
imports a module outside the closure or the toolchain; and requires its `@[csimp]` theorems to be exactly the entry's
`csimp_theorems` and its `implemented_by` substitutions exactly the entry's
`implemented_by_sites` (absent: none), each recorded with the ruling that admits
it.

The one entry, `ix-ck-kernel`, is ix's `IxCK/` package (`«ix-ck»`), beside
IxCC in the workspace, of which IxCC imports `IxCK.Ixon.Canonical`,
`IxCK.Ixon.Codec`, `IxCK.Kernel.Key`, `IxCK.Kernel.Admission.Tier`,
`IxCK.Kernel.Cached.CoreC` and `IxCK.Kernel.Ixon.Prelude`, and the grounding
library (`IxCCGrounding`) also `IxCK.Kernel.Core` and the kernel's model,
`IxCK.Kernel.Denotes` (a 98-module closure: the 82 modules of the production
library's, about 49,000 lines, 13,737 of them the committed role data, and 16
more for the model's statement, the set theory interface
`IxCK/Kernel/SetTheory/*`, `IxCK/Kernel/SetModel/Ops.lean` and
`IxCK/Kernel/Verify/{Level,LevelGeran}.lean`, about 3,500 lines; importing
`Init`, `Std` and, at elaboration time in `IxCK/Kernel/BasisGen.lean`, `Lean`;
not the kernel's proof tree). The model's files are pinned because the
grounding theorems are stated over them: a change to `Denotes.lean` (the
certified IxVM work's laws, when they land) fails this audit until reviewed.
`check-build-graph` refuses an import of the grounding library or of the model
from the production library or any program of the shared build, so the
production binaries' import closures stay within the 82. The codec is the ingress decoder and encoder;
the tiered admission entry and the executed typing core are the front end
over the kernel ([kernel front end](kernel-front-end-design.md)), which takes
an environment's acceptance and the relevance annotation's types from them;
`IxCK.Kernel.Key` gives the kernel's role vocabulary (`Ix.Kernel.Role`, `Role.all`), against
which IxCC decodes the binding section of a role-bound environment and maps
roles to its pinned identities ([byte contract](byte-contract.md)), so a role
is read as the kernel of the same build reads it. Its 32 `@[csimp]`
theorems are the entry's `csimp_theorems`, among them `Name.beq_eq_beqPtr`,
`Key.beq_eq_beqPtr` and `Level.beq_eq_beqPtr` (pointer-guarded equality),
`putTagN_eq_fast` and `getTagN_eq_fast` (the TagN codec specialised to its flag
widths), and the kernel's memoised term walks (`instantiate1_eq_instantiate1Fast`
and its siblings). Each is a proved equality, so the functions the theorems are
about are unchanged; only the compiled code path differs.

Its `implemented_by_sites` are the four substitutions the closure declares,
each admitted by the kernel's own runtime audit (`Ix.Kernel.Audit.runtimeRulings`,
`IxCK/Kernel/Audit/Roots.lean`), whose list the entry reuses rather than
reinventing: `Ix.Kernel.withExclusive`, implemented by `withExclusiveUnsafe`
(`IxCK/Kernel/Exclusive.lean`; the audit's one admitted runtime
implementation, whose type carries the obligation `k true = k false`, so the
reference-count read it performs cannot change a value), and the three
elaboration-time evaluators of `IxCK/Kernel/BasisGen.lean` (`evalInfo`,
`evalVal`, `evalEnv`, each implemented by its `unsafe` twin; the audit's
elaboration module, `meta` code compiled code cannot call). The kernel's
`@[computed_field]` hash overrides are not `implemented_by` in source and are
admitted by the same audit; the closure declares no `partial` definition and
no extern. The kernel takes its content hash as a parameter, so no assumed
substitution enters: IxCC instantiates it with its pure BLAKE3.
The resource-selection checker also uses its pure framing operations on the
recheck path, with pure BLAKE3 for the effective profile's identity. The
rechecker receives the raw profile bytes and pair records and validates them
against its Src declarations; it does not trust an ix acceptance Boolean.
A codec defect can make ingress reject a closure or read a different program
than ix compiled, which `Recheck.run` then checks as given; the front end over
the kernel checks IxCC's reading against the kernel's. The kernel's soundness
theorems are proved in its own package on Lean's standard axioms; IxCC imports
the executable kernel, not those proofs.
Nix packages exactly the closure this entry records (`nix/sources.nix`) under
the same package name with a library of exactly those modules
(`nix/build.nix`), so the kernel's proof tree is never built; the
`trusted-extern-ledger` check reads the same files at `../IxCK` in its copy of
the workspace.

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
flags the model leaves undefined are not compared. The Sail agreement (step S2 of the
[reference-model route](x86-reference-model.md)) remains the proof route.

**Native runs in the gates: test executables, no C (X1).** The native suites
run a compiled object as a test executable IxCC writes of it with the same
writer as `ixcc compile --exe` (`X86.Exe.writeFor`, checked by `checkFor`), with
the test shell [`IxCCTests/Exe/TestShell.lean`](../IxCCTests/Exe/TestShell.lean)
as its frame. The test shell is untrusted, integrity-pinned test code, like the
C drivers it replaced: after `prctl` and a seccomp filter that allows only
`read` from standard input, `write` to standard output or error and `exit`, it
serves binary requests from a host in Lean: call an export by a direct
`call rel32` with the six argument registers, sentinels in the callee-saved
registers and `rsp` at a fixed top, answering `rax:rdx` and whether the
sentinels and `rsp` survived; read or write bytes of the region (bounds
checked). The host ([`IxCCTests/Rt/Native.lean`](../IxCCTests/Rt/Native.lean))
does what the C runtime driver did: for each input it stores
`stack_budget` (the stack size less 4 KiB) at `region + 16`, calls
`cx_init(region, size, stack_budget)` and then the root, and reads the context
and the object area back. The region is private, a zero-filled segment of its
own one unmapped page above the stack segment, and untouched between `cx_init`
and the root's return; nothing is mapped right below it, past its last page or
below the stack, so a write just outside the region and a stack that ran past
its budget and its reserve both fault. Each result is decoded by `Rt.readback` and by an
independent decoder ([`IxCCTests/Rt/Decoder.lean`](../IxCCTests/Rt/Decoder.lean),
the C driver's decoder transcribed to Lean, separate code with a separate
derivation in the same language), and the two must agree. The back end's
harness ([`IxCCTests/Backend/Native.lean`](../IxCCTests/Backend/Native.lean))
sets up the context block as `cx_init` would and places generated programs'
regions at the Lean test region's address, in a zero-filled segment of its own.
No production path depends on any of it.

C remains in the tree only as test harnesses: `native_harness.c`,
`exports_harness.c` and `unwind_harness.c`, with which `check-x86-object` links
the object writer's fixtures and runs them (`native_harness.c` still supplies
the legacy `callRuntime` fixture's `ixcc_rt_allocate` stub until
`Instr.callRuntime` retires), and `hw_diff_harness.c`, with which
`check-x86-hardware` tests the processor against the instruction table. No gate
runs a compiled program through C. Because the native gates no longer link
the compiler's objects, `check-x86-object --ixcc` links objects `ixcc compile`
writes in the check (eleven objects: the five K1 programs, `k1.ixe`'s five
roots, the real-source RC fixture on the plain-RC route, `gcd` on the zero-RC
route, and the ABI, scalar and boundary corpus families' roots, one object per
family) with the system linker, without running them, and requires every export
where the object puts it.

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

The RC procedures' native controls
([`IxCCTests/Rt/Rc/NativeControls.lean`](../IxCCTests/Rt/Rc/NativeControls.lean))
and the same-arena reuse session
([`IxCCTests/Rt/Rc/ReuseSupport.lean`](../IxCCTests/Rt/Rc/ReuseSupport.lean))
run in test executables IxCC writes; until X1 they were C harnesses linked with
the object, and they are those harnesses transcribed to Lean, check for check.
They are test evidence, not allocator externs. The primitive controls write
synthetic fixture fields to test exact procedure behavior; the reuse session
initializes once and makes no allocator metadata writes afterward. The compiled
gates preserve 4,393 primitive assertions, 40 codec refusals, 15
complete-replay refusals, 25 standalone full-value checks and 168 same-arena
calls/drops with 114,820 independent assertions, full values by two decoders
and exact reclaimed-address sets.
The separately required `tests-cfg-rc` retains four complete abstract-Cfg
value/heap cases, bounded timeout checks and 12 bridge ownership/count controls;
its pure proof aggregate retains all 29 original marker/map/scope/bounds examples.
`tests-pipeline-rc` additionally compares complete values across actual RC
pipeline stages with independent list/pair formulas. Its allocation/inc/dec/free
counter is a test-side observer of production `Cfg.Rc.step`, differential-tested
against `Cfg.Rc.run`; it is neither a new trusted evaluator nor a native cost
theorem. The native modes retain two decoders' observations, reject
object-only text corruption before it runs even when its bundle is rehashed, and
exercise real-source root heap exhaustion separately from initializer refusal,
with successful same-code neighbors. Counts stop before caller output-drop;
physical reclamation remains covered by the existing native recycling gate.
These tests add no driver assumption, extern or trusted allocator.
The real-source fixture records its historical producer; final Phase 1.5 gate, producer
review and refreeze are still separate from these accepted local results.

**The comparison with test executables (X1).** Before the C drivers were
deleted, every line they printed in a required gate was also produced by a test
executable IxCC wrote of the same object, and the two had to agree: `init`,
status, value (an address as the same offset into each region), the
callee-saved registers and `rsp`, the observation and the object area. They
agreed on every line (2,955 across the native suites), and the Lean RC controls
and reuse sessions reproduced the C harnesses' 4,393 and 114,820 checks count
for count.

**The driver model (specification assumption
`x86-phase1-runtime-driver-model`).** `Recheck.sound` and the bounded
`Recheck.RcReplay.sound` are theorems about
`X86.Linked` ([`Linked.lean`](../IxCC/X86/Linked.lean)): the
object's execution from a `X86.Driver`
([`Driver.lean`](../IxCC/X86/Driver.lean)) that calls `cx_init` and
then the root's export, each at the address `ELF.symbol?` finds for its
symbol in the parsed object, and observes the root's result by
`Rt.readback`. Reading it as a statement about a native run assumes that the
caller and the loader set up those calls as the model does. Since X1 every
caller is an executable IxCC writes: the standalone executable's shell
(`x86-linux-exe-shell`, below) and, in the gates, the test shell. The writer
places the object's text byte for byte and resolves each of the shell's calls
to its export's offset by `ELF.symbol?`, and the executable check reads each
call's target back from the file (`check_sound`, `checkFor_sound`), so no
system linker resolves symbols. What the gates now assume:
- the Linux loader maps the executable as its checked program headers say:
  the file read and execute at `0x400000` (the text at `base`), the
  zero-filled segments read and write and zero, nothing executable on the
  stack;
- one region of `size` bytes at `region`, its bytes before the first call
  zero except the stack budget at `region + 16` (`ctx − 48`), which the host
  stores through the test shell before `cx_init`; the call stack (`budget + 56`
  bytes below `sp`, and the return slot) apart from the region;
- the test shell enters each call at its export's address with `rsp` at its
  fixed top less the return slot, its return address after the text,
  `rdi = region` and the arguments in `rsi`…`r9`, sentinels in the callee-saved
  registers, other registers and flags as it leaves them, and does not touch
  the region between `cx_init` and the root's return (it touches it only to
  serve the host's reads and writes between calls), as `TestShell.lean`
  describes;
- `read`, `write`, `exit`, `prctl` and `seccomp` behave as Linux documents them;
- the observation: status 0 and the value read back at the root's type over
  the region from `region + 16` (the host reads the region back through the
  shell and decodes it with `Rt.readback` and the independent decoder, which
  must agree), other statuses the wrapper's resource failures; arguments of
  2⁶⁴ or more cannot be passed.

Until X1 the caller was a C runtime driver linked by the system linker, and the
assumption covered that driver, the C compiler, the C library and the linker's
symbol resolution; X1 deleted the driver. The model maps only the region and
the call stack. A real process maps more (its file, the shell's 256 bytes, the
initial stack, the vDSO). That a run the model shows non-faulting is the
process's run, or the process stops on a fault, and writes nothing outside the
model's mapping is a theorem of the byte machine for every row
(`X86.ByteAgree`: agreement or fault, and the frame), no longer part of this
assumption. A caller with two call sites, the shell, calling `cx_init` from one
and the root from another with other registers, is modelled by `X86.LinkedAt`,
for which the object theorems hold (`Recheck.sound_at`, `RcReplay.sound_at`);
`X86.Linked` is its instance at the driver's own site. `Driver.Ok`, the numeric contract,
is a hypothesis of the theorem, satisfiable for every accepted artifact
(`Recheck.driver_exists`), not part of this assumption. The reading also rests
on `x86-v0-local-semantics`; the loader's mapping of the written executable is
part of this entry and of `x86-linux-exe-shell`.

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
stores the stack budget at `region + 16` as `X86.Driver.initBytes` has it, calls
`cx_init` once and then the root's SysV wrapper directly, under the
driver contract (a private region untouched by C, a stack budget
that leaves at least 1 MiB below the thread's stack limit); it checks the
status and the Nat tag of every result. No check, proof or production
artifact depends on these files, and the runner is outside the root flake.

**The standalone executable's shell (specification assumption
`x86-linux-exe-shell`).** `ixcc compile --exe` writes a static Linux x86-64
executable with no C compiler, C library, linker or assembler
([`IxCC/Exe.lean`](../IxCC/Exe.lean), [`X86/Exe/`](../IxCC/X86/Exe)): the
object's text byte for byte, read-only data (a seccomp filter and the
messages), and a *shell* that sets up the calls the model `X86.Driver` describes.
The shell is trusted code, about 950 bytes: platform code written as typed
x86 and encoded by the compiler's own encoder, with the system call (`0F 05`)
as a constructor of its own instruction type (`X86/Exe/Shell.lean`), never a
row of the program instruction table, so compiled program text still cannot
contain it. The entry assumes what [`X86/Exe/Code.lean`](../IxCC/X86/Exe/Code.lean)
says the shell does: confine the process (no new privileges, then a seccomp
filter allowing only `write` to file descriptors 1 and 2 and `exit`), parse
exactly the root's parameter count of decimal numerals from the initial stack,
store the stack budget at `region + 16`, call `cx_init` and the root on the
static stack by direct calls, and print the value (`n` for a `Nat`, `#k` for a
constructor without fields) or a message and a fixed status per failure. It
also assumes the kernel loads the file as its program headers say (the file
read and execute at `0x400000`, a zero-filled read-write segment at
`0x10000000` holding the stack and then the region) and enters it with the
System V initial stack. What is proved: `Layout.driver_canonicalOk`, every
clause of `Driver.CanonicalOk` for each accepted layout and each of the
shell's return addresses, which `X86.Exe.writeChecked` carries for both calls;
and `X86.Exe.check_sound`, the written file's structure read back by an
independent reader, including each call's target decoded from the file. Each
call is meant to see the driver `Layout.driver` builds, `cx_init` from its call
site and the root from its own (`X86.LinkedAt`; `Recheck.sound_at` holds for
it). That a run the model shows non-faulting touches only modelled memory is
`X86.ByteAgree`'s theorem. The driver model's entry
(`x86-phase1-runtime-driver-model`) covers the native gates' test executables,
which replaced the C driver in X1. This shell is retired on its own: the
shell proof (X0-P) takes the generic machine shell below first, and this one
stays ledgered until byte executables (X3) can replace its parsing and
rendering.

**The numeric state machines' generic shell (specification assumption
`x86-linux-machine-shell`).** `ixcc compile --exe FILE --machine` writes the
executable of a numeric state machine: a root `step : Nat → Nat → Nat` of a
state and an event whose result packs the next state and a request
([`IxCC/Exe/Machine.lean`](../IxCC/Exe/Machine.lean)), run by a generic shell
([`X86/Exe/Machine.lean`](../IxCC/X86/Exe/Machine.lean); 1,059 bytes, the same
for every machine). It parses and renders nothing: a program does that in
Lean compiled with it (`lib/IxccExe.lean`), so the decimal parsing and
rendering of `--exe`'s shell are not trusted code here. The entry is separate
from `x86-linux-exe-shell` so that each can be retired on its own; the shell
proof takes this one first. It assumes what the module note says the shell
does: confine the process with `--exe`'s filter; keep the state, the event,
an argument cursor and an output byte in its own 256 bytes above the call
stack's top; per call, store the budget at `region + 16`, call `cx_init`
and the step by direct calls on the static stack, check `rsp`, map a status
to 65 to 68 or 70; require an odd word (71); split it into the state and the
request field and perform the request (one argument byte, or 256 or 257; one
byte written to 1 or 2 and the answer 0 or 1; the program's exit status; 72
for anything else); and write a fixed message for each of its own failures.
It also assumes the kernel loads the file as its five program headers say
(the region in a segment of its own, one unmapped page above the stack
segment) and enters it with the System V initial stack. What is proved:
`X86.Exe.Machine.Layout.driver_canonicalOk`, every clause of
`Driver.CanonicalOk` at each call site for every initial bytes (a call starts
from whatever the previous one left), carried by `X86.Exe.Machine.writeChecked`;
and `X86.Exe.checkFor_sound`, the file's structure read back independently.
The session theorem is proved over the linked-object model
(`IxCC.Exe.Machine.session_sound`, `Rc.session_sound`, `machine_session_sound`):
every finite trace of a session is the source step's iteration on the same
answers, up to a final resource failure, unless the step goes wrong on the way.
It is also proved over the calls as the shell makes them, `cx_init` and the
step from two call sites (`machine_session_sound_at`, `Rc.session_sound_at`,
over `X86.LinkedAt`), with the third outcome at a call the source reaches along
a prefix of the trace. That a run the model shows non-faulting is the
process's run or stops on a fault, and writes nothing outside the model's
mapping (the shell's bytes included), is `X86.ByteAgree`'s theorem. That the
shell realises the session model is not proved (X0-P's later parts); with this
assumption the theorem is a statement about the executable.

The [indexed stream checker](stream-checking.md) preserves this boundary:
bounded decoding and cached canonical positions are proved exactly equal
to the original decoder and stream checker on all inputs. Production
emission and relocation validation use the same `Stream.Valid` certificate.
Four additional public fences retain the ordinary logical axiom basis.

| Boundary | Current scope | Evidence and remaining work |
| --- | --- | --- |
| Local ISA semantics | Agreement of the local byte machine with actual x86-64, including canonical addresses, unified code fetch, memory permissions, flags, faults, and the caller ABI. Compiler-contract traps must be proved unreachable; they are not hardware exceptions. | E1 and E2 prove local-to-local agreement. The [S0 readiness decision](x86-reference-model.md) pins the Sail snapshot; reference execution comparison, the Lean adapter, and S2 agreement remain pending. |
| Encoder stream/layout | Discharged for successful certified production emission. Raw `Encode.encode`/`Program.encode` clients must validate their output or prove the same facts. | `Stream.check_sound` checks every boundary, canonical position, target and relocation. Complete-stream proofs cover call-free execution and internal calls under concrete `SafeTrace` conditions, including residual return-slot bytes. `ELFLink` proves checked PC32 application and runtime CALL transfer. External procedure bodies still require their semantic/ABI contracts. |
| Runtime driver model | `X86.Driver`/`X86.Linked` model initialization and the root call for accepted scalar and bounded RC objects. The same entry describes `DriverSession`'s separate owned raw-word drop protocol; it does not upgrade the one-call theorem to arbitrary-session adequacy. | Existing pipeline gates plus `tests-rt-rc`, `tests-rc-certificate` and `tests-driver-session` check complete values, ABI, reclamation and same-region reuse. The callers are executables IxCC writes (the production and the test shell); the loader's mapping, the shells' code, source adequacy and general whole-call session framing remain explicit. |
| Standalone executable shell | `x86-linux-exe-shell`: the shell of `ixcc compile --exe` and the kernel's loading of the static executable, as `X86/Exe/Code.lean` describes them | `Layout.driver_canonicalOk` (the layout keeps the driver contract), `X86.Exe.check_sound` (the file's structure); `tests-corpus --exe` and `tests-exe`. The shell's behaviour from the loader's post-state is not proved; it stays ledgered until byte executables (X3) can replace it |
| Numeric state machines' shell | `x86-linux-machine-shell`: the generic request shell of `ixcc compile --exe --machine` and the kernel's loading of its executable, as `X86/Exe/Machine.lean` describes them | `X86.Exe.Machine.Layout.driver_canonicalOk` (the contract at every call, from any bytes), `X86.Exe.checkFor_sound`, the session theorem over the linked-object model (`Exe.Machine.session_sound`) and over the shell's two call sites (`machine_session_sound_at`), `X86.ByteAgree` (a non-faulting model run is the process's and writes only the model's mapping); `tests-exe` (the `phase1-machines` roots, `fib` against `--exe`, `echo` against Lean's interpreter and the model on the byte evaluator) and `tests-corpus`. The shell's realisation of the session model is not proved; the shell proof takes it first |
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
