# Certified Lean kernel

Ix's certified checker is [con-leche](https://github.com/leanprover/con-leche)'s
verified checker (`Ix.Kernel.Cached.checkDecls` at `.verified`), **vendored
in place under `Ix/Kernel/**` as a modified copy** (namespace `Ix.Kernel`;
see "Vendored con-leche" below), run on Ixon records by Ix's reader in
`Ix/Kernel/Ixon/`. The certified API is `Ix.Ixon.Admission.checkBytes`. This
page states what that entry does, what is proved about it, what is trusted,
how the gate checks the trust boundary, how the vendored copy tracks
upstream, and how to run the census.
The roadmap's section 2 (`plans/ix-certified-roadmap.md`) is the contract
this page implements; plan v4 (`plans/ix-kernel-con-leche-port-v4.md`, not
versioned) records the port's steps L0 to L6.

Nothing here certifies the Lean-to-Ixon compiler, the Rust checker, `Ix.Tc`
or IxVM. An accepted environment has a model; that it is the environment
the original Lean source meant is outside the claim.

## The certified entry

```lean
def Ix.Ixon.Admission.checkBytes (limits : Limits) (records : Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except KernelAdmission.Error Ix.Kernel.Env
```

`records` is an ordered list of `(Address, ByteArray)` pairs, one canonical
Ixon constant per pair; `blobs` holds literal payloads (`Nat` little-endian
bytes, `String` UTF-8 bytes) by address; `hint` is an optional, untrusted
reducibility hint per constant. The entry runs, in order:

| Stage | Function | Fails with |
| --- | --- | --- |
| the committed pin table, prelude and Nat-operation pins load | `defaultPins`, `builtinPrelude`, `builtinNatOpPins` | `.prelude reason` |
| batch limits: record and blob counts, total payload bytes | `Admission.preflight` | `.limit resource` |
| key uniqueness: no two records and no two blobs under one address | `Admission.uniqueKeys` | `.duplicate table position address` |
| canonical per-record decoding within byte and universe-node limits | `Admission.decodeRecords` | `.decode position address reason` |
| the Ixon reader: records to `Array Ix.Kernel.Declaration` | `IxonReader.readRecords` | `.read position (.malformed _ / .declined _)` |
| the prelude is put in front (`Ix.Kernel.Frontend.preparePrelude`) | | |
| con-leche's fold | `Ix.Kernel.Cached.checkDecls .verified natPins` | `.kernel error position` |

The pipeline is `Ix.Ixon.KernelAdmission.checkBytes`; `checkBytesWith`
takes the pin table, prelude and Nat-operation pin list as parameters, and
`checkConstants{,With}` start from decoded records. Two variants share the
byte stage and the checker: `Ix.Ixon.Projection.checkBytes` reconstructs
omitted projection records (addresses by pure BLAKE3 of their canonical
bytes) before checking, and `Ix.Ixon.BlockOrder.checkBytes` also checks the
order of mutual blocks: an inductive, definition or mixed block in canonical
structural order (`canonicalClasses`, as Rust's `canonical_check.rs`), a block
of recursors in motive order (member `j` eliminates motive `j`, read off its
type as the reader reads it, `recursorMotive_of_analyse`), which is the order
the compiler stores it in and not always the structural one (2026-10-01:
the structural check refused 2 of the 7 compiled recursor blocks of the
fidelity fixture, `Rose.rec`/`Rose.rec_1` and `Args.rec`/`Tm.rec`).

**Outcomes.** `Admission.outcome` classifies every failure as a reject (the
input is wrong) or a decline (the checker does not certify it):

| Error | Outcome | Why |
| --- | --- | --- |
| `.limit` | decline | a coverage bound, not evidence about the input |
| `.duplicate`, `.decode` | reject | the bytes are malformed |
| `.read _ (.malformed _)` | reject | the records describe no declaration (a missing reference or blob, a bad table index, a recursor header that disagrees with its block, ...) |
| `.read _ (.declined _)` | decline | unsupported: unsafe or `partial` definitions, unsafe axioms, an inductive block whose recursor is not in the input, a mutually recursive definition block, a block the in-process modeller declines |
| `.prelude` | decline | a corrupted committed table |
| `.kernel` | decline | every checker verdict: con-leche reports fuel exhaustion as `internal` and a failed conversion search as `invalid`, and neither is independent evidence that the input is wrong |

Only an accept carries the theorems below.

**Host obligations.** The host supplies the order, the address keys and the
blobs. Addresses are keys, not authenticated hashes (only the projection
variant derives addresses). The entry does not reorder beyond
`preparePrelude`: each record must follow the records it references; a
record that contains a literal must follow the constants the literal names
(`IxonReader.literalEdges`: the `Nat` block, and for a string literal
`String`, `String.ofList`, `List`, `Char`, `Char.ofNat`); a pinned `Nat`
operation must follow its certificate ground. A host order that violates
this declines; it cannot cause an unsound accept. The census driver's
order (`Benchmarks/Kernel/CheckIxeStep.lean`, `order`) satisfies it.

## The theorems

All public theorems are in `Ix/Ixon/Consistency.lean`, about the executed
function, at the committed tables. Each is the corresponding theorem of
`Ix/Ixon/KernelConsistency.lean` (namespace `Ix.Ixon.KernelAdmission`)
at `checkBytesWith`, where it holds for every pin table, prelude and
Nat-operation pin list, so no theorem depends on how the tables were
generated. Every public and fidelity root depends on exactly `propext`,
`Classical.choice` and `Quot.sound`.

| Theorem (`Ix.Ixon.Admission.`) | Statement, for `h : checkBytes limits records blobs hint = .ok env` |
| --- | --- |
| `checkBytes_eq` | `checkBytes = KernelAdmission.checkBytes` (definitional) |
| `checkBytes_has_model` | `∀ V [Ix.Kernel.SetTheory V], Nonempty (Ix.Kernel.Model V env)` |
| `checkBytes_has_model_values` | there is a model `M` in which every stored `defnInfo cv value _` satisfies `Denotes M.cval env φ ρ value (M.cval cv.name φ)` for all `φ ρ` |
| `checkBytes_no_proof_of_False` | no `ci ∈ env.consts` has type `.const Ix.Kernel.falseName []` |
| `checkBytes_no_False_theorem` | no theorem record of the decoded input (`RecordsRead limits records constants`) has a type that the reader reads as `.const Ix.Kernel.falseName []` |
| `checkBytes_reading` | the tables load; `WithinBatch limits records blobs`; `UniqueKeys records blobs`; `RecordsRead limits records constants` for some `constants`; and `KernelAdmission.Installed pins pre natPins constants blobs hint env` |
| `checkBytes_resources` | `resourceUnits constants ≤ 2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes` |

`Ix.Kernel.Model V env` (`Ix/Kernel/Denotes.lean`) assigns a set
`cval c φ` to every constant at every level assignment such that every
stored constant is a member of what its type denotes (`mem`), what the
built-in `False` denotes is empty (`false_empty`), and what the built-in `Eq`
denotes is set equality (`eq_equality`). Definitional equalities need no
clause: an accepted `rfl` theorem's two sides denote the same set. The
model theorem is `Ix.Kernel.model_exists` (`Ix/Kernel/MainTheorem.lean`,
upstream's statement and proof) at the prepared declarations: it holds for
every declaration array the fold accepts, so the reader owes nothing for
consistency. Definition values come from con-leche's `defn_reads` through
`Ix.Kernel.IxonFold.checkDecls_model_defn_values`
(`Ix/Kernel/Ixon/Values.lean`). Theorem and opaque bodies have no value
equation, by con-leche's design.

**Fidelity** is what `checkBytes_reading` adds to consistency:

- `WithinBatch` and `UniqueKeys` (`Ix/Ixon/Verify/Admission.lean`): the
  batch limits hold, and the record keys and the blob keys are each
  pairwise distinct (`preflight_ok_iff`, `uniqueKeys_ok_iff`).
- `RecordsRead`: each payload is the canonical encoding of its decoded
  constant within the per-record limits, keys unchanged
  (`decodeRecords_ok_iff`, unique by `RecordsRead.deterministic`).
- `Installed` (`Ix/Ixon/KernelConsistency.lean`): the reader's output is a
  record-by-record reading of the decoded records (`StreamRead`, from
  `readRecords_spec`), no two decoded records share an address
  (`Installed.keys`, from `readRecords_nodup`), and the fold accepted
  exactly that output behind the prelude. `Installed.skels`: the
  environment has exactly the install skeletons of the accepted array.
  `Installed.singleton`: every definition, theorem, opaque, axiom or
  quotient record is read under its name with its level parameters, its
  type's reading and its value's reading (or the projection rewrite), and
  is installed under that name with its kind (a quotient record,
  `sorryAx` and `Quot.sound` install as the pinned blocks do).
- `keyName_injective` and `Ctx.nameOf_of_pin`/`Ctx.nameOf_of_unpinned`
  (`Ix/Kernel/Ixon/{Reader,ReaderSpec}.lean`): which name a reference
  is read under.

Not proved:

- that installed types and values equal the decoded ones. Con-leche
  installs the annotation of a declared term: binder regimes (`pw`) are
  computed (the reader emits `pw := .never`), `let` is ζ-reduced, and
  projections are checked. The intended statement is about `pw`-erasure and
  needs a lemma about con-leche's `installConstantVal`/`installValue`;
- the member-level reading of inductive blocks (member order, constructor
  and recursor headers, rule constructors) through `readInductive`;
- per-member completeness of definition blocks (`defOrder` is not proved to
  be a permutation);
- that the committed table pins Init's own constants. That is the
  generator's verification, not a theorem; the no-False theorems are stated
  at `falseName` and hold for any table.

The projection and block-order variants have the same shape:
`Ix.Ixon.Projection.checkBytes_{run_iff, ok_iff, of_expansion, reading,
has_model, no_proof_of_False}` and `Ix.Ixon.BlockOrder.checkBytes_{run_iff,
ok_iff, of_ordered, reading, has_model, no_proof_of_False}`, each with
`UniqueKeys` in its reading. The separate package `Models/SetTheory`
(Mathlib) provides `IxSetTheoryModel.zfSetTheoryOfCarneiro`, a
`Ix.Kernel.SetTheory ZFSet` instance under `OmegaInaccessibles`, and the
corollaries `IxSetTheoryModel.checkBytes_has_ZFSet_model` and
`IxSetTheoryModel.checkBytes_no_proof_of_False`.

## Keys, pins and the prelude

**Keys** (`Ix/Kernel/Ixon/Reader.lean`). Con-leche's environment is keyed
by `Ix.Kernel.Name`. A reference `ConstRef Address` is encoded under the
reserved root `ix`: `.member b i` is `ix.<hex b>.i` and `.ctor b i c` is
`ix.<hex b>.i.c`, with numeric components (`keyName`, injective). Level
parameters are positional. Three kinds of names differ:

- recursors are named after what they eliminate, as Lean names them
  (`T.rec`, and `T.rec_j` for the `j`-th auxiliary motive of a nested
  block), because con-leche finds a block's recursor by name;
- pinned references take their pinned name;
- the pinned standard-axiom constants and their recursors carry Lean's own
  level-parameter names (`Pins.levels`), because con-leche's `matchesPin`
  compares them, and a large eliminator names its extra level parameter
  so that con-leche recognises it.

**Pins** (`Ix/Kernel/Ixon/PinData.lean`, generated). The table maps 55
references to con-leche's pinned names and no others: the basis (`Eq`,
`Nat`, `PUnit`, `Empty`, `False`, the `Quot` package), `And` and `Bool`, the
literal support (`String`, `String.ofList`, `List`, `Char`, `Char.ofNat`),
the structural and pin-certified `Nat` operations, the standard axioms with
`Iff` and `Nonempty`, the compiler-trust family with `True`, and `sorryAx`.
`pinMap` refuses a table that is not a partial injection or that uses the
`ix` root or a derived name shape. The table decides coverage only:
con-leche compares every pinned name's declaration with its pinned shape
(basis blocks up to `canon`, with a reserved-name reject otherwise; literal
support and `Nat` operations by exact type shapes and certified
recurrences; standard and trust axioms by `matchesPin`), so a pin on a
constant of another shape is refused, never accepted under the pinned
name.

**Nat-operation pins** (`Ix/Kernel/Ixon/NatOpPinData.lean`, generated).
One `Ix.Kernel.NatOpPinSet` for the eight pin-certified operations (`div`,
`mod`, `gcd`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`): the pins are
the operations' stored values in the compiled Init, the certificates are the
theorems of `Ix/Kernel/PinGen/Certs.lean` compiled by Ix. `model_exists`
holds at every pin list, so the list is untrusted.

**Prelude** (`Ix/Kernel/Ixon/Prelude.lean`). Con-leche puts twelve
declarations in front of every fold: the basis blocks `Eq`, `Nat`, `PUnit`,
`Empty`, `False`, the quotient package (four `Quot` constants and
`Quot.sound`), `And` and `Bool`. Here they are the compiled Init's own Ixon
records (`PinData.prelude`, canonical bytes by address), decoded by the
canonical decoder and read by the same reader. The empty stream installs
27 constants. A stream that declares a prelude constant is checked on its
own record (`preparePrelude` moves the stream's copy to the front); the
prelude's copy fills in where the stream has none.

**Regeneration.** Both tables come from `kernel-pin-gen`
(`Benchmarks/Kernel/PinGen.lean`), which checks every pinned
constant's record and the literal capabilities through con-leche's fold
before writing:

```sh
lake exe ix compile Benchmarks/Compile/CompileInitStd.lean --out .lake/envs/initstd.ixe
lake exe ix compile Ix/Kernel/PinGen/Certs.lean --out .lake/envs/certs.ixe --consts <the certificate theorems>
lake exe kernel-pin-gen .lake/envs/initstd.ixe .lake/envs/certs.ixe \
  Ix/Kernel/Ixon/PinData.lean Ix/Kernel/Ixon/NatOpPinData.lean
```

The full `--consts` list and the source hashes are in the generated files'
headers. The table names addresses, so a toolchain or compiler change that
moves Init's addresses requires regeneration: until then the moved
constants are not pinned and the inputs that need them (literals, the
pinned `Nat` operations, the standard axioms) decline. Soundness does not
depend on the table.

## Trust surface

The theorems are about the Lean functions. Trusted beneath them: Lean's
kernel, compiler and runtime, and the inherited `Init`/`Std` primitives the
compiled code reaches (the entry's closure reaches 123 inherited externs,
for example `ByteArray` and `String` primitives and `lean_sarray_dec_eq`,
which implements `ByteArray` equality and therefore `Address` equality).
Not in the closure: `ix_rs`, C or Rust BLAKE3, `Ix.Tc`, any JSON or
lean4export parser. The projection variant computes addresses with pure
Lean BLAKE3 (`Address.blake3Pure`).

Project-level execution constructs are admitted only as named by
`runtimeRulings` (`Ix/Kernel/Audit/Roots.lean`):

| Construct | Where | Why admitted |
| --- | --- | --- |
| `@[computed_field]` overrides | `Ix.Kernel.Level`, `Ix.Kernel.Expr`, `Ix.Kernel.Name` | cached hashes and packed data; a compiler feature, trusted with the compiler |
| project `@[csimp]` | `Ix.Kernel` | each replacement theorem depends on the standard axioms only |
| `withPtrEq`, `withPtrAddr`, `ptrEq`, `isExclusiveUnsafe` and their unsafe implementations | Lean's `Init` | the continuation carries the obligation that it does not observe the answer |
| `Ix.Kernel.withExclusive` `implemented_by` `withExclusiveUnsafe` | `Ix/Kernel/Exclusive.lean` | its type carries `k true = k false`, discharged by `Subsingleton.elim` |
| elaboration-time `unsafe`, `implemented_by`, `meta import Lean` | `Ix.Kernel.BasisGen`, `Ix.Kernel.PinGen*` | elaboration only; compiled code cannot reach them |
| `partial` | `Ix.Kernel.Frontend.InModel`, `InModelDump` | con-leche's in-process modeller, vendored as upstream has it |

Import allowlists (`Ix/Kernel/Audit/Roots.lean`):

- `kernelImportAllowlist`: `Init`, `Std`, `Ix.Kernel` (the vendored
  checker and Ix's boundary), `Ix.Address.Core`, `Ix.Ixon.Types`. It fences
  the reader, the record store, the projection writer and the pure Ixon
  types.
- `importAllowlist` (the certified API's closure, rooted at
  `Ix.Ixon.Admission`): the above plus exactly `Ix.Ixon.{Codec, Wire,
  WireCheck, Bounded.Constant, Bounded.Universe, Canonical, Admission,
  KernelAdmission}`. No projection hashing, block order, `Ix.Address.Pure`,
  proof module or `Lean` (outside `elaborationImports`).
- `proofImportAllowlist` (the theorem modules): `importAllowlist` plus
  `Ix.Ixon.Bounded.Size`, `Ix.Ixon.Verify`, the two theorem modules and
  `Lean`.
- `elaborationImports`: below `Ix.Kernel.BasisGen` and
  `Ix.Kernel.PinGen` only `Init`, `Std`, `Lean` and `Ix.Kernel`.

`Std` is admitted for its maps and their lemmas, as con-leche uses them.

## Audits and fences

The audits are Lean modules that fail elaboration on a violation. They are
built by the strict standalone package `IxKernel/` (`lake -d IxKernel build
--wfail`, sources from the repository, no dependency beyond the toolchain).

| Module | Checks |
| --- | --- |
| `Ix/Kernel/Audit/Roots.lean` | presence of every root (`publicRoots` 20, `fidelityRoots` 17, the operations); each at exactly the three standard axioms (`#guard_kernel_axioms`); the import closures against the allowlists; frozen runtime closures with their rulings; frozen `#check` statements; a control showing the fold fails without the rulings |
| `Ix/Ixon/Admission/Audit.lean` | the byte stage's imports, closure and extern difference, its lemmas' axioms, and the public statements |
| `Ix/Ixon/ProjectionAudit.lean`, `Ix/Ixon/BlockOrderAudit.lean` | the variants' imports, closures, extern differences and statements, and the projection writer's guards |
| `Ix/Ixon/Audit.lean` | the codec's own import, runtime and axiom audit |
| `Models/SetTheory/IxSetTheoryModel/Audit.lean` | the model package's full dependency closure: standard axioms only |

Frozen runtime closures (compiled functions; inherited externs):

| Roots | Functions | Externs |
| --- | ---: | ---: |
| fold `Ix.Kernel.Cached.checkDecls` | 3022 | 83 |
| reader `readRecords`, `readStream` | 1886 | 82 |
| entry: the API, `KernelAdmission.checkBytes{,With}`, `checkConstants{,With}` | 5310 | 123 |
| byte admission: `preflight`, `uniqueKeys`, `decodeRecords`, `checkBytes` | 5308 | 123 |
| projection: `address`, `reconstruct`, `Projection.checkBytes` | 5430 | 132 |
| block order: `checkBytes`, `canonicalClasses`, `compareExpr` | 5563 | 132 |

A frozen value changes only in a commit that explains the change in the
audit's comment (the closures above include L6b's `uniqueKeys`, 10
functions, cl-m1's adapted modeller grouping: 6, and 15 in the reader,
which also reaches `List.mergeSort`, T1's record maps: −2, and its address
encodings: +4, and cl-level's Géran fallback of the level comparison: 12, and
13 in the reader, with `Int.natAbs`; the block-order entry's motive order for
recursor blocks: 9). Statements are re-recorded the same way.

`lake run check-kernel [--with-model]` is the gate. In order:

1. `scripts/check-kernel-retirement.py`: no active reference to a retired
   intrinsic module, entry point, executable or script (with negative and
   positive controls), and `scripts/vendor-conleche.py check-lake`: the
   vendored library's globs are exactly the vendored tree;
2. the strict `IxKernel` build with every audit;
3. the host build of the kernel tests (`Tests/Ix/Kernel/{ByteAdmission,
   Reader, CertifiedEntry, Projection, BlockOrder, Codec, ...}`),
   whose `#guard`s run at elaboration;
4. `kernel-provenance` (below);
5. `kernel-codec` (production codec against Rust) and `kernel-order`
   (canonical block order against Rust);
6. with `--with-model`, the `Models/SetTheory` build and its audit;
7. `scripts/layering.sh`: the vendored tree's import layering, by upstream
   path (implementation never imports theory, base never imports the model
   lane, the rules fence and its five recorded doors, and the boundary: a
   vendored module imports only the vendored tree, `Init`, `Std` and, at
   elaboration time, `Lean`);
8. `scripts/trust-surface.sh`: a lexer-based scan of the vendored tree for
   compiler escapes (`unsafe`, `implemented_by`, `computed_field`,
   `native_decide`, `extern`, `sorry`, `axiom`, ...); 11 escapes in four
   allowlisted files (`Ix/Kernel/{Expr,Name,Exclusive,BasisGen}.lean`)
   are permitted, each with its justification in the script;
9. `kernel-entry-cases`: Lean declarations of
   `Tests/Ix/Kernel/EntryCaseDefs.lean` compiled by Ix's compiler and
   submitted as canonical bytes to `checkBytes`, each with an exact expected
   verdict (accepts: a definition, a theorem, an inductive with its
   recursor, a structure with a projection, a quotient reduction, `Nat`
   literals and a pinned `Nat` operation, a `String` literal, a nested
   inductive, the opaque face of a `partial` definition; rejects: truncated
   bytes, a duplicate constant, a duplicate blob, `Nat.rec` with a wrong K
   flag; declines: `Nat.add` with another value, a `partial` definition's
   `_unsafe_rec` body, a non-standard axiom, a theorem of `False`). Rows go
   to `.lake/build/kernel-entry-cases.jsonl`.

The CI job runs the same gate and keeps the codec, order and entry-case
logs.

## Vendored con-leche

[Con-leche](https://github.com/leanprover/con-leche) is a Lean kernel
checker written in Lean whose acceptance is proved to imply consistency:
`ConLeche.model_exists` gives every environment its fold accepts a model in
any set theory implementing its `SetTheory` interface, on the three standard
axioms. Ix uses it as its certified checker, vendored in place: `Ix/Kernel/**`
holds a modified copy of the files of con-leche's `ConLeche/` tree that the
checker, the reader and the theorems use, and Ix's own boundary beside them.

**What is vendored, from where.** 452 Lean modules from
`https://github.com/leanprover/con-leche.git` at
`ae0c0c4e4ce6a0081648aff03fe9c39d002c4526`, seven of them (the files
upstream task #323, KEEPPROJ, changed) at
`3ca9e2fe749a51cba4c6e3527aeecba074c29316`, under Apache-2.0
(`Ix/Kernel/LICENSE-CON-LECHE`, upstream's `LICENSE` verbatim;
`Ix/Kernel/NOTICE` states the modifications). They are the import closure
of `model_exists`, the eight frontend modules the reader calls, and
`Verify/Cached/StreamThm.lean`.

**The rewrite.** Every vendored file is upstream's file passed through one
deterministic script, `scripts/vendor-conleche.py`:

- paths: `ConLeche/Kernel/X` becomes `Ix/Kernel/X` (the kernel directory is
  flattened), any other `ConLeche/X` becomes `Ix/Kernel/X`;
- names: the namespace and module prefix `ConLeche` (and `ConLeche.Kernel`)
  become `Ix.Kernel`, as whole words, so `import ConLeche.Kernel.Core` is
  `import Ix.Kernel.Core` and `ConLeche.Expr` is `Ix.Kernel.Expr`;
- one first line, `-- con-leche's <upstream path>, vendored by
  scripts/vendor-conleche.py (paths and namespace ConLeche → Ix.Kernel); see
  Ix/Kernel/NOTICE.`

445 of the 452 modules are exactly that (`Transformation.rewritten` in the
manifest), so they stay "verbatim up to the rewrite", and checkably so:
`kernel-provenance --source-git <checkout>` re-derives each from upstream
through the script and compares hashes. The script refuses an upstream path
that would land in Ix's boundary or collide after the flattening, and its
`upstream` command inverts the path map (the fences classify modules by
upstream path).

**What is adapted, and why.** Seven vendored modules carry further changes,
each listed in its port header (`Ported from con-leche at <revision>.
Source: <upstream path>. Transformations: ...`) and its manifest row, and
then the same rewrite:

| File | Change | Why |
| --- | --- | --- |
| `Ix/Kernel/CheckerBase.lean` | imports `NatOpPinSet` instead of `NatOpPins` | upstream's `NatOpPins` splices JSON pin dumps; Ix's Nat-operation pins are generated from Ixon records (`Ix/Kernel/Ixon/NatOpPinData.lean`) |
| `Ix/Kernel/Verify/Cached/{AgreeFloor,PushChain}.lean` | `import all Init.LetFun` | Lean 4.34.0 no longer exposes `letFun`'s body, which these proofs unfold |
| `Ix/Kernel/Frontend/InModel/Nested.lean` | container groups formed largest family first | Ix's compiler orders a nested block's auxiliary motives canonically (cl-m1) |
| `Ix/Kernel/Level.lean`, `Ix/Kernel/Verify/Level.lean` | the `(param, max)` case falls back on Géran's sublevels, with its soundness case | nanoda's comparison is incomplete there, and Ixon's canonical levels reach the gap (Mathlib's `RatFunc.liftOn_def`, cl-level) |
| `Ix/Kernel/MainTheorem.lean` | only `model_exists` kept | the NDJSON corollary needs a frontend Ix does not use |

The axiom pin `Tests/Ix/Kernel/Axioms.lean` (upstream's
`tests/ConLecheTests/Axioms.lean`, cut to the vendored closure) is the
eighth adapted row. Two modules inside the vendored tree are Ix's,
`Ix/Kernel/LevelGeran.lean` and `Ix/Kernel/Verify/LevelGeran.lean`
(Géran's sublevels and their soundness and completeness), because the
adapted `Level` files import them and a vendored module imports only the
vendored tree. Upstream's `ConLeche/Kernel/NatOpPins.lean` is not vendored.

**Ix's boundary beside it** (`Ix/Kernel/{Ref,Search}.lean`,
`Ix/Kernel/{Audit,Ingress,Egress,Ixon}/`, the umbrella `Ix/Kernel.lean`) is
Ix-authored: the Ixon reader and its specification, the committed pins and
prelude, the record store, the projection writer and the audits. It was
`Ix/Kernel/ConLeche/` until 2026-10-01; the vendored tree was `ConLeche/**`
with namespace `ConLeche`, byte-identical to upstream, from the port (plan
v4, 2026-09-30) until the user's ruling of 2026-10-01 moved it under
`Ix.Kernel`.

**Builds.** The vendored modules are the library `IxKernelVendored` in both
`lakefile.lean` and `IxKernel/lakefile.lean`, for one option:
`linter.deprecated` is off, so upstream's 4.33.0-era sources build under
`--wfail` on 4.34.0 unchanged. Its globs are exactly the vendored tree
(`vendor-conleche.py check-lake`, run by `check-kernel`).

**Syncing with upstream.** Upstream drifts (master has uniform inductives,
FEnv linearity, csimp openers); a sync is a separate change:

1. Fetch the new revision into a con-leche checkout (`plans/refs/con-leche`).
2. `python3 scripts/vendor-conleche.py sync <checkout> <revision>`: it
   rewrites every vendored file from the new revision, leaves the adapted
   and Ix-authored files alone (and lists them), and lists upstream files
   that are not vendored. Review `jj diff`; vendor any new module the
   closure now imports (`sync <checkout> <revision> <path>...`, then
   `check-lake` for the lakefile globs).
3. Re-apply each adaptation to its new upstream source, keeping its port
   header (`Source:` is the upstream path).
4. `python3 scripts/vendor-conleche.py rows <checkout> <revision> <paths>...`
   prints the rewritten rows; add the adapted ones by hand, then
   `python3 scripts/provenance-rows.py rows.tsv --check-dest . --splice
   Tests/Ix/Kernel/ImportManifest.lean`; set `conLeche.revision` (or add an
   origin, as `conLecheKeepProj` for #323) and the revisions in
   `Ix/Kernel/NOTICE` and the lakefile docstrings.
5. `lake exe kernel-provenance --source-git <checkout>` and the full gate.
   A changed closure moves the frozen counts; re-record each with its
   explanation, and re-record changed statements.

## Provenance

`Tests/Ix/Kernel/ImportManifest.lean` records every imported file: source
path and SHA-256 at the origin's revision, destination path and SHA-256, and
transformation (`verbatim`, `rewritten` by `scripts/vendor-conleche.py`, or
`adapted` with a summary). Rows are grouped by origin and licence:

- con-leche, `https://github.com/leanprover/con-leche.git` at
  `ae0c0c4e4ce6a0081648aff03fe9c39d002c4526`: the 452 vendored modules (445
  rewritten, seven adapted; above), the axiom pin `Tests/Ix/Kernel/Axioms.lean`,
  the licence, and the two fence scripts with the lexer fixture. The seven
  modules upstream task #323 (KEEPPROJ) changed are at
  `3ca9e2fe749a51cba4c6e3527aeecba074c29316` instead and form their own set
  (int-5). `MainTheorem.lean` and the axiom pin carry Argument's
  modification notice and are licensed `Apache-2.0 AND (MIT OR Apache-2.0)`;
  the rest is `Apache-2.0`;
- the old Ix branch `jcb/ix-kernel-consistency` at `ad60e5f6`: only
  `Ix/Kernel/Ref.lean` and its licence and notice files remain since L6;
- `authored`: the 68 Ix-authored modules under the inventoried trees, among
  them the boundary `Ix/Kernel/{Ixon,Ingress,Egress,Audit}/**`,
  `Ix/Kernel/Search.lean`, the umbrella, the pure Ixon boundary, and
  `Ix/Kernel/LevelGeran.lean` and `Ix/Kernel/Verify/LevelGeran.lean`
  (cl-level), the only Ix modules inside the vendored tree.

`lake exe kernel-provenance` checks that every Lean file under `Ix/Kernel`
and `Ix/Ixon` (and `Ix/Kernel.lean`, `Ix/Address/Core.lean`) is recorded;
every destination hash; the vendoring header of every rewritten file and
that its path is the script's destination of its source; the port header of
every adapted file; licences and licence files. `--source-git <con-leche
checkout>` also verifies every source hash at the recorded revision and
re-derives every rewritten file from upstream through the script
(`plans/refs/con-leche` and `plans/refs/con-leche-upstream` hold both
revisions); `--source <jj workspace>` does so for the old branch, which
needs a workspace holding `ad60e5f6`. The upstream-sync recipe is above.

## Census

The census measures coverage on a compiled corpus; it is not a certified
verdict. `kernel-check-ixe` (`Benchmarks/Kernel/CheckIxe.lean`, entry
`CheckIxeMain.lean`; `kernel-census-cl` is the same driver) reads an
`.ixe`, orders its primary records (the prelude's first, then dependencies,
`Nat`-operation grounds and literal edges), reads each record with the Ixon
reader and installs and checks it one record at a time with an incremental
step of con-leche's fold (`Benchmarks/Kernel/CheckIxeStep.lean`),
continuing past failures and reporting dependents of a failure as blocked.
Hints are the compiler's. Each row is JSON (`address, names, kind, outcome,
reason, micros, readMicros`).

```sh
lake build --wfail kernel-check-ixe
lake exe ix compile Benchmarks/Compile/CompileInitStd.lean --out .lake/envs/initstd.ixe
systemd-run --user --scope -p MemoryMax=24G -p MemorySwapMax=0 \
  env CHECK_IXE_WATCH_MB=12000 scripts/check-ixe-guarded.sh \
  .lake/build/bin/kernel-check-ixe .lake/envs/initstd.ixe .lake/envs/initstd.jsonl
python3 scripts/check-ixe-report.py .lake/envs/initstd.jsonl
```

Usage: `kernel-check-ixe <input.ixe> <output.jsonl> [limit]`. Environment:

- `CHECK_IXE_WATCH_MS` (default 60000) and `CHECK_IXE_WATCH_MB` (default 20000):
  a watchdog ends the run with exit code 3 when one record's check exceeds
  the time or the process's resident memory exceeds the size, and appends
  the record's address to `<output>.runaway`. The resident size includes
  the decoded corpus, which the driver holds in memory: about 4 GB for
  Init and about 38 GB for Mathlib. `CHECK_IXE_WATCH_MB` must exceed it, or
  the watchdog fires before the first check (for Mathlib, for example,
  `CHECK_IXE_WATCH_MB=46000` under a `MemoryMax` above that);
- `CHECK_IXE_SKIP` (comma-separated addresses) declines those records
  unchecked; `scripts/check-ixe-guarded.sh` reruns with every recorded runaway
  skipped until the run completes;
- `CHECK_IXE_ROOTS` (comma-separated Lean names) restricts the run to the
  prelude and the dependency closure of those constants.

Run one census at a time, under a memory cap, with no concurrent build.
`scripts/check-ixe-summary.py` and `scripts/bench-check-ixe.py`
summarize and compare runs. Mathlib's `.ixe` comes from
`Benchmarks/Compile/CompileMathlib.lean` (`Benchmarks/Compile/README.md`).

## The retired intrinsic kernel

From K0 (2026-09-17) to L5, the certified checker was an intrinsic,
proof-carrying kernel in `Ix/Kernel/**` (`Ix.Kernel.check`, `checkDecls`,
`checkEnv`), built on a set model and syntax ported from the Ix branch
`jcb/ix-kernel-consistency` at `ad60e5f6` (with con-leche's `SetTheory` at
`86cd20a6`). Each admitted declaration constructed its model extension
(`StepClaim`, `AdmissionClaim`); the public theorems were
`check_has_model`, the conditional `checkDecls_has_model`, a semantic
`no_proof_of_False` over `Env.EmptyType`, installation fidelity
(`Ingress.Installed`) and `checkBytes_unique_keys`. Its supported profile
covered single definitions, theorems and opaques, ordinary inductive
families with supplied recursors, structures, `Nat`, equality, quotients
and the two standard axioms, and declined arbitrary axioms, unsafe and
partial declarations, and general mutual and nested inductives. L5
(2026-09-30) made con-leche behind the Ixon reader the certified API and
renamed the intrinsic entries `checkBytesIntrinsic`; L6 (2026-10-01)
deleted the kernel (132 files, 29,805 lines) with its entries, 19 test
modules, census, benchmark and host differentials (25 files, 4,080
lines). The last tree that contains it is the parent of "L6-A: retire the
intrinsic entry points and their consumers" in this branch's history. The
retirement's file-by-file
inventory is in `plans/review/cl-l6/` (not versioned). Its design notes
went with it: the roadmap's sections 3.1 to 3.7, and the UID and
performance plan for that kernel (`docs/certified-kernel-uids-plan.md`,
2026-09-30, never implemented), both removed on 2026-10-01. Since the vendored
con-leche tree moved under `Ix/Kernel/**` (2026-10-01), four of its module
names are reused (`Ix.Kernel.Env`, `Ix.Kernel.Expr`, `Ix.Kernel.Level` and
the directory `Ix/Kernel/Model/`, with different contents), as is the axiom
test's path `Tests/Ix/Kernel/Axioms.lean`; `scripts/check-kernel-retirement.py`
rejects the intrinsic names that are not reused, and the reused paths are
guarded by provenance (every Lean file there is a hash-pinned row).

## Removal ledger: lean4ix and Ix.Tc

Recorded at D01 (2026-09-29), before the con-leche port. Where it names
`Ix.Kernel` roots, audits and `check-kernel` job counts, it describes the
intrinsic kernel of that date; the current gate is described above.

D01 removed both dependency paths on 2026-09-29: the root Lake package
`lean4lean` fetched `argumentcomputer/lean4ix` at
`a4188d7c2979378d85c6bb41fdd96c3a48a71371`, and TruthMines independently
fetched `digama0/lean4lean` at `e0e3f6bcccb840cb0ea6f11c2b274ada93a12e00`.
The old verification trees and their consumers are gone. Runtime `Ix.Tc`
remains until D02's consumer and corpus-parity gates are satisfied.

| Retired or remaining surface | Replacement or disposition | Status |
| --- | --- | --- |
| `Ix/Tc/Verify/**` checker statements and proof frontier | Executed `Ix.Kernel` acceptance/model/fidelity roots and adversarial fixtures; behavior outside the supported profile remains in runtime tests | D01 complete |
| `Ix/Tc/Verify/Audit/{Basic,Completed,Conditional,Statements,SorryFrontier}.lean` | Kernel axiom/import/runtime audits supply strict checks and negative controls; obsolete upstream/native/sorry allowances were deleted | D01 complete |
| `Ix/Compile/Verify/{Codec,ExprCodec,ExprSpineCodec,ConstantCodec,ConstantTablesCodec,NonrecursiveConstantCodec,RecursorConstantCodec,MutualConstantCodec}.lean` | Preserved under `Ix/Ixon/Verify`, with complete wire domains, frozen contracts, and independent audits | D01 complete; old copies deleted |
| `Ix/Compile/Verify/{Catalog,IxonValue,SourceValue,Reference}.lean` | Structural predicates live in `Ix/Ixon/Wire`; K3 exact readings cover resolved values; the old semantic square is retired | D01 complete |
| Remaining `Ix/Compile/Verify/**`, including `Compile*`, `Arena`, `Sharing`, `Statements`, and its audits | Retired compiler/specification machinery; no Ix.Kernel compiler-correctness theorem is claimed | D01 complete |
| Root `lakefile.lean` / `lake-manifest.json` | Removed dependency, proof libraries, replay benchmark, proof loader, and `build-all` exception; Lake regenerated the manifest | D01 complete; all 24 remaining targets build strictly |
| `ix_ffi_dyn`, `crates/ffi-dyn`, workspace `Cargo.toml` / `Cargo.lock` | Removed the proof-only crate and loader; ordinary runtime FFI remains | D01 complete; Cargo regenerated the lockfile |
| `Benchmarks/Lean4Lean.lean`, `Benchmarks/Lean4LeanMain.lean`, `Tests/Ix/Lean4Lean.lean`, `Tests/Main.lean` | Removed replay library, executable, smoke runner and registration; fixture dispositions below | D01 complete |
| `Ix/Cli/BenchCmd.lean`, `Ix/BenchConstants.lean`, `docs/benchmarking.md` | Removed backend registry, dispatch, help, and active commands; measurements use the existing certified harness and Rust driver | D01 complete; removed backend exits 2 as unknown |
| `Benchmarks/TruthMinesSpec/{Catalog,Spec}.lean` | Removed package/member at the generator source | D01 complete; generator checks pass |
| `Benchmarks/TruthMines/{lakefile.lean,lake-manifest.json,Drivers/Lean4Lean.lean}` | Regenerated configuration without the independent upstream dependency; deleted the generated driver | D01 complete; 78 retained package entries |
| `Benchmarks/Compile/{lake-manifest.json,TruthMines/lake-manifest.json,TruthMines/Members/Lean4Lean.lean}` | Removed inherited package entries and generated member; retained unrelated pins | D01 complete; 24 and 80 retained package entries |
| `.github/workflows/merge-tests.yml`, `.github/workflows/ci.yml` | Removed old proof jobs and runner; the certified kernel/model/provenance/differential job covers PRs and merge groups; temporary runtime parity jobs remain | D01 complete |
| `flake.nix` | Removed dependency override; added the retirement source check and Python to development shells | D01 complete; native x86_64-linux Nix gate passes |
| `docs/ffi.md`, `docs/tc-k0-backedge-audit.md`, this ledger | Obsolete active commands retired; historical audit labeled explicitly; replacement guarantees stated below | D01 complete |
| `Ix/Tc.lean`, remaining `Ix/Tc/**`, `Tests/Ix/Tc/**`, CLI, AuxGen, IxVM claim harness, and validation round trips | Move consumers and behavior tests to their new owners; switch differential testing to Rust; delete Ix.Tc last | D02 pending after K3/K4 and K6 consumer parity |
| Kernel/model LICENSE and NOTICE; explanatory attribution in Rust, IxVM, tests and historical documentation | Retained; historical mentions are outside the active-reference guard | Preserved |

The final consumer scan confirmed that the proof loader was the only Lake
consumer of `ix_ffi_dyn`. The ordinary Rust `unsigned` implementation and
its runtime symbols remain in `ix-ffi`.

The retired dependency smoke test replayed `Nat.add_comm` and submitted an
axiom whose type was the natural-number literal zero. `Nat.add_comm` remains
the normal CI compiler/zkVM fixture; the certified suite separately covers
natural-number recursion/literals, non-type declared types, and unsupported
axioms. The arbitrary-axiom route declines under the current certified
profile, so this retirement does not claim the old smoke test's exact
acceptance/rejection behavior or full `Nat.add_comm` certified parity.

### Preserved and retired compiler contracts

| Old contract | Selected replacement | Explicit limits |
| --- | --- | --- |
| `deUniv_serUniv` | `Ix.Ixon.Verify.deUniv_serUniv` (implemented) | Compressed-successor and UInt64 wire bounds retained |
| `deExpr_serExpr` | `Ix.Ixon.Verify.deExpr_serExpr` (implemented) | Wire-sized vectors, spine counts, binder bits, and whole-buffer consumption retained |
| `deConstant_serConstant` | `Ix.Ixon.Verify.deConstant_serConstant`, plus `deConstantExact_serConstant` (implemented) | All variants and arbitrary side tables retained with count/address/table bounds |
| `Reads` / `Writes` | `Ix.Ixon.Verify.Codec` cursor and append laws (implemented) | Codec behavior only; exact consumption and suffix rejection added in `Verify.Framing` |
| `ExprTableWF`, decreasing sharing bounds, reference/universe table resolution | K3 checked resolution plus exact erasure to the supplied Ixon declaration | Detect bad indexes, missing payloads, sharing cycles/forward entries, and unsupported modes before certification |
| Binder-mode erasure relation | K3 explicit accepted mode policy and exact reading; K7 for nonstandard semantic modes | No Lean4Lean interpretation is retained as a hidden premise |
| Production compiler refinement/value-preservation and end-to-end semantic square | Retired as part of D01; a separate compiler-correctness project would need new source semantics and proofs | Ix.Kernel acceptance does not prove that the compiler preserved the original Lean declaration |

The retained codec chain imports the pure structural `wireWF` predicates,
so the former `ExprSpineCodec → Catalog → IxonValue → Lean4Lean` dependency
is gone. The temporary old copies have been deleted. Retained codec roots
use only the three standard axioms; native hash/name allowances from the
old compiler proofs are not inherited. K4's resource bounds, validity,
canonicality, and byte-admission composition remain open.

### D01 validation and recurrence guard

`python3 scripts/check-kernel-retirement.py` runs before `check-kernel`
and as a Nix check. It checks tracked Lean code (including `public import`,
`import all`, and multiline imports), every tracked Lake manifest, and
active build/CI/Nix/Cargo/generator configuration. Nested Lean comments,
historical documentation, and legal attribution are preserved. Negative
controls cover import forms, aliased repository URLs, stale target/crate
names, retired paths, and malformed manifests. A source-export walk covers
Nix builds without VCS metadata.

Validation used a fresh jj workspace with no project Lean artifacts and no
Lean4Lean package. Only retained pinned third-party package caches and the
Rust artifact cache were reused. All 24 host library/executable targets
passed `lake lint -- --wfail`; default tests (including TruthMines records,
benchmark measures, runtime Tc, and FFI), CLI tests, generator checks, and
the explicit removed-backend/help checks passed. The regenerated TruthMines
Lake configuration compiled. Lake's manifest reader/writer removed the
three nested entries while retaining every other entry and revision; no
unrelated package pin changed. This validates corpus configuration, not a
build or parity sweep of all retained corpus packages.

`lake run check-kernel --with-model` passed: 164 standalone, 173 host
fixture/provenance, 529 runner, and 975 model jobs; 38 differential cases,
26 compiler ingress/exact-egress cases, and the production codec property
tests with Rust comparisons. Provenance remains 97 ported, 53 authored or
reorganized modules, and four license files. Public statements and audit
allowlists are unchanged.

The x86_64-linux Nix gate used immutable source snapshot
`a829f6d86f49dec0acb9447da014bf76b32ab9ec`, with no workspace caches in the
source. The library, packaged Lean tests, retirement guard, clippy, nextest,
and distributable CLI smoke check passed. Nextest ran 1,533 tests with
1,533 passes and 14 skips. Other operating systems were not tested.
The final checkpoint differs from that tested snapshot only in this ledger
and the roadmap's completion notes.
The remaining Rust workspace also passed the local locked release
all-target build and clippy checks with `parallel,net,test-ffi` enabled,
and the default-feature workspace tests and doc tests.

D02 still requires no active `Ix.Tc` dependency and the documented consumer
parity corpus, including the ordered-reference policy. Dependency
retirement does not complete the runtime cutover.
