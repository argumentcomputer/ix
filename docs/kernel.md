# Certified Lean kernel

Ix's certified checker, `Ix.Kernel.Cached.checkDecls` at `.verified`, is
derived from [con-leche](https://github.com/leanprover/con-leche)'s verified
checker: `Ix/Kernel/**` holds a modified copy under the namespace
`Ix.Kernel` (see "Origin and attribution" below), run on Ixon records by Ix's
reader in `Ix/Kernel/Ixon/`. The certified API is
`Ix.Kernel.Admission.checkBytes` (`import Ix.Kernel.Admission`; its theorems
are in `Ix.Kernel.Admission.Theorems`). This page states what that entry does, what
is proved about it, what is trusted, how the gate checks the trust boundary,
where the kernel comes from, and how to check a whole compiled environment.
This page is the contract: what an accept promises (a set-theoretic model,
no constant of the pinned `False`, the checked declarations are the ones
the bytes encode, bounded resources), under which assumptions (an
`Ix.Kernel.SetTheory V`; proofs on `propext`, `Classical.choice` and
`Quot.sound` only), on which execution foundation ("Trust surface"), and
with which outcomes (accept, reject, decline; only an accept carries the
theorems).

Nothing here certifies the Lean-to-Ixon compiler, the Rust checker, `Ix.Tc`
or IxVM. An accepted environment has a model; that it is the environment
the original Lean source meant is outside the claim.

## The certified entry

```lean
def Ix.Kernel.Admission.checkBytes (limits : Limits) (records : Records)
    (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error Ix.Kernel.Env
```

Each entry has one runnable module, which holds definitions only, and its
theorems and audit beside it: `Ix/Kernel/Admission.lean` (the entry, its
`Error` and `Outcome`), `Ix/Kernel/Admission/Bytes.lean` (the byte stage
and its `ByteError`), `Ix/Kernel/Admission/{Theorems,Bytes/Theorems,
Audit}.lean`; the variants `Ix/Ixon/{Projection,BlockOrder}.lean` with
`Ix/Ixon/{Projection,BlockOrder}/{Theorems,Audit}.lean`. Running the entry
does not build the proof tree: the import closure of
`Ix.Kernel.Admission` is 76 repository modules and does not reach
`Ix.Kernel.MainTheorem`.

`records` is an ordered list of `(Address, ByteArray)` pairs, one canonical
Ixon v4 constant payload per pair (the bytes of one `Ixon.Constant`, without
an environment header); `blobs` holds literal payloads (`Nat` little-endian
bytes, `String` UTF-8 bytes) by address; `hint` is an optional, untrusted
reducibility hint per constant. The entry takes no format version: a payload
is read as Ixon v4, and the host's `.ixe` readers, which supply the payloads
of a compiled environment, reject a file of any other version by its header.
The entry runs, in order:

| Stage | Function | Fails with |
| --- | --- | --- |
| the committed pin table, prelude and Nat-operation pins load | `defaultPins`, `builtinPrelude`, `builtinNatOpPins` | `.prelude reason` |
| batch limits: record and blob counts, total payload bytes | `Admission.preflight` | `.limit resource` |
| key uniqueness: no two records and no two blobs under one address | `Admission.uniqueKeys` | `.duplicate table position address` |
| canonical per-record decoding within byte and universe-node limits | `Admission.decodeRecords` | `.decode position address reason` |
| the Ixon reader: records to `Array Ix.Kernel.Declaration` | `Reader.readRecords` | `.read position (.malformed _ / .declined _)` |
| the prelude is put in front (`Ix.Kernel.Frontend.preparePrelude`) | | |
| the verified fold | `Ix.Kernel.Cached.checkDecls .verified natPins` | `.kernel error position` |

The pipeline is `Ix.Kernel.Admission.checkBytes`; `checkBytesWith`
takes the pin table, prelude and Nat-operation pin list as parameters, and
`checkConstants{,With}` start from decoded records. Two variants share the
byte stage and the checker: `Ixon.Projection.checkBytes` reconstructs
omitted projection records (addresses by pure BLAKE3 of their canonical
bytes) before checking, and `Ixon.BlockOrder.checkBytes` also checks the
order of mutual blocks: an inductive, definition or mixed block in canonical
structural order (`canonicalClasses`, as Rust's `canonical_check.rs`), a block
of recursors in motive order (member `j` eliminates motive `j`, read off its
type as the reader reads it, `recursorMotive_of_analyse`), which is the order
the compiler stores it in and not always the structural one (a structural
check would refuse 2 of the 7 compiled recursor blocks of the fidelity
fixture, `Rose.rec`/`Rose.rec_1` and `Args.rec`/`Tm.rec`).

**Outcomes.** `Admission.Error.outcome` (called as `e.outcome`) classifies
every failure as a reject (the input is wrong) or a decline (the checker
does not certify it):

| Error | Outcome | Why |
| --- | --- | --- |
| `.limit` | decline | a coverage bound, not evidence about the input |
| `.duplicate`, `.decode` | reject | the bytes are malformed |
| `.read _ (.malformed _)` | reject | the records describe no declaration (a missing reference or blob, a bad table index, a recursor header that disagrees with its block, ...) |
| `.read _ (.declined _)` | decline | unsupported: unsafe or `partial` definitions, unsafe axioms, an inductive block whose recursor is not in the input, a mutually recursive definition block, a block the in-process modeller declines |
| `.prelude` | decline | a corrupted committed table |
| `.kernel` | decline | every checker verdict: the checker reports fuel exhaustion as `internal` and a failed conversion search as `invalid`, and neither is independent evidence that the input is wrong |

The variants keep their own errors (`Ixon.Projection.CheckError`,
`Ixon.BlockOrder.CheckError`) and the same classifier, `e.outcome`: a
checker failure (`.checker e`) as above, the byte stage
(`Admission.ByteError.outcome`) as `.limit`, `.duplicate` and `.decode`
above, and their own failures as follows.

| Error | Outcome | Why |
| --- | --- | --- |
| `Projection.Error.limit`, `BlockOrder.Error.exhausted` | decline | coverage bounds (projection requests; comparison and refinement fuel) |
| `Projection.Error.ownerWidth`, `.conflict`, `.projection (.malformed _)` | reject | an owner key that is not a 32-byte hash, a supplied record that differs from the derived one at its key, a projection the writer finds malformed |
| `Projection.Error.projection` (any other search failure) | decline | the writer did not establish the projection |
| `BlockOrder.Error.malformed`, `.nonCanonical`, `.motiveOrder` | reject | a malformed block, or a block out of canonical (or motive) order |

Only an accept carries the theorems below.

**Host obligations.** The host supplies the order, the address keys and the
blobs. Addresses are keys, not authenticated hashes (only the projection
variant derives addresses). The entry does not reorder beyond
`preparePrelude`: each record must follow the records it references; a
record that contains a literal must follow the constants the literal names
(`Reader.literalEdges`: the `Nat` block, and for a string literal
`String`, `String.ofList`, `List`, `Char`, `Char.ofNat`); a pinned `Nat`
operation must follow its certificate ground. A host order that violates
this declines; it cannot cause an unsound accept. The environment check's
order (`Benchmarks/Kernel/CheckIxeStep.lean`, `order`) satisfies it.

## The theorems

All public theorems are in `Ix/Kernel/Admission/Theorems.lean` (namespace
`Ix.Kernel.Admission`), about the executed function `checkBytes`, at the
committed tables. Each follows from the corresponding theorem at
`checkBytesWith`, where it holds for every pin table, prelude and
Nat-operation pin list, so no theorem depends on how the tables were
generated. Every public and fidelity root depends on exactly `propext`,
`Classical.choice` and `Quot.sound`.

| Theorem (`Ix.Kernel.Admission.`) | Statement, for `h : checkBytes limits records blobs hint = .ok env` |
| --- | --- |
| `checkBytes_has_model` | `∀ V [Ix.Kernel.SetTheory V], Nonempty (Ix.Kernel.Model V env)` |
| `checkBytes_has_model_values` | there is a model `M` in which every stored `defnInfo cv value _` satisfies `Denotes M.cval env φ ρ value (M.cval cv.name φ)` for all `φ ρ` |
| `checkBytes_no_proof_of_False` | no `ci ∈ env.consts` has type `.const Ix.Kernel.falseName []` |
| `checkBytes_no_False_theorem` | no theorem record of the decoded input (`RecordsRead limits records constants`) has a type that the reader reads as `.const Ix.Kernel.falseName []` |
| `checkBytes_reading` | the tables load; `WithinBatch limits records blobs`; `UniqueKeys records blobs`; `RecordsRead limits records constants` for some `constants`; and `Installed pins pre natPins constants blobs hint env` |
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
consistency. Definition values come from the kernel's model invariant
`defn_reads` through `Ix.Kernel.Cached.checkDecls_model_defn_values`
(`Ix/Kernel/Ixon/Values.lean`). Theorem and opaque bodies have no value
equation, by upstream's design.

**Fidelity** is what `checkBytes_reading` adds to consistency:

- `WithinBatch` and `UniqueKeys` (`Ix/Kernel/Admission/Bytes/Theorems.lean`): the
  batch limits hold, and the record keys and the blob keys are each
  pairwise distinct (`preflight_ok_iff`, `uniqueKeys_ok_iff`).
- `RecordsRead`: each payload is the canonical encoding of its decoded
  constant within the per-record limits, keys unchanged
  (`decodeRecords_ok_iff`, unique by `RecordsRead.deterministic`).
  "Canonical encoding" is the codec's: the payload is the bytes the v4
  writer produces for the decoded constant. It is not a statement about the
  constant's sharing table (see "Sharing tables" below).
- `Installed` (`Ix/Kernel/Admission/Theorems.lean`): the reader's output is a
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
- `Ix.Kernel.Reader.keyName_injective` and `Ctx.nameOf_of_pin`/`Ctx.nameOf_of_unpinned`
  (`Ix/Kernel/Ixon/{Reader,ReaderSpec}.lean`): which name a reference
  is read under.

Not proved:

- that installed types and values equal the decoded ones. The checker
  installs the annotation of a declared term: binder regimes (`pw`) are
  computed (the reader emits `pw := .never`), `let` is ζ-reduced, and
  projections are checked. The intended statement is about `pw`-erasure and
  needs a lemma about the kernel's `installConstantVal`/`installValue`;
- the member-level reading of inductive blocks (member order, constructor
  and recursor headers, rule constructors) through `readInductive`;
- per-member completeness of definition blocks (`defOrder` is not proved to
  be a permutation);
- that the committed table pins Init's own constants. That is the
  generator's verification, not a theorem; the no-False theorems are stated
  at `falseName` and hold for any table.

The projection and block-order variants have the same shape:
`Ixon.Projection.checkBytes_{run_iff, ok_iff, of_expansion, reading,
has_model, no_proof_of_False}` and `Ixon.BlockOrder.checkBytes_{run_iff,
ok_iff, of_ordered, reading, has_model, no_proof_of_False}`, each with
`UniqueKeys` in its reading. The separate package `Models/SetTheory`
(Mathlib) provides `IxSetTheoryModel.zfSetTheoryOfCarneiro`, a
`Ix.Kernel.SetTheory ZFSet` instance under `OmegaInaccessibles`, and the
corollaries `IxSetTheoryModel.checkBytes_has_ZFSet_model` and
`IxSetTheoryModel.checkBytes_no_proof_of_False`.

**Assumptions.** Consistency is relative to `Ix.Kernel.SetTheory V`
(`Ix/Kernel/SetTheory/Core.lean`): membership with extensionality,
unordered pairs, unions, power sets, regularity, replacement as a
Lean-level scheme (the image of a set under any `V → V`), and a strictly
increasing ω-chain of Grothendieck universes interpreting the universe
tower. The Mathlib instance above supplies it from ω inaccessible
cardinals, which its corollaries take as a hypothesis, not as an axiom.

**Input policy.** The entry never falls back to `Ix.Tc` or the Rust
checker; neither is in its closure ("Trust surface"). An input may declare
Init's compiler-trust family (`Ix/Kernel/TrustAxioms.lean`):
`Lean.trustCompiler` installs as an opaque with value `True.intro`,
`Lean.reduceBool` and `Lean.reduceNat` as opaques whose stored values are
pinned against the identity (a drifted value declines), and
`Lean.ofReduceBool` and `Lean.ofReduceNat` as pinned axioms over them.
`sorryAx` is tolerated as a declaration and installs nothing; any use of it
declines (`Ix/Kernel/Core.lean`). The well-founded `Nat` operations are
admitted through pins and certificates the checker checks itself
("Nat-operation pins" below).

## Keys, pins and the prelude

**Records** are Ixon v4 constant payloads ([Ixon](Ixon.md), [Ixon v4](Ixon-v4.md)):
TagN integers, and a sharing table per constant. The reader consumes decoded
constants (`Ix.Ixon.Types`) and never sees the integer code; only the byte
stage (`Ix/Ixon/{Codec,Bounded/*,Canonical,WireCheck}.lean`) and its proofs
(`Ix/Ixon/Verify`, including the TagN laws in `Ix/Ixon/Verify/TagN.lean`) do.

**Sharing tables.** In Ixon v4 the table the compiler writes is canonical:
`Ix.Sharing.Exact.canonicalSharingTiered .tagN` of the constant's expanded
roots ([Ixon](Ixon.md), "Sharing System"). The certified entry does not check
that. It accepts any table whose entries refer only to earlier entries: the
reader expands every `Share` against the record's own table and rejects a
reference that is not to an earlier entry as malformed
(`Ix/Kernel/Ixon/Reader.lean`), so the declarations it reads do not depend
on which backward table the record carries. This is deliberate. Checking
canonicity would put the sharing construction `Ix.Sharing.Exact` (its `Std`
maps, the `@[csimp]` fast twins the compiler runs, and the `unsafe`
pointer-cache key `exprPtr`) into the certified closure, and no theorem
needs it. A record with a valid but non-canonical table is therefore read and
checked like any other; its address is not the one the compiler would give
the same constant, which matters only to a host that derives addresses (the
projection variant hashes the records it writes, which carry no table). A
check of table canonicity, if wanted, belongs in a separate variant, as the
block-order check is.

**Keys** (`Ix/Kernel/Ixon/Reader.lean`). The kernel's environment is keyed
by `Ix.Kernel.Name`. A reference `ConstRef Address` is encoded under the
reserved root `ix`: `.member b i` is `ix.<hex b>.i` and `.ctor b i c` is
`ix.<hex b>.i.c`, with numeric components (`keyName`, injective). Level
parameters are positional. Three kinds of names differ:

- recursors are named after what they eliminate, as Lean names them
  (`T.rec`, and `T.rec_j` for the `j`-th auxiliary motive of a nested
  block), because the checker finds a block's recursor by name;
- pinned references take their pinned name;
- the pinned standard-axiom constants and their recursors carry Lean's own
  level-parameter names (`Pins.levels`), because the checker's `matchesPin`
  compares them, and a large eliminator names its extra level parameter
  so that the checker recognises it.

**Pins** (`Ix/Kernel/Ixon/PinData.lean`, generated). The table maps 55
references to the checker's pinned names and no others: the basis (`Eq`,
`Nat`, `PUnit`, `Empty`, `False`, the `Quot` package), `And` and `Bool`, the
literal support (`String`, `String.ofList`, `List`, `Char`, `Char.ofNat`),
the structural and pin-certified `Nat` operations, the standard axioms with
`Iff` and `Nonempty`, the compiler-trust family with `True`, and `sorryAx`.
`pinMap` refuses a table that is not a partial injection or that uses the
`ix` root or a derived name shape. The table decides coverage only:
the checker compares every pinned name's declaration with its pinned shape
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

**Prelude** (`Ix/Kernel/Ixon/Prelude.lean`). The checker puts twelve
declarations in front of every fold (`preparePrelude`): the basis blocks `Eq`, `Nat`, `PUnit`,
`Empty`, `False`, the quotient package (four `Quot` constants and
`Quot.sound`), `And` and `Bool`. Here they are the compiled Init's own Ixon
records (`PinData.prelude`, canonical bytes by address), decoded by the
canonical decoder and read by the same reader. The empty stream installs
27 constants. A stream that declares a prelude constant is checked on its
own record (`preparePrelude` moves the stream's copy to the front); the
prelude's copy fills in where the stream has none.

**Regeneration.** Both tables come from `kernel-pin-gen`
(`Benchmarks/Kernel/PinGen.lean`), which checks every pinned
constant's record and the literal capabilities through the verified fold
before writing:

```sh
lake exe ix compile Benchmarks/Compile/CompileInitStd.lean --out .lake/envs/initstd.ixe
lake exe ix compile Ix/Kernel/PinGen/Certs.lean --out .lake/envs/certs.ixe --consts <the certificate theorems>
lake exe kernel-pin-gen .lake/envs/initstd.ixe .lake/envs/certs.ixe \
  Ix/Kernel/Ixon/PinData.lean Ix/Kernel/Ixon/NatOpPinData.lean
```

The full `--consts` list and the source hashes are in the generated files'
headers. The table names addresses, so a toolchain, compiler or format
change that moves Init's addresses requires regeneration: until then the moved
constants are not pinned and the inputs that need them (literals, the
pinned `Nat` operations, the standard axioms) decline. Soundness does not
depend on the table.

## Trust surface

The theorems are about the Lean functions. Trusted beneath them: Lean's
kernel, compiler and runtime, and the inherited `Init`/`Std` primitives the
compiled code reaches (the entry's closure reaches 121 inherited externs,
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
| elaboration-time `unsafe`, `implemented_by`, `meta import Lean` | `Ix.Kernel.BasisGen` | elaboration only; compiled code cannot reach them |
| `partial` | `Ix.Kernel.Frontend.InModel*` | the in-process modeller, as upstream con-leche has it |

Import allowlists (`Ix/Kernel/Audit/Roots.lean`):

- `kernelImportAllowlist`: `Init`, `Std`, `Ix.Kernel` (the checker and
  Ix's Ixon boundary), `Ix.Address.Core`, `Ix.Ixon.Types`. It fences
  the reader, the record store, the projection writer and the pure Ixon
  types.
- `importAllowlist` (the certified API's closure, rooted at
  `Ix.Kernel.Admission`): the above plus exactly `Ix.Ixon.{Codec, Wire,
  WireCheck, Bounded.Constant, Bounded.Universe, Canonical}`, without the
  entry's theorem and audit modules and the kernel's audits
  (`importDenylist`; `kernelImportDenylist` likewise keeps
  `Ix.Kernel.Admission` and `Ix.Kernel.Audit` out of the kernel-side list).
  No projection hashing, block order, `Ix.Address.Pure`,
  proof module or `Lean` (outside `elaborationImports`).
- `proofImportAllowlist` (the theorem modules): `importAllowlist` plus
  `Ix.Ixon.Bounded.Size`, `Ix.Ixon.Verify`, the theorem module and
  `Lean`.
- `elaborationImports`: below `Ix.Kernel.BasisGen` only `Init`, `Std`,
  `Lean` and `Ix.Kernel`.

`Std` is admitted for its maps and their lemmas, as the kernel uses them.

## Audits and fences

The audits are Lean modules that fail elaboration on a violation. They are
built by the strict standalone package `IxKernel/` (`lake -d IxKernel build
--wfail`, sources from the repository, no dependency beyond the toolchain).

| Module | Checks |
| --- | --- |
| `Ix/Kernel/Audit/Roots.lean` | presence of every root (`publicRoots` 15, `fidelityRoots` 16, the operations); each at exactly the three standard axioms (`#guard_kernel_axioms`); the import closures against the allowlists; frozen runtime closures with their rulings; frozen `#check` statements; a control showing the fold fails without the rulings |
| `Ix/Kernel/Admission/Audit.lean` | the byte stage's imports, closure and extern difference, its lemmas' axioms, and the public statements |
| `Ix/Ixon/Projection/Audit.lean`, `Ix/Ixon/BlockOrder/Audit.lean` | the variants' imports, closures, extern differences and statements, and the projection writer's guards |
| `Ix/Ixon/Audit.lean` | the codec's own import, runtime and axiom audit |
| `Models/SetTheory/IxSetTheoryModel/Audit.lean` | the model package's full dependency closure: standard axioms only |

Frozen runtime closures (compiled functions; inherited externs):

| Roots | Functions | Externs |
| --- | ---: | ---: |
| fold `Ix.Kernel.Cached.checkDecls` | 3022 | 83 |
| reader `readRecords`, `readStream` | 1886 | 82 |
| entry: `checkBytes{,With}`, `checkConstants{,With}` | 5295 | 121 |
| byte admission: `preflight`, `uniqueKeys`, `decodeRecords`, `checkBytes` | 5293 | 121 |
| projection: `address`, `reconstruct`, `Projection.checkBytes` | 5416 | 130 |
| block order: `checkBytes`, `canonicalClasses`, `compareExpr` | 5549 | 130 |

A frozen value or statement changes only deliberately: the change that
re-records it states why the closure or the statement moved.

`lake run check-kernel [--with-model]` is the gate. In order:

1. the strict `IxKernel` build with every audit;
2. the host build of the kernel tests (`Tests/Ix/Kernel/{ByteAdmission,
   Reader, CertifiedEntry, Projection, BlockOrder, Codec, ...}`),
   whose `#guard`s run at elaboration;
3. `kernel-codec` (production codec against Rust) and `kernel-order`
   (canonical block order against Rust);
4. with `--with-model`, the `Models/SetTheory` build and its audit;
5. `kernel-layering` (`Tests/Ix/Kernel/Layering.lean`, derived from
   con-leche's `tests/layering.sh`): the kernel's import layering, each file
   of `Ix/Kernel/` classified by its path (`Tests/Ix/Kernel/KernelLayout.lean`;
   an unclassified file fails): the checker never imports the theory, the
   base never imports the model lane, the rules fence and its five recorded
   doors, and the boundary: the checker and the theory import only
   themselves, `Init`, `Std` and, at elaboration time, `Lean` (Ix's
   boundary modules `Admission`, `Ixon`, `Audit`, `Ingress`, `Egress`, `Ref`
   and `Search` import the kernel, not the reverse);
6. `kernel-trust-surface` (`Tests/Ix/Kernel/TrustSurface.lean`, derived from
   con-leche's `tests/trust-surface.sh`, with its lexer self-test on
   `Tests/Fixtures/trust-surface/lexer.lean`): a lexer-based scan of the
   checker and the theory for compiler escapes (`unsafe`, `implemented_by`,
   `computed_field`, `native_decide`, `extern`, `sorry`, `axiom`, ...); 11 escapes in four
   allowlisted files (`Ix/Kernel/{Expr,Name,Exclusive,BasisGen}.lean`)
   are permitted, each with its justification in the tool's header;
7. `kernel-level-comparison`: the level comparison (`Level.leq`,
   `Level.isEquiv` and its Géran fallback) against brute-force evaluation,
   on random levels and on Ixon's canonical forms;
8. `kernel-entry-cases`: Lean declarations of
   `Tests/Ix/Kernel/EntryCaseDefs.lean` compiled by Ix's compiler and
   submitted as canonical bytes to `checkBytes`, each with an exact expected
   verdict (accepts: a definition, a theorem, an inductive with its
   recursor, a structure with a projection, a quotient reduction, `Nat`
   literals and a pinned `Nat` operation, a `String` literal, a nested
   inductive, a mutual inductive with definitions by structural recursion
   over it, a mutual and nested inductive, the opaque face of a `partial`
   definition; rejects: truncated
   bytes, a duplicate constant, a duplicate blob, `Nat.rec` with a wrong K
   flag; declines: `Nat.add` with another value, a `partial` definition's
   `_unsafe_rec` body, a non-standard axiom, a theorem of `False`). Rows go
   to `.lake/build/kernel-entry-cases.jsonl`;
9. `kernel-reader-fidelity --fixture` and `--check-kernel`: the Ixon reader
   against a direct translation of the Lean constants it was compiled from,
   and the projection output against the compiler's records, on the fixture
   closure (the check the `lake test` suite `kernel-reader-roundtrip` runs)
   and on the first records of Init and Std; the log goes to
   `.lake/build/kernel-reader-fidelity.log`.

The CI job runs the same gate and keeps the codec, order, entry-case and
reader-fidelity logs.

### On a toolchain bump

When `lean-toolchain` changes, by hand or by the toolchain bot
(`.github/workflows/update.yml`, which moves the toolchain files and the
Mathlib tag but regenerates nothing), the change also does the following.

1. **Toolchains.** `lean-toolchain`, `Benchmarks/Compile/lean-toolchain`,
   `IxKernel/lean-toolchain` and `Models/SetTheory/lean-toolchain` name the
   same release (CI's `lean-test` job compares them). The model's `mathlib`
   `rev` in `Models/SetTheory/lakefile.toml` is Mathlib's tag for that
   release; after changing it, `lake -d Models/SetTheory update mathlib`
   refreshes `Models/SetTheory/lake-manifest.json`.
2. **Pin tables.** A new toolchain moves Init's addresses: regenerate
   `PinData.lean` and `NatOpPinData.lean` with the three commands under
   "Regeneration" above (the full `--consts` list is in the generated
   headers). Until then the moved constants are not pinned, and the
   inputs and entry cases that need them decline.
3. **Frozen audit records.** The runtime closures (`N compiled functions;
   inherited externs M, ...`), the extern differences and the frozen
   `#check` statements are `#guard_msgs` records in
   `Ix/Kernel/Audit/Roots.lean`, `Ix/Ixon/Audit.lean` and
   `Ix/Kernel/Admission/Audit.lean` (built by `lake -d IxKernel build
   --wfail`), and in `Ix/Ixon/Projection/Audit.lean` and
   `Ix/Ixon/BlockOrder/Audit.lean` (built by `lake build --wfail
   Ix.Ixon.Projection.Audit Ix.Ixon.BlockOrder.Audit`). A record that no
   longer matches fails the build and prints the message its command now
   produces; re-record it by replacing the record's docstring with that
   message, and update the closure table above and the counts in
   `Roots.lean`'s module docstring. Any other `#guard_msgs` that fails (the
   controls in `Ix/Kernel/Audit/Runtime.lean`, the axiom records in
   `Tests/Ix/Kernel/Axioms.lean`) is re-recorded the same way. A changed
   closure **count** is accepted only with its explanation: the change that
   re-records it states what entered or left the closure and why.
4. **Gate.** `lake run check-kernel --with-model` passes in full.

### On a format change

A change of the Ixon wire format (a new `Ixon.Env.VERSION`, as from v3 to
v4) moves essentially every address: an integer whose bytes change, or a
different sharing table, changes a constant's hash, and addresses propagate
through references. The readers reject files of another version, so every
stored artifact is regenerated, not converted. The change does everything a
toolchain bump does, in this order, with the format-specific steps
interleaved:

1. **Codec proofs.** `Ix/Ixon/Verify` proves the codec the byte stage runs.
   Re-prove it for the new grammar keeping the name and statement of every
   lemma used outside `Ix/Ixon/Verify` (the `#check` records in
   `Ix/Ixon/Audit.lean` list them; the byte stage's theorems in
   `Ix/Kernel/Admission/Bytes/Theorems.lean` must then build unchanged).
   `lake -d IxKernel build --wfail IxKernel` is the acceptance.
2. **Primitive addresses.** `lake exe ixon-v4-primitives` compiles the
   primitive closure into `$IX_IXON_V4_DIR` and fails if
   `Tests/Fixtures/ixon-v4/primitives.tsv` differs from the live addresses;
   copy the file it names over the fixture. Mirror every changed address
   into `crates/common/src/prim_addrs.rs` (`PrimAddrs::new`),
   `Ix/Tc/Primitive.lean` and the IxVM literals in `Ix/IxVM/Kernel/*.lean`
   (search each old address in hex and in 32-byte array form). The suites
   `prim-addrs` and `primitive-address-parity` and
   `lake exe ixon-v4-tests --primitives` must pass.
3. **Generated IxVM Rust.** `lake exe ix codegen` regenerates
   `crates/ixvm-codegen/src/*.rs` from the IxVM sources (the literals of step
   2 among them); `lake exe ix codegen --check` must pass.
4. **Fixtures.** `lake exe ixon-v4-tests --export-fixtures --export-handoff`
   writes `claims.tsv`, `addressed.tsv`, `resource.tsv` and the handoff set
   to `$IX_IXON_V4_DIR`; copy them into `Tests/Fixtures/ixon-v4/` after
   `lake exe ixon-v4-tests` validates them. If they moved, so did the
   catalog claim digest (`Tests/Ix/Claim.lean`, `crates/ixon/src/proof.rs`)
   and the environment-bytes hash (`crates/compile/src/graph.rs`); re-pin
   them from the serializers' output. The independent expression vectors
   (`Tests/Fixtures/ixon-v4/expressions.txt`) are written by hand from the
   specification.
5. **Pin tables**, as step 2 of a toolchain bump: the three commands under
   "Regeneration" above. Write the two environments to fresh files, never
   to paths that are symbolic links to another format's stored environments:
   the commands write through a link.
6. **The reader test's frozen records.** `Tests/Ix/Kernel/Reader.lean`
   holds compiled records as bytes. `lake exe kernel-entry-cases --records
   nested-through-nested` and `--records level-comparison` print them
   (`lTreeRecords`, `levelRecords`) with the names of the blocks they
   belong to; replace the lists and the owner addresses with the output. The
   byte vectors of `Tests/Ix/Kernel/{Codec,ParserWork,ByteAdmission}.lean`
   are the codec's: rewrite them for the new grammar (`kernel-codec`
   compares the Lean codec with Rust's on them).
7. **IxVM costs.** `lake test --wfail -- --ignored ixvm` reports every
   kernel-check FFT-cost pin of `Tests/Ix/IxVM.lean` and the shard pin in
   `Tests/Main.lean` that moved; set each to the measured value.
8. **Frozen audit records**, as step 3 of a toolchain bump, including the
   codec's own closure in `Ix/Ixon/Audit.lean`.
9. **Stored environments.** Recompile every `.ixe` the documentation's
   measurements use (`Benchmarks/Compile/CompileInitStd.lean`,
   `CompileMathlib.lean`), and compare environment-check rows with the
   previous format's by name, not by address.
10. **Gate.** `lake run check-kernel --with-model`, `lake test --wfail`, and
    `lake exe ixon-v4-primitives && lake exe ixon-v4-tests --primitives`.

Version-pinned external artifacts (a benchmark artifact pinned by hash, a
dated proof fixture) cannot be regenerated without their inputs; they stay
pinned and are rejected by the new readers, never misread.

## Origin and attribution

[Con-leche](https://github.com/leanprover/con-leche) is a Lean kernel
checker written in Lean whose acceptance is proved to imply consistency:
`ConLeche.model_exists` gives every environment its fold accepts a model in
any set theory implementing its `SetTheory` interface, on the three standard
axioms. Ix's kernel is derived from it, is maintained here, and is expected
to diverge from upstream.

**What was taken.** 452 Lean modules of con-leche's `ConLeche/` tree, the
import closure of `model_exists`, the eight frontend modules the reader
calls and `Verify/Cached/StreamThm.lean`, from
`https://github.com/leanprover/con-leche.git` at
`ae0c0c4e4ce6a0081648aff03fe9c39d002c4526`; seven of them (the files
upstream task #323 changed) at `3ca9e2fe749a51cba4c6e3527aeecba074c29316`.
The axiom pin `Tests/Ix/Kernel/Axioms.lean` is derived from upstream's
`tests/ConLecheTests/Axioms.lean`. Upstream's
`ConLeche/Kernel/NatOpPins.lean` is not included: Ix's Nat-operation pins
are generated from Ixon records (`Ix/Kernel/Ixon/NatOpPinData.lean`).

**What was changed.** Every file was moved (`ConLeche/Kernel/X` and
`ConLeche/X` to `Ix/Kernel/X`) and its namespace and module prefix renamed
(`ConLeche.Kernel` and `ConLeche` to `Ix.Kernel`, as whole names). Seven
files carry further changes:

| File | Change | Why |
| --- | --- | --- |
| `Ix/Kernel/CheckerBase.lean` | imports `NatOpPinSet` instead of `NatOpPins` | upstream's `NatOpPins` splices JSON pin dumps; Ix's pins come from Ixon records |
| `Ix/Kernel/Verify/Cached/{AgreeFloor,PushChain}.lean` | `import all Init.LetFun` | Lean 4.34.0 no longer exposes `letFun`'s body, which these proofs unfold |
| `Ix/Kernel/Frontend/InModel/Nested.lean` | container groups formed largest family first | Ix's compiler orders a nested block's auxiliary motives canonically |
| `Ix/Kernel/Level.lean`, `Ix/Kernel/Verify/Level.lean` | the `(param, max)` case falls back on Géran's sublevels, with its soundness case | nanoda's comparison is incomplete there, and Ixon's canonical levels reach the gap (Mathlib's `RatFunc.liftOn_def`) |
| `Ix/Kernel/MainTheorem.lean` | only `model_exists` kept | the NDJSON corollary needs a frontend Ix does not use |

Ix's own files under `Ix/Kernel/` are `Admission.lean` and the `Admission`
directory (the certified entry, its byte stage, theorems and audit),
`Ref.lean`, `Search.lean`, the `Audit`, `Ingress`, `Egress` and `Ixon`
directories (the Ixon reader and its specification, the committed pins and
prelude, the record store, the projection writer and the audits), and
`LevelGeran.lean` and
`Verify/LevelGeran.lean` (Géran's sublevels and their soundness and
completeness), which the changed `Level` files import.

**Notices.** `Ix/Kernel/LICENSE-CON-LECHE` is con-leche's Apache-2.0 licence
and `Ix/Kernel/NOTICE` states the origin, the revisions and the changes;
`Models/SetTheory` carries its own copy for the file it takes from con-leche.

**Builds.** All of `Ix/Kernel` is one library, `IxKernelTree`, in both
`lakefile.lean` and `IxKernel/lakefile.lean`, for one option:
`linter.deprecated` is off, so the con-leche-derived sources, written for
Lean 4.33.0, build under `--wfail` on 4.34.0 without renaming the deprecated
`if_pos`/`if_neg`/`dif_pos`/`dif_neg` lemmas they use (2,885 uses in 209
files). Ix's own files there do not rely on it: they build without warnings
with the linter on.

**Bringing over an upstream change.** By hand: take upstream's diff between
the recorded revision and the new one for the files concerned, map its
paths (`ConLeche/Kernel/X` and `ConLeche/X` to `Ix/Kernel/X`) and names
(`ConLeche` to `Ix.Kernel`), apply it, update the revisions in
`Ix/Kernel/NOTICE`, and run the full gate. A module the closure newly
imports is added the same way. A changed closure moves the frozen counts;
re-record each with its explanation, and re-record changed statements.

## Environment check

The environment check measures coverage on a compiled environment (an
`.ixe`); it is not a certified verdict. `kernel-check-ixe`
(`Benchmarks/Kernel/CheckIxe.lean`, entry `CheckIxeMain.lean`) reads an
`.ixe`, orders its primary constants (the prelude's first, then dependencies,
`Nat`-operation grounds and literal edges), reads each constant with the Ixon
reader and installs and checks it one constant at a time with an incremental
step of the verified fold (`Benchmarks/Kernel/CheckIxeStep.lean`),
continuing past failures and reporting dependents of a failure as blocked.
Hints are the compiler's. Each row is JSON (`address, names, kind, outcome,
reason, micros, readMicros`).

```sh
lake build --wfail kernel-check-ixe
lake exe ix compile Benchmarks/Compile/CompileInitStd.lean --out .lake/envs/initstd.ixe
CHECK_IXE_WATCH_MB=12000 .lake/build/bin/kernel-check-ixe --guarded --memory-max 24 \
  .lake/envs/initstd.ixe .lake/envs/initstd.jsonl
.lake/build/bin/kernel-check-ixe --report .lake/envs/initstd.jsonl
```

Usage: `kernel-check-ixe [--load stream|eager] [--jobs <n>] <input.ixe>
<output.jsonl> [limit]`. The records are streamed by default
(`Benchmarks/Kernel/CheckIxeStream.lean`): the order and the record views
are built over record skeletons, and each record is decoded in full at its
turn and dropped once it is read. `--load eager` decodes and keeps the whole
environment up front. `--jobs <n>` installs every record first and then runs
the recorded checks on `n` worker threads
(`Benchmarks/Kernel/CheckIxePool.lean`). All three write the same rows
(`kernel-check-ixe --compare` shows it); with `--jobs`, a row's `micros` is
its install plus its checks. Environment:

- `CHECK_IXE_WATCH_MS` (default 60000) and `CHECK_IXE_WATCH_MB` (default 20000):
  a watchdog ends the run with exit code 3 when one constant's check exceeds
  the time or the process's resident memory exceeds the size, and appends
  the constant's address to `<output>.runaway` (with `--jobs`, every
  worker's check is watched). The resident size includes what the driver
  holds of the environment. Measured peaks: Init+Std 1.5 GB streaming and
  3.6 GB with `--load eager`; Mathlib 14.7 GB streaming (15.7 GB with
  `--jobs 32`) and 34.2 GB with `--load eager`
  (`Benchmarks/Kernel/README.md`). `CHECK_IXE_WATCH_MB` must exceed the
  run's peak, or the watchdog fires before the check ends: the default
  covers every streaming run, including Mathlib's; an eager Mathlib run
  needs more (for example `CHECK_IXE_WATCH_MB=60000`, under a `MemoryMax`
  above that);
- `CHECK_IXE_SKIP` (comma-separated addresses) declines those constants
  unchecked; `kernel-check-ixe --guarded` reruns with every recorded runaway
  skipped until the run completes (`--memory-max <GB>` runs each attempt in
  a memory-capped cgroup scope, `Ix.Watchdog`);
- `CHECK_IXE_ROOTS` (comma-separated Lean names) restricts the run to the
  prelude and the dependency closure of those constants;
- `CHECK_IXE_THREAD=0` runs the check on the main thread instead of a
  dedicated one, and `CHECK_IXE_READ_CACHE=<dir>` keeps a persistent read
  cache (`Benchmarks/Kernel/CheckIxeReadCache.lean`).

Run one environment check at a time, under a memory cap, with no concurrent build.
`kernel-check-ixe --report` and `--summary` summarize a run's rows, and
`--compare` and `--paired` compare runs (`Benchmarks/Kernel/README.md`).
Mathlib's `.ixe` comes from `Benchmarks/Compile/CompileMathlib.lean`
(`Benchmarks/Compile/README.md`).

## The retired intrinsic kernel

Before the con-leche-derived checker, this branch's certified checker was an
intrinsic, proof-carrying kernel in `Ix/Kernel/**` (`Ix.Kernel.check`,
`checkDecls`, `checkEnv`), built on a set model and syntax ported from the
Ix branch `jcb/ix-kernel-consistency` at `ad60e5f6` (with con-leche's
`SetTheory` at `86cd20a6`). Each admitted declaration constructed its model
extension (`StepClaim`, `AdmissionClaim`); the public theorems were
`check_has_model`, the conditional `checkDecls_has_model`, a semantic
`no_proof_of_False` over `Env.EmptyType`, installation fidelity
(`Ingress.Installed`) and `checkBytes_unique_keys`. Its supported profile
covered single definitions, theorems and opaques, ordinary inductive
families with supplied recursors, structures, `Nat`, equality, quotients
and the two standard axioms, and declined arbitrary axioms, unsafe and
partial declarations, and general mutual and nested inductives. It was
deleted (132 files, 29,805 lines) with its entry points, 19 test modules,
environment check, benchmark and host differentials (25 files, 4,080
lines); it never reached `main`. Its level normalizer is the source of
`Ix/Kernel/LevelGeran.lean`'s algorithm.

## Removal ledger: lean4ix and Ix.Tc

This ledger records what was removed from `main` with the lean4ix/Lean4Lean
dependency and the `Ix.Tc` and `Ix.Compile` verification trees, and what
replaced each part. The codec proofs and the proofs of the canonical sharing
construction were kept and moved, not removed (the rows below say where).
Where it names `Ix.Kernel` roots, audits or fixtures, it describes the
retired intrinsic kernel (above); the current gate is described above.

Both dependency paths are removed: the root Lake package `lean4lean`
fetched `argumentcomputer/lean4ix` at
`a4188d7c2979378d85c6bb41fdd96c3a48a71371`, and TruthMines independently
fetched `digama0/lean4lean` at `e0e3f6bcccb840cb0ea6f11c2b274ada93a12e00`.
The old verification trees and their consumers are gone; runtime `Ix.Tc`
is unchanged.

| Retired or remaining surface | Replacement or disposition | Status |
| --- | --- | --- |
| `Ix/Tc/Verify/**` checker statements and proof frontier | Executed `Ix.Kernel` acceptance/model/fidelity roots and adversarial fixtures; behavior outside the supported profile remains in runtime tests | Done |
| `Ix/Tc/Verify/Audit/{Basic,Completed,Conditional,Statements,SorryFrontier}.lean` | Kernel axiom/import/runtime audits supply strict checks and negative controls; obsolete upstream/native/sorry allowances were deleted | Done |
| `Ix/Compile/Verify/{Codec,ExprCodec,ExprSpineCodec,ConstantCodec,ConstantTablesCodec,NonrecursiveConstantCodec,RecursorConstantCodec,MutualConstantCodec}.lean` | Preserved under `Ix/Ixon/Verify` (`Basic`, `Expr`, `ExprSpine`, `Constant`, `ConstantTables`, `NonrecursiveConstant`, `RecursorConstant`, `MutualConstant`), for the Ixon v4 codec, with complete wire domains, frozen contracts, and independent audits | Done; old copies deleted |
| `Ix/Compile/Verify/TagN.lean` (the TagN bijection and rejection laws) | `Ix/Ixon/Verify/TagN.lean` (namespace `Ixon.Verify.TagN`), built with the codec proofs by `lake -d IxKernel build --wfail` | Done |
| `Ix/Compile/Verify/{SharingExact,SharingExactCanon,SharingExactPasses}.lean`, `Tiered*`, `Uniform*` and `Audit/CompiledCode.lean` (the canonical sharing construction) | Moved to `Ix/Sharing/Verify` (namespace `Ix.Sharing.Verify`; deprecated lemma names replaced for Lean 4.34.0; no statement changed), library `IxSharingVerify` (`lake build --wfail IxSharingVerify`, also built by `lake lint`); audits `Ix/Sharing/Verify/Audit/{Statements,SorryFrontier,CompiledCode}.lean` | Done; no theorem of these files dropped |
| `Ix/Compile/Verify/CompileSharingCodec.lean` | Its builder part (`buildConstantWithSharing_wireWF`, `SharingRunOK`, the singleton-driver tail) is `Ix/Sharing/Verify/Builder.lean`; its expression-compilation roundtrips are retired with the compiler chain they rest on | Done |
| `Ix/Compile/Verify/{Catalog,IxonValue,SourceValue,Reference}.lean` | Structural predicates live in `Ix/Ixon/Wire`; the intrinsic kernel's exact readings covered resolved values; the old semantic square is retired | Done |
| Remaining `Ix/Compile/Verify/**`, including `Compile*` (the per-declaration compiler endpoint theorems among them), `Arena`, the former heuristic `Sharing`, `Statements`, and its audits | Retired compiler/specification machinery; no Ix.Kernel compiler-correctness theorem is claimed | Done |
| Root `lakefile.lean` / `lake-manifest.json` | Removed dependency, proof libraries, replay benchmark, proof loader, and `build-all` exception; Lake regenerated the manifest | Done; the remaining targets build strictly |
| `ix_ffi_dyn`, `crates/ffi-dyn`, workspace `Cargo.toml` / `Cargo.lock` | Removed the proof-only crate and loader; ordinary runtime FFI remains | Done; Cargo regenerated the lockfile |
| `Benchmarks/Lean4Lean.lean`, `Benchmarks/Lean4LeanMain.lean`, `Tests/Ix/Lean4Lean.lean`, `Tests/Main.lean` | Removed replay library, executable, smoke runner and registration; fixture dispositions below | Done |
| `Ix/Cli/BenchCmd.lean`, `Ix/BenchConstants.lean`, `docs/benchmarking.md` | Removed backend registry, dispatch, help, and active commands; measurements use the existing certified harness and Rust driver | Done; removed backend exits 2 as unknown |
| `Benchmarks/TruthMinesSpec/{Catalog,Spec}.lean` | Removed package/member at the generator source | Done; generator checks pass |
| `Benchmarks/TruthMines/{lakefile.lean,lake-manifest.json,Drivers/Lean4Lean.lean}` | Regenerated configuration without the independent upstream dependency; deleted the generated driver | Done; 78 retained package entries |
| `Benchmarks/Compile/{lake-manifest.json,TruthMines/lake-manifest.json,TruthMines/Members/Lean4Lean.lean}` | Removed inherited package entries and generated member; retained unrelated pins | Done; 24 and 80 retained package entries |
| `.github/workflows/merge-tests.yml`, `.github/workflows/ci.yml` | Removed old proof jobs and runner; the `certified-kernel` job covers PRs and merge groups; runtime parity jobs remain | Done |
| `flake.nix` | Removed dependency override | Done |
| `docs/ffi.md`, `docs/tc-k0-backedge-audit.md`, this ledger | Obsolete active commands retired; historical audit labeled explicitly; replacement guarantees stated below | Done |
| Explanatory attribution in Rust, IxVM, tests and historical documentation | Retained | Preserved |

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
| `deUniv_serUniv` | `Ixon.Verify.deUniv_serUniv` (implemented) | Compressed-successor and UInt64 wire bounds retained |
| `deExpr_serExpr` | `Ixon.Verify.deExpr_serExpr` (implemented) | Wire-sized vectors, spine counts, binder bits, and whole-buffer consumption retained |
| `deConstant_serConstant` | `Ixon.Verify.deConstant_serConstant`, plus `deConstantExact_serConstant` (implemented) | All variants and arbitrary side tables retained with count/address/table bounds |
| `Reads` / `Writes` | `Ixon.Verify.Codec` cursor and append laws (implemented) | Codec behavior only; exact consumption and suffix rejection added in `Verify.Framing` |
| Tag0/Tag2/Tag4 integer laws and their minimal-width checks | the TagN writer and reader laws `Ixon.Verify.Codec.{putTagN_writes, getTagN_reads}` over the byte specification `tagNBytes` (`Ix/Ixon/Verify/Basic.lean`), and `Ixon.Verify.TagN`: `runGetExact_getTagN_iff` (a read succeeds exactly on the written bytes), `putTagN_inj`, `getTagN_rejects_code`, `getTagN_rejects_overflow` (implemented) | Ixon v4 has one integer code, and it is bijective, so no minimal-width check remains |
| `ExprTableWF`, decreasing sharing bounds, reference/universe table resolution | Checked resolution in the canonical decoder and the Ixon reader (a bad index or a missing payload is a malformed record) | Detect bad indexes, missing payloads, sharing cycles/forward entries, and unsupported modes before certification |
| Binder-mode erasure relation | An explicit accepted mode policy: the Ixon reader erases binder contracts | No Lean4Lean interpretation is retained as a hidden premise |
| Production compiler refinement/value-preservation and end-to-end semantic square | Retired; a separate compiler-correctness project would need new source semantics and proofs | Ix.Kernel acceptance does not prove that the compiler preserved the original Lean declaration |

These contracts are stated about the Ixon v4 codec (TagN integers), with the
same names and statements as for v3, as is every codec lemma the byte stage
uses. The byte stage's resource proofs (`Ix/Ixon/Verify/Work*`,
`ReaderBounds`, `ConstantBounds`) charge a TagN read at most two units per
consumed byte, which the per-byte budget of `Work.Costs` covers, so
`checkBytes_resources` has the same statement.

The retained codec chain imports the pure structural `wireWF` predicates,
so the former `ExprSpineCodec → Catalog → IxonValue → Lean4Lean` dependency
is gone. The temporary old copies have been deleted. Retained codec roots
use only the three standard axioms; native hash/name allowances from the
old compiler proofs are not inherited. For the certified entry, the
resource bound, canonical decoding and the byte-admission composition are
proved (`checkBytes_resources`, `decodeRecords_ok_iff`,
`Ix/Kernel/Admission/Bytes/Theorems.lean`).
