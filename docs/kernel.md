# Certified Lean kernel

Ix's certified checker, `Ix.Kernel.Cached.checkDecls` at `.verified`, is
derived from [con-leche](https://github.com/leanprover/con-leche)'s verified
checker: `IxCK/Kernel/**` holds a modified copy under the namespace
`Ix.Kernel` (see "Origin and attribution" below), run on Ixon records by Ix's
reader in `IxCK/Kernel/Ixon/`. The certified API is
`Ix.Kernel.Admission.checkBytes` (`import IxCK.Kernel.Admission`; its theorems
are in `Ix.Kernel.Admission.Theorems`), which takes its content hash as a
parameter; the root library runs it at BLAKE3 as
`Ixon.Authenticated.checkBytes` (`import Ix.Ixon.Authenticated`). This page
states what that entry does, what
is proved about it, what is trusted, how the gate checks the trust boundary,
where the kernel comes from, and how to check a whole compiled environment.
This page is the contract: what an accept promises (a set-theoretic model,
no constant of `False`'s role key, every record and blob and the role
table's binding section stored under the hash of its bytes, the checked
declarations are the ones the bytes encode, bounded resources), under which assumptions (an
`Ix.Kernel.SetTheory V`; proofs on `propext`, `Classical.choice` and
`Quot.sound` only), on which execution foundation ("Trust surface"), and
with which outcomes (accept, reject, decline; only an accept carries the
theorems).

This entry does not by itself certify the Lean-to-Ixon compiler or IxVM.
An accepted environment has a model; that it is the
environment the original Lean source meant is outside this entry's claim;
for the Lean compiler's output, the compiler theorem (next section) relates
the two.

## Relation to compiler certification

The Lean compiler is proved correct against this page's entry, in `Ix/Cert`.
The statement is `Ix.Cert.CompileCorrect`
([`Ix/Cert/CompileCorrect.lean`](../Ix/Cert/CompileCorrect.lean)), proved by
`Ix.Cert.ReaderStreamsTrace.compileCorrect`
([`Ix/Cert/CompileCorrectProof.lean`](../Ix/Cert/CompileCorrectProof.lean))
on `propext`, `Classical.choice` and `Quot.sound` only. It is stated per
closure. When quotient Source accepts the closure (`SourceAcceptsQ`), the
compile (`Ix.Cert.compileReport`) reports no failure for it, and the
artifact checks hold (the published role names sit at the default table's
addresses, the published names agree with the artifact's address map,
quotient Source's evidence agrees with the table's, and the table's
certificates check), then:

- the artifact publishes every constant of the closure;
- Ixon accepts the compiled closure at the reference level
  (`IxonAcceptsRef`): this entry's binding admission, byte stages and reader,
  then the verified fold at some fuel, under the default binding and in an
  order that respects references. Reference acceptance is not a guarantee
  that the executable checker succeeds at its fixed fuel;
- the installed environment is quotient Source's environment renamed to
  the artifact's addresses, injectively on the names that environment
  mentions (`RenamesSource`); types and values, theorem statements and
  proofs included, are preserved by that renaming;
- every constant of the closure reads as a compiled constant
  (`ReadingCovers`), except the constants represented by the inert
  `sorryAx` role, which install nothing and whose uses decline;
- every strong model of the compiled environment
  (`Ix.Kernel.Cached.StrongModel`) gives **one value model of quotient
  Source** for the whole closure, in which every constant denotes what its
  reading denotes, at every level and variable valuation (`CommutesStrong`).

The statement is partial correctness: a compile that fails, a closure with a
failed constant, and a closure quotient Source does not accept are outside
it. The compiler compiles Lean verbatim (each block in Lean's grouping and
member order, every declaration as Lean declared it). Its internal mutual
representation is a flat ordered list: one payload and member index per
source member, with constructors in source order. Singleton groups remain
only at the serialized metadata boundary. Whole-constant alpha collapse
still lets identical anonymous encodings share an address; it does not
merge member positions inside a block. Acceptance is therefore certified from
quotient Source, where alias fibers are collapsed. The link to nominal Source
is not assumed for every environment: `CompileCorrect.checked` gets it per
artifact from the executed quotient check, and `CompileCorrect.nominal` takes
it as a hypothesis. That link concerns acceptance only: it supplies no
relation between nominal and quotient value models. The compiler conclusion
does not assert model existence; `CommutesStrong` retains its quantification
over every strong model.

On the command line, `ix compile` and `ix compile-lean` run the certified
compiler, `Ix.Cert.compileReport` itself (`Ix.CompileM.compileCertified` in
[`Ix/CompileCertified.lean`](../Ix/CompileCertified.lean)). The input's source
contracts are resolved, its constants canonicalized (`Ix.CanonM`), and
`compileReport` compiles them and runs its report checks (`Ix.Cert.checkReport`);
a failed check refuses the compile and nothing is written. Every reported
failure must be an input constant's, and an input with semantic contracts must
compile completely and validate its resources. The role support, certificates
and binding are then added (`Ix.RoleBinding.Compile.finalize`, which compiles the
support with `compileReport` too), and the finalized artifact is checked again
(`checkFinalized`: the original's publications and hints unchanged, and every
report check that reads the artifact alone) before it is written. The certified
compiler runs at the default sharing limits, which `compileReport` fixes: a
sharing-limit override is refused there.

Name-only `ix prove`, `ix check` and `ix addr-of` use
`Ix.Check.loadNamedIxonEnv`, which also compiles the closure through the
certified compiler `Ix.CompileM.compileCertified` (`Ix.Cert.compileReport`);
supplying a `.ixe` uses the supplied artifact instead. The uncertified
streamed and Rust compiler paths have been retired
([retired Rust](retired-rust.md)). Metadata is outside the
certification claim.

What the theorem covers on these paths: `CompileCorrect` is about the pure
function `Ix.Cert.compileReport`, which `ix compile`, `ix compile-lean` and
`Ix.Check.loadNamedIxonEnv` run on the canonicalized input
(`Ix.Compile.ReadyCompile.reportIO` proves by type that the IO worker-queue
driver returns `Ix.Cert.compileReport`, and `Ix.Cert.FreshSnapshot` proves
wave-snapshot freshness and disjointness across blocks in a wave, feeding the
direct semantic proof on the wave-snapshot fold; equivalence between the
wave-snapshot fold and a one-block-at-a-time live-state fold is not proved in
`Ix.Cert.Schedule`).
`finalize`'s additions are outside the theorem.

## The certified entry

```lean
def Ix.Kernel.Admission.checkBytes (hash : ByteArray → Address) (binding : Binding)
    (limits : Limits) (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error Ix.Kernel.Env

def Ixon.Authenticated.checkBytes (binding : Admission.Binding) (limits : Admission.Limits)
    (records : Admission.Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Admission.Error Ix.Kernel.Env :=
  Admission.checkBytes Address.admissionHash binding limits records blobs hint
```

`binding` is the role table's binding section and the address it claims
(`Admission.Binding`: `address`, `bytes`; "Roles, the role table and the
prelude" below). The entry admits it before it reads any record: the
address must be `hash` of the bytes, the bytes a canonical section
(`RoleTable.ofBytes`), and the table well formed (`RoleTable.check`). The
default table of the compiled Init is `Admission.defaultBinding`, for tests
and the command line; every theorem holds for every table.

`hash` is the content hash every address is authenticated against. The
kernel admits no hasher (its import fence, below), so the entry and every
theorem about it are generic in `hash`. The root library instantiates the
entry and its projection variant at `Address.admissionHash`
(`Ix/Address/Admission.lean`), which is pure BLAKE3 (`Address.blake3Pure`)
for every theorem and executes as the Rust BLAKE3 (`Address.blake3`); that
substitution is an assumption ("Trust surface").

An Ixon address is BLAKE3 of exact bytes, with no tag and no length prefix: a
record's is BLAKE3 of its complete serialization (`Ixon.serConstant`, the
bytes an `.ixe` stores for it after its length prefix), a projection
record's likewise, and a blob's is BLAKE3 of its payload. The compiler
addresses them so (`Address::hash` over `Constant::put`), the `.ixe` loaders
verify them so, and the resource adapter commits them so
(`Ix.Resource.Addressed.commit`).

Each entry has one runnable module, which holds definitions only, and its
theorems and audit beside it: `IxCK/Kernel/Admission.lean` (the entry, its
`Error` and `Outcome`), `IxCK/Kernel/Admission/Bytes.lean` (the byte stage
and its `ByteError`), `IxCK/Kernel/Admission/{Theorems,Bytes/Theorems,
Audit}.lean`; the projection variant `Ix/Ixon/Projection.lean` with
`Ix/Ixon/Projection/{Theorems,Audit}.lean`; the instantiations
at BLAKE3 `Ix/Ixon/Authenticated.lean` with
`Ix/Ixon/Authenticated/{Theorems,Audit}.lean`. Running the entry
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
| the role table's admission: its section under `hash` of its bytes, canonical, well formed | `Admission.admitBinding` | `.binding (.mismatch _ \| .decode \| .malformed _)` |
| the committed prelude, read under the admitted table | `Reader.preludeFor` | `.prelude reason` |
| batch limits: record and blob counts, total payload bytes | `Admission.preflight` | `.limit resource` |
| key uniqueness: no two records and no two blobs under one address | `Admission.uniqueKeys` | `.duplicate table position address` |
| authentication: every record and every blob under `hash` of its bytes, as supplied (a record's payload is hashed before it is decoded, never re-encoded) | `Admission.authenticate` | `.mismatch table position address` |
| the depth limit, as stored: every record's expressions (shares as leaves) and universes nest at most `limits.maxDepth` levels, read from the bytes before decoding | `Admission.scanDepths` | `.limit .depth` |
| canonical per-record decoding within byte and universe-node limits | `Admission.decodeRecords` | `.decode position address reason`; a record over `maxRecordBytes`, or a universe table past `maxRecordUnivNodes`: `.limit .recordBytes`, `.limit .recordUnivNodes` (`ByteError.asLimit`) |
| the depth limit, shares expanded: every decoded record's expressions nest at most `limits.maxDepth` levels as the reader builds them | `Admission.expandedDepths` | `.limit .depth` |
| the Ixon reader: records to `Array Ix.Kernel.Declaration`, bound addresses named by their role keys | `Reader.readRecords` | `.read position (.malformed _ / .declined _)` |
| the table's evidence, each proof entry resolved to its theorem's key and value | `Reader.evidenceOf` | (an unresolved proof leaves its operation without evidence) |
| the prelude is put in front (`Ix.Kernel.Frontend.preparePrelude`) | | |
| the verified fold | `Ix.Kernel.Cached.checkDecls .verified ev` | `.kernel error position` |

The pipeline is `Ix.Kernel.Admission.checkBytes`: it admits the binding and
reads the prelude under the table (`checkBytesUsing`), then runs
`checkBytesWith`, which takes the prelude as a parameter and whose
`prepareWith` runs the byte stages, admits the binding again (the theorems
read the table off it), decodes and reads; `checkConstants{,With}`
start from decoded records under an admitted table, and `checkConstantsAt`
admits a binding first. One variant shares the byte stage and the checker,
and takes the same `hash`: `Ixon.Projection.checkBytes` reconstructs omitted
projection records (addresses by `hash` of their canonical bytes) before
checking.

**Block order.** The entry does not check the member order of a mutual
block. The compiler stores every block in Lean's order: an inductive block in
the order of Lean's `all`, a definition block in its members' order there,
and a block of recursors in its family's order (`T.rec` for each member,
then `T.rec_1`, …), which is the order of its motives. The one order the
root library checks is a recursor block's: `Ixon.BlockOrder.checkRecord`
(`Ix/Ixon/BlockOrder.lean`, with `Ix/Ixon/BlockOrder/{Theorems,Audit}.lean`)
accepts a block of recursors only in motive order (member `j` eliminates
motive `j`, read off its type as the reader reads it,
`recursorMotive_of_analyse`, and declares one motive per member), and every
other record as it is (`checkRecord_ok_iff`, `OrderedRecord`). It is not an
entry: the fidelity suite (`Ix/KernelFidelity/Egress.lean`) runs it over
compiled environments.

**Outcomes.** `Admission.Error.outcome` (called as `e.outcome`) classifies
every failure as a reject (the input is wrong) or a decline (the checker
does not certify it):

| Error | Outcome | Why |
| --- | --- | --- |
| `.limit` | decline | a coverage bound, not evidence about the input |
| `.duplicate`, `.decode` | reject | the bytes are malformed |
| `.mismatch` | reject | a key is not the hash of the bytes stored under it |
| `.read _ (.malformed _)` | reject | the records describe no declaration (a missing reference or blob, a bad table index, a recursor header that disagrees with its block, ...) |
| `.read _ (.declined _)` | decline | unsupported: unsafe or `partial` definitions and unsafe axioms (the tiered entry types them, "The typing tier"), unsafe inductives, an inductive block whose recursor is not in the input, a mutually recursive definition block, a block the in-process modeller declines |
| `.binding` | reject | the role table's section is not the hash of its bytes, not canonical, or not well formed |
| `.prelude` | decline | a corrupted committed prelude |
| `.kernel` | decline | every checker verdict: the checker reports fuel exhaustion as `internal` and a failed conversion search as `invalid`, and neither is independent evidence that the input is wrong |

The projection variant keeps its own error (`Ixon.Projection.CheckError`)
and the same classifier, `e.outcome`: a checker failure (`.checker e`) as
above, the byte stage (`Admission.ByteError.outcome`) as `.limit`,
`.duplicate`, `.mismatch` and `.decode` above, and its own failures as
follows.

| Error | Outcome | Why |
| --- | --- | --- |
| `Projection.Error.limit` | decline | a coverage bound (projection requests) |
| `Projection.Error.ownerWidth`, `.conflict`, `.projection (.malformed _)` | reject | an owner key that is not a 32-byte hash, a supplied record that differs from the derived one at its key, a projection the writer finds malformed |
| `Projection.Error.projection` (any other search failure) | decline | the writer did not establish the projection |

Only an accept carries the theorems below.

**Host obligations.** The host supplies the order, the address keys and the
blobs. Every key is authenticated as `hash` of the bytes stored under it, so
a key names exactly one payload (up to a collision of `hash`); the
projection variant derives the addresses of omitted projection records with
the same `hash`. The entry does not reorder beyond
`preparePrelude`: each record must follow the records it references; a
record that contains a literal must follow the constants the literal names
(`Reader.literalEdges`: the `Nat` block, and for a string literal
`String`, `String.ofList`, `List`, `Char`, `Char.ofNat`); a bound `Nat`
operation must follow the constants its evidence references. A host order that violates
this declines; it cannot cause an unsound accept. The environment check's
order (`Ix/KernelCheck/Step.lean`, `Ixon.CheckOrder.order`) satisfies it.

## The theorems

All public theorems are in `IxCK/Kernel/Admission/Theorems.lean` (namespace
`Ix.Kernel.Admission`), about the executed function `checkBytes`. Each holds
at every content hash `hash` and for every role table `binding`, and follows
from the corresponding theorem at `checkBytesWith`, where it holds for every
prelude as well, so no theorem depends on which hash executes, which table
is supplied, or how the committed prelude was generated. Every public and fidelity
root depends on exactly `propext`, `Classical.choice` and `Quot.sound`.

| Theorem (`Ix.Kernel.Admission.`) | Statement, for `h : checkBytes hash binding limits records blobs hint = .ok env` |
| --- | --- |
| `checkBytes_has_model` | `∀ V [Ix.Kernel.SetTheory V], Nonempty (Ix.Kernel.Model V env)` |
| `checkBytes_has_model_values` | there is a model `M` in which every stored `defnInfo cv value _` satisfies `Denotes M.cval env φ ρ value (M.cval cv.name φ)` for all `φ ρ` |
| `checkBytes_no_proof_of_False` | no `ci ∈ env.consts` has type `.const (roleKey .false) []` (`False`'s role key, whatever the table binds) |
| `checkBytes_no_False_theorem` | no theorem record of the decoded input (`RecordsRead limits records constants`) has a type that the reader, under the admitted table, reads as `.const (roleKey .false) []` |
| `checkBytes_authentic` | `Authentic hash records blobs` (every record and every blob is stored under `hash` of its bytes, as supplied) and `hash binding.bytes = binding.address` |
| `checkBytes_binding` | `BindingAdmitted hash binding t` for some table `t`: the section is authentic, `t` is its canonical decoding (`t.wireWF`, `t.toBytes = binding.bytes`) and `t.check = .ok ()` (`admitBinding_ok_iff`) |
| `checkBytes_reading` | the binding admits as some `t` and the prelude reads under it (`preludeFor t = .ok pre`); `WithinBatch limits records blobs`; `UniqueKeys records blobs`; `Authentic hash records blobs`; `BindingAdmitted hash binding t`; `RecordsRead limits records constants` for some `constants`; `Hashed hash constants`; and `Installed t pre constants blobs hint env` |
| `checkBytes_resources` | `resourceUnits constants ≤ 2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes` |

The projection variant has the same theorems at every `hash`
(`Ixon.Projection.checkBytes_{ok_iff,reading,authentic,has_model,no_proof_of_False}`);
its `checkBytes_authentic` adds that every record the checker read, supplied
or reconstructed, is stored under `hash` of its serialization
(`Projection.Expanded.hashed`). `Ixon.Authenticated.Theorems` states them at
the specification hash `Address.blake3Pure` for the BLAKE3 entries (for
example `Ixon.Authenticated.checkBytes_authentic : … →
Authentic Address.blake3Pure records blobs`).

`Ix.Kernel.Model V env` (`IxCK/Kernel/Denotes.lean`) assigns a set
`cval c φ` to every constant at every level assignment such that every
stored constant is a member of what its type denotes (`mem`), what the
built-in `False` denotes is empty (`false_empty`), and what the built-in `Eq`
denotes is set equality (`eq_equality`). Definitional equalities need no
clause: an accepted `rfl` theorem's two sides denote the same set. The
model theorem is `Ix.Kernel.model_exists` (`IxCK/Kernel/MainTheorem.lean`,
upstream's statement and proof) at the prepared declarations: it holds for
every declaration array the fold accepts, so the reader owes nothing for
consistency. Definition values come from the kernel's model invariant
`defn_reads` through `Ix.Kernel.Cached.checkDecls_model_defn_values`
(`IxCK/Kernel/Ixon/Values.lean`). Theorem and opaque bodies have no value
equation, by upstream's design.

**The reference level** (`IxCK/Kernel/Verify/Cached/Reference.lean`,
`PerBlock.lean`, `IxCK/Kernel/Admission/Reference.lean`): an accept of the fold
is an accept of the pure declaration checker at some fuel, of the same
declarations with the same environment (`Ix.Kernel.Cached.AcceptsRef`,
`checkDecls_refines_ref`; at the entry `Admission.checkBytes_refines_ref`, in
Source mode `Ix.LeanIngress.checkSource_refines_ref`). The pure checker is
monotone in its fuel, so a reference accept determines its environment
(`AcceptsRef.unique`). Checking each declaration's deferred records right
after it (`checkDeclsPB`) accepts exactly what the deferred fold accepts
(`checkDecls_ok_iff_PB`): phase B is deferred for parallelism, not for
correctness. Statements about the fold that should mention neither the caches
nor a fuel (renaming, locality) are stated at this level.

**Fidelity** is what `checkBytes_reading` adds to consistency:

- `WithinBatch` and `UniqueKeys` (`IxCK/Kernel/Admission/Bytes/Theorems.lean`): the
  batch limits hold, and the record keys and the blob keys are each
  pairwise distinct (`preflight_ok_iff`, `uniqueKeys_ok_iff`).
- `Authentic` (`authenticate_ok_iff`): every record and blob key is `hash` of
  the bytes stored under it, exactly as supplied; with `RecordsRead`, every
  decoded record is stored under `hash` of its canonical encoding (`Hashed`,
  `RecordsRead.hashed`).
- `RecordsRead`: each payload is the canonical encoding of its decoded
  constant within the per-record limits, keys unchanged
  (`decodeRecords_ok_iff`, unique by `RecordsRead.deterministic`).
  "Canonical encoding" is the codec's: the payload is the bytes the v4
  writer produces for the decoded constant. It is not a statement about the
  constant's sharing table (see "Sharing tables" below).
- `Installed` (`IxCK/Kernel/Admission/Theorems.lean`): the reader's output is a
  record-by-record reading of the decoded records (`StreamRead`, from
  `readRecords_spec`), no two decoded records share an address
  (`Installed.keys`, from `readRecords_nodup`), and the fold accepted
  exactly that output behind the prelude. `Installed.skels`: the
  environment has exactly the install skeletons of the accepted array.
  `Installed.singleton`: every definition, theorem, opaque, axiom or
  quotient record is read under its name with its level parameters, its
  type's reading and its value's reading (or the projection rewrite), and
  is installed under that name with its kind (a quotient record,
  `sorryAx` and `Quot.sound` install as the basis blocks do).
- `Ctx.keyAt_eq_ok`, `Ctx.memberKey_of_role` and `Ctx.memberKey_of_unbound`
  (`IxCK/Kernel/Ixon/ReaderSpec.lean`): which key a reference and a member are
  read under (the role's key where the table binds the reference, otherwise
  the input key of the address it is keyed by).
- `RoleTable.ofBytes_eq_some_iff` (`IxCK/Kernel/Ixon/RoleTable.lean`): the
  binding section's decoder is canonical: it returns `t` exactly when `t` is
  in the format's domain and encodes to the given bytes.

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
- that a bound role's constant meets its specification (`Role.spec`)
  beyond what the fold checks: the block roles are checked against their
  specifications by the basis install, the operations by their evidence,
  the standard axioms with their `Iff` and `Nonempty` families by
  `stdAxiomOk`; the anchors (`Bool`, `True`, `List`, `String`, `Char`, ...)
  by their uses, and `Bool.rec`, `And`,
  `And.intro`, `And.rec` by the fold's step at install (`matchesPin`). That the
  default table binds Init's own constants is the generator's
  verification, not a theorem; the no-False theorems are stated at
  `False`'s role key and hold for any table.

The projection variant has the same shape:
`Ixon.Projection.checkBytes_{run_iff, ok_iff, of_expansion, reading,
has_model, no_proof_of_False}`, with `UniqueKeys` in its reading. The
separate package `Models/SetTheory` (Mathlib) provides `IxSetTheoryModel.zfSetTheoryOfCarneiro`, a
`Ix.Kernel.SetTheory ZFSet` instance under `OmegaInaccessibles`, and the
corollaries `IxSetTheoryModel.checkBytes_has_ZFSet_model` and
`IxSetTheoryModel.checkBytes_no_proof_of_False`.

**Assumptions.** Consistency is relative to `Ix.Kernel.SetTheory V`
(`IxCK/Kernel/SetTheory/Core.lean`): membership with extensionality,
unordered pairs, unions, power sets, regularity, replacement as a
Lean-level scheme (the image of a set under any `V → V`), and a strictly
increasing ω-chain of Grothendieck universes interpreting the universe
tower. The Mathlib instance above supplies it from ω inaccessible
cardinals, which its corollaries take as a hypothesis, not as an axiom.

**Input policy.** The entry has no fallback: what it declines stays declined,
and no checker outside its closure ("Trust surface") is consulted. The certified theory
uses Lean's three standard axioms: `propext`, `Classical.choice` and
`Quot.sound`. The compiler-trust axioms `Lean.trustCompiler`,
`Lean.ofReduceBool` and `Lean.ofReduceNat` are non-standard axioms here and
decline. There are no native-evaluation roles for these declarations or for
`Lean.reduceBool` and `Lean.reduceNat`; opaque definitions follow the ordinary
checking rules. Native evaluation is outside this certified theory.
`sorryAx` is tolerated as a declaration of its own type and installs
nothing; any use of it declines (`IxCK/Kernel/Core.lean`). The well-founded `Nat`
operations are admitted through the role table's evidence, which the
checker checks itself ("Roles and the role table" below).

**User axioms (uncertified).** Every other safe axiom, the three compiler-trust
axioms among them, declines at the certified entry and in every host driver
by default. A real Lean library therefore does not check whole: strict checking
of Init+Std declines `Lean.trustCompiler` and blocks the four native-evaluation
constants that depend on it, the other two axioms among them
(`Tests/Fixtures/initstd-reference.txt`). The host drivers can opt in with
`--allow-user-axioms` (`ix check-lean`, `kernel-check-ixe`): the declaration
checks then install a safe axiom whose key is an input constant's
(`Key.isCustomAxiomEligible`) as an axiom, and a whole `check-lean` run runs,
once, the entry under the `allowUser` axiom policy
(`Admission.checkBytesUnder .allowUser`, `checkBytesTieredUsingUnder .allowUser`,
through `Ix.RoleBinding.Artifact.checkConditional` and
`checkTieredConditional`). It returns the environment with the user axioms
among the declarations it ran over. When that list is empty the accept is the
certified entry's (T1, `Admission.checkBytesUnder_strict_of_nil`; the host
turns the receipt into the certified one with `ReceiptConditional.toReceipt`),
so the run issues the host statement as a strict run does. Otherwise no
soundness theorem covers the accept and there is no host statement. A run that admits a user
axiom prints `CONDITIONAL on K user axioms:` and lists them (the addresses the
declarations key them by, with their names in meta mode), and `check-lean`
exits with 5 rather than 0 ("`ix check-lean`" below). The binding must pass the
kernel's role-table check for user axioms (`Admission.admitAxiomPolicy
.allowUser`: `sorryAx`, `propext` and `Classical.choice` bound): a binding that
leaves one out keys Lean's own constant as an input constant, which the checks
would admit as a user axiom. The entries run that check themselves; the
record-by-record drivers never reach admission, so the host runs it first
(`Ix.RoleBinding.UserAxioms.requireAxiomRoles`), and such an artifact, like
one with no binding, is refused before any checking.

**Running time.** The theorems are about what the entry accepts; none bounds
its running time, and the checker's fuel (`checkFuel`) bounds recursion
depth, not work. Universe levels are one place where the checker itself
builds a term much larger than its input. The ∀ rule's level combines the
domain's and the codomain's, and on a chain of ∀s over one shared type
(`T (j+1) = T j → T j` in a sharing table, or `let a(j+1) : Type := aj → aj`,
which the annotation pass substitutes) the plain `imax u v` built a level
shared as a DAG of linear size whose tree doubles per binder, which the
level functions walk as trees (`Level.simplify`, from the comparison of the
inferred sort with the declared one, and `levelHasParam`, at every `.sort`
node built): a 225-byte constant took 52 s, twice as long per further step.
The rule's level stays upstream's `imax u v` (`Infer.forallE`); the executed
tier is what changed. `Level` caches its has-parameter bit; the cached core
hash-conses the ∀ rule's levels (`Cached.internLM`, the identity in the
logic: a hit is returned only after `==` confirms it), so that the level the
binder loop builds again for a telescope's tail is the object built before
(without it a `let` chain is cubic, 9 s at 2,000 steps); and the level walks
below are memoised. The hash-consing is an executed-tier device: `internLM l`
is `l` in the logic (a hit is returned only after `==`, which is lawful, has
confirmed it; `internLM_eff`, with `CSOK.withIntern`: no clause of the cached
core's state invariant reads the table), and the only proofs it changes are
the cached core's two simulation steps at the ∀ sites, `inferPisOutC_sim` and
`inferBodyIOC_sim`. `IxCK/Kernel/Rules/`, `IxCK/Kernel/Model/`,
`IxCK/Kernel/Core.lean` and
`IxCK/Kernel/Verify/{BinderLoop,InferLemmas,InferIOLemmas,Level,PropWhen}.lean`
are byte-identical to the rename commit `41b2eeac6` (upstream at `bdd4304fa`,
renamed), checked by `git diff`. Levels stay shared as DAGs whose trees double per step:
the ∀ chains above, two chains at two parameters, each step mentioning the
other's (`A (j+1) = A j → B j`, `B (j+1) = B j → A j`), and the levels
unfolding builds when each of a chain of definitions instantiates
the previous at `max u u` (`Level.subst` puts one object at both sides).
Level equality (`==`) is memoised below its pointer and hash tests on the
pairs it proves equal (`Level.decMemo`), and the executed forms of
`Level.simplify`, `Level.leqCore`, `Level.zeronessOf` and `Level.isNeverZero`
remember, for one call, the result at every node (for `leqCore`, every
subproblem `(fuel, l, r, diff)`) they have finished; `leqCore`'s case split
on a large level substitutes with a memoised `subst` (`Level.substMemo`).
Each executed form is proved equal to its specification and swapped in by
`@[csimp]`; below 64 nodes (32 for `leqCore`'s two operands) an exact copy
of the plain recursion runs instead, so ordinary levels cost what they did.
So every level walk is linear in the level's DAG, and such constants check
in milliseconds at hundreds of steps (the `kernel-level-sharing` test checks
the families at 200, the `let` chain and its parameter variant at 2,000
within a bound, and the printing of a failure about such a level: the
display shows at most 64 `max`/`imax` nodes of a level, `⋯` past them).

Terms repeat the same pattern one level up. The binder-telescope loops
(`Cached.inferPisI`, `inferLamsI`, `annotatePisI`, `annotateLamsI`) peel a
telescope to its end, and on a chain `T (j+1) = T j → T j` that meant
re-peeling, at every step, the whole telescope below it, although its tail
`T j` was inferred and annotated the step before; annotation also rebuilt
the peeled spine as fresh nodes, so an annotated chain of `k` steps held
about `k²/2` distinct nodes, and comparing two annotations of the same
chain built in different declarations (a function's declared type against
its value's) visited them all. The loops now stop at the first closed
residual the memo already holds (`Cached.peelFuelToM`: the peel fuel is the
number of binders before it; the fuel is semantically transparent, the
loops' simulations hold for every fuel, and `peelFuelToM_eff` says the
choice reads the state and changes nothing), so the leaf is a memo hit
and the rebuild shares the memoised term. And a level is simplified
through the declaration's memo (`Cached.simplifyMemoC`, the memoised walk
seeded with `lsimpC`), so a level built on levels already simplified costs
its new nodes. A residual the memo lacks is peeled as before: no knot
nesting is added. On the build box a 16,000-step `let` chain (a 112 KB
constant) checks in under a second where 8,000 steps took 27 s and 1.6 GB,
and comparing two annotations of a 2,000-step chain in 50 ms where it took
6.5 s (the `kernel-level-sharing` test bounds them). Two chains stay
quadratic: at a universe parameter, the specification's `Level.simplify`
does not merge `max u u`, so the simplified sort of each step is a DAG as
deep as the chain and `leqCore` walks it (8.8 s at 8,000 steps; at 16,000
the comparison's depth fuel declines it); and a chain of λs over the
previous value (`lamlet` in the test), where `Level.zeronessOf` walks the
∀ rule's level of each step's type (3.6 s at 8,000 steps, 18.8 s at
16,000).

Every memo of the cached core is a `Std.HashMap` keyed by terms, and the
term's hash is a field computed at construction. That hash was the low 32
bits of a `mixHash` recurrence over the node's fields, kept in the packed
word beside the variable ranges. A chain of nodes built by one repeated
step (`E_k = (λx. E_(k-1)) P L`, each head normalisation nesting once)
makes the hashes of successive levels iterate one function on 2^32 values,
which enters a cycle: at `P = Prop` level 8,323 repeats level 5,987. Past
the cycle every memo probe meets entries of equal hash and descends them
structurally, so the run is cubic past the entry: 32,000 levels took 83 s.
The hash is now 64 bits in a word of its own (`Expr.hashW`; equality's
fast reject tests both words), and the same chains first repeat beyond
1,000,000 levels (the `kernel-depth` test checks it and bounds the chain
at 32,000 levels, 35 to 49 ms). What it costs: the second word, +17 to
+20 % peak memory on Init+Std (2.79 to 2.83 GB against 2.33 to 2.40);
time within that run's noise (five rounds, ±7 % per round on a loaded
machine; an earlier, quieter paired run gave +10.5 to +11.9 %). The packed
word's freed bits 63 to 31 are reserved, for the cached depth the depth
limit may need. Measured alternative, rejected: a 48-bit hash in the
existing word, which narrows the range fields to 8 and 7 bits; their
saturated fallback (an exact walk per cutoff test) then costs seconds on
honest inputs (a 255-field structure of IxCC's fixtures, 90 ms before, 4.4
s or 10.4 s by the split) and a 16,384-binder telescope 26 to 36 s.

What the wider hash closes and what it does not. The cycle of a chain is
an accident of the function a step iterates; an adversary can also search
for a step whose cycle starts early and is short. Treating each truncated
node as a random function, which a simulation of the recurrence confirms
at 24, 32, 40 and 48 bits (it reproduces the measured 32-bit cycles
exactly), a step cycles with entry at most `a` and period at most `p` with
probability about `a p / 2^b`, and the run it buys costs about
`(n - a)^3 / (3 p)` comparison steps at depth `n`. At 32 bits such chains
are free; at 48 bits about 2^40 hash evaluations buy tens of seconds per
chain and about 2^49 a fixed point (`p = 1`, hours); at 64 bits the same
need about 2^56 and 2^65 (each candidate step costs about 2^13 to 2^14
evaluations to test). Not closed: (1) a
collision bought between two different terms (about 2^32 evaluations at 64
bits) makes each lookup of one descend the other: quadratic in their
depth, bounded by a depth limit (planned). (2) **Bucket flooding,
independent of the hash's width**: a map's bucket is the low bits of
`scrambleHash` of the hash, and the hash is not keyed, so an input can
carry R distinct terms that share a bucket of one memo (finding them costs
about 1.3 R² hash evaluations); each insertion then scans the others,
Θ(R²) comparisons in one map, bounded by the batch's size, not by depth.
R literals in one bucket of an `Expr`-keyed map insert in 8, 32, 145 and
619 ms at R = 2,048, 4,096, 8,192 and 16,384 (consecutive literals: 1 ms);
extrapolated, 10^5 terms take about 25 s. With equal full hashes
(multicollisions: k birthday searches give 2^k terms) each comparison also
descends. Two remedies, neither made: a keyed hash (a per-process random
key mixed into the node hash, or only into the maps' bucket index, which
stops the cheap flood but not full-hash multicollisions): an opaque
constant whose executed value is drawn at start, one new trust-surface
entry, no theorem changes, and hash values that differ between runs; or a
cap on bucket scans or structural comparisons per declaration, declining
when exceeded: no trust surface, but every memo lemma of the cached
simulation gains the decline case.

What remains is the comparison itself. `Level.leqCore` decides
`eval l ≤ eval r + diff` at every assignment by nanoda's case analysis:
splitting on a parameter being zero or not (`byCases`), distributing `imax`
over `imax` and `max`, and Géran's sublevels for the case nanoda's split
misses; it is complete when it answers. Deciding `l ≤ r` at every assignment
for levels built from `zero`, `succ`, `max`, `imax` and parameters is
coNP-hard, by a reduction from satisfiability (our own; not taken from the
literature): a CNF formula φ over variables `1 … n` becomes, with two
parameters `xi`, `yi` per variable, `2 = succ (succ zero)` and
`I [c1, …, cm] = imax (… (imax 2 c1) …) cm`, the levels
`G = I [max x1 y1, …, max xn yn]` and
`R = max (T_C1, …, T_Cm, x1, y1, …, xn, yn)`, where `T_C` is `I` of the
complements of clause `C`'s literals (`yi` for `i`, `xi` for `¬i`).
`G ≤ R` can fail only where every parameter is `0` or `1` (`G` is at most
`max 2` its parameters, `R` at least each), and there it fails exactly where
each pair has a nonzero member and each clause has a literal whose complement
is `0`: read `i` as true where `yi = 0`, that is an assignment satisfying φ,
and every satisfying assignment gives one. Both levels are linear in φ, and
`G = R` reduces to it as `max G R = R`. So no complete comparison is
polynomial unless P = NP: some bound or some incompleteness is unavoidable.
On the constant `def S : Sort (succ R) := Sort (max G R)` this kernel accepts
the unsatisfiable formulas and refuses the satisfiable ones (the
`kernel-level-sharing` test checks one of each), in time growing about ×4
per two variables on the chain `1 ∧ (¬1 ∨ 2) ∧ … ∧ ¬n`. Lean's kernel
decides level equality by normalisation only, which is incomplete: it refuses
all of these in under a millisecond, and also a well-typed constant this
kernel accepts (a chain of `imax` over `n` parameters compared with the same
chain with two parameters swapped), on which `leqCore`'s memo leaves a
polynomial of degree about 4 (10 s at 128 parameters). A host that checks
third-party bytes needs its own time and memory limit.

**Native stack.** The executed kernel recurses on the native stack, so how
deep an input it survives depends on the thread it runs on. Two drivers of
that depth are removed: neither the number of reduction steps nor the
number of records takes native stack. The reduction loops
(`Cached.whnfCoreLoopI`, `whnfLoopI`, `defeqLoopI`) hand the loop to the
step as a continuation; called through a closure, that kept native frames
per step, so a chain of 52,000 unfoldings of one-line definitions overflowed
an 8 MiB stack. Each loop's executed form runs a twin of the step that
returns its tail call instead of making it, then continues by a self tail
call, a loop in the emitted C (`whnfCoreLoopFast`, `whnfLoopFast`,
`defeqLoopFast`, swapped in by `@[csimp]`; `…Step_factor` proves the step
equal to its twin followed by the continuation, for every continuation).
The index build (`mkFEnvGo`, run again by the record-by-record check after
every failing declaration) and the whole-unit check of the certified entry
(`unitsGo`) recursed once per constant; their executed forms are a fold and
an accumulator loop (`mkFEnvGo_eq_mkFEnvGoFast`, `unitsGo_eq_unitsGoFast`),
and the host's record loop (`CheckIxeStep.checkLoopWith`) is a tail-recursive
loop in `IO` (`forArrayIO`). The `kernel-depth` test runs 90,000 unfoldings,
100,000 ι reductions, 200,000 one-line records through the certified entry
and 200,000 through the record-by-record check on a 2 MiB stack, and
Init+Std checks with every thread at 8 MiB (`initstd-stack`); before, each
of them overflowed (Init+Std on every stack up to 16 MiB).

The five substitutions are compiled-code replacements under the project
`@[csimp]` ruling (`runtimeRulings.csimpModules`); each theorem depends on
the standard axioms only, and IxCC's ledger lists them
(`lean_dependencies`, `csimp_theorems`):

| `@[csimp]` theorem | runs | in place of | proved from |
| --- | --- | --- | --- |
| `Cached.whnfCoreLoopI_eq_whnfCoreLoopFast` | `whnfCoreLoopFast` | `whnfCoreLoopI` | `whnfCoreStepI_factor` (with `whnfAppI_factor` and `betaPeelI_factor`, by well-founded recursion on the spine), by induction on the fuel |
| `Cached.whnfLoopI_eq_whnfLoopFast` | `whnfLoopFast` | `whnfLoopI` | `whnfStepI_factor`, by induction on the fuel |
| `Cached.defeqLoopI_eq_defeqLoopFast` | `defeqLoopFast` | `defeqLoopI` | `defeqStepI_factor`, by induction on the fuel |
| `mkFEnvGo_eq_mkFEnvGoFast` | `mkFEnvGoFast` | `mkFEnvGo` | `mkFEnvGo_eq_foldr` and `List.foldl_reverse` |
| `unitsGo_eq_unitsGoFast` | `unitsGoFast` | `unitsGo` | `unitsGoTR_spec`, by induction on the list |

What this bounds, and what it does not. The three loops and the two
record-count recursions take no native stack per iteration: a reduction
step or a record costs heap, not stack. The loops' fuels stay as bounds on
the steps (1,000,000 head-normalisation steps, 100,000 `whnf` and 100,000
conversion steps, each exhausted as a decline). Two calls of the
head-normalisation loop are not iterations and stay nested: `whnfAppR` after
an ι reduction with arguments left over, and `betaPeelR` when the peeled body
is not a λ and arguments remain, need the reduct's normal form before the
spine continues. Each nested call costs one step of the same loop's fuel, so
the nesting is at most 1,000,000 deep. Measured on a chain whose head
normalisation nests once per level (`(λx. E) P L`, each `E` the next link),
a level takes 750 to 780 bytes of stack: 2 MiB holds 2,750 levels, 8 MiB
10,500; at that rate the fuel's 1,000,000 levels would need about 750 MB, and
the command line's 256 MiB thread holds about 340,000 (inferred, not run).
In every construction found so far this nesting follows the input's own β
structure; whether ι reduction can produce it from a shallow input is not
settled. Init+Std still needs more than 2 MiB (it aborts on 2 MiB, 1 MiB and
512 KiB, in the typing core's nesting through `iotaRecI`, `prepareMajorI` and
`whnf`); see the next paragraph.

What still takes native stack is nesting: the canonical decoder on a record
nested without shares (about 30,000 levels overflow a 2 MiB stack, 100,000 an
8 MiB one), the reader and the install walks on the nesting of the terms they
read, the typing core on the nesting of the terms it infers and compares, and
the level functions on a level's depth. **The depth limit** bounds the input's
part of it. `Limits.maxDepth` (default 16,384: 13 times the deepest record
found in Mathlib, 1,221 with shares expanded; Init+Std's deepest is 325, IxCC's
committed closures' 775) is checked twice in the byte stage
(`Admission.decodeWithin`, which every byte entry and the hosts' own record
decoders run in place of `decodeRecords`): before decoding, `scanDepths` reads
each record's bytes in the codec's grammar without building anything, with a
stack of its own (words in an array: no native stack and no allocation per
level; integer headers of one and two bytes read in place, proved equal to the
codec's reader, `Depth.tagAt_eq` and `Depth.u8At_eq`, wider ones by the reader
itself), and declines (`.limit .depth`) at the first expression or
universe nested past the limit, shares counted as leaves; after decoding,
`expandedDepths` measures each record's expressions with their shares
expanded, as the reader builds them: the sharing entries in order, each against
the depths of the entries before it (the only references the reader admits),
then the payload. That walk recurses on the native stack, one frame per stored
level and never past one level beyond the limit, so its depth is bounded by the
stored nesting the scan has just admitted under the same limit, at every value
of the limit. Its frame is about 80 bytes; the codec's is 110 (λ telescopes) to
206 bytes (argument nests, `let`s) per level, measured on 8 MiB
(`kernel-depth-case frame-walk-*`, `frame-decode-*`); a spine is the one shape
the codec reads without nesting and the walk nests on, so a stack sized for the
limit must cover the larger of the two per level, which `Limits.stackFor`'s
16 KiB per level does. A table in which an entry refers to itself or to a later
entry (which the reader refuses) is measured instead by an explicit post-order
(`Depth.expandedPost`: each entry memoised, a share that reaches itself past
every limit), linear in the record: the same spine of 65,536 levels behind a
forward reference takes 4 ms, a cyclic table 2 ms (`kernel-depth` `post-spine`,
`post-cycle`; the post-order as first written copied its value array at every
node, 2.4 s at 65,536 levels). `kernel-depth` `differential` checks the scan
against its first form and the walk against the post-order on generated
records, mutated bytes included. A known cost of the byte entries themselves: they run the
two stages one record after another, about 1.5 s on Init+Std's 115 MB while the fold's phase B
runs on every core, so Init+Std through `checkBytesWithUserAxioms` takes 18.5 → 20.3 s best of
three (+9.6 %) against the entry without the depth limit, while the committed closures take +1.7 %
through the tiered entry and +1.2 % through IxCC's front end, and the hosts, which run the stages in
parallel (`RoleBinding.RecordDecoding.scanDepthsParallel`, `expandedDepthsParallel`, proved equal
to the sequential stages), stay within about 1 % on Init+Std. The remedy, not taken: the same
parallel stages inside the entry, bounded by `Limits.workers`, with the entry proofs rewritten
through their equality (about 60-100 lines). A record that cannot reach the limit is not
walked: an expression's levels grow by at most one per byte that writes it and a
universe's by at most the decoder's node budget (`storedDepthBound`), and a record
within the byte limit has at most two decoded nodes per byte, which an acyclic expansion meets
once each (`expandedDepthBound`); the statements about a compiled closure choose a limit above both
(`Ix.Cert.Stream.closure_decodes`). Both bounds are unproved assumptions of the skip: if
one were wrong, a record deeper than the limit could pass the stage meant to stop it. The
argument: a stored expression's levels grow by one per child, and every child is written with
at least one tag byte of its own (a spine or telescope of `n` steps is written with `n` more
expressions); a universe's levels are its nodes, which the decoder's budget counts before it
builds them; a decoded record has at most two nodes per byte (the spine and telescope nodes
add one per written expression), and an acyclic path meets each once. `kernel-depth`'s `bounds`
case checks both on the shapes that nest most per byte. Open: prove the two bounds, or remove
the skip by proving depth ≤ size where `closure_decodes` needs it. Levels count as the kernel's terms nest:
an application of `n` arguments has its head `n` levels down, a telescope of `n`
binders its body `n` levels down, `succ^k u` has `u` `k` levels down. The
checks are coverage bounds: nothing is proved about what they compute, and
`decodeWithin_error` shows they add no failure but the decline; what an
accepted input decodes to is `decodeRecords`'s (`decodeWithin_ok_iff`). A host
runs the entry on a thread of `Limits.stackFor` bytes (16 KiB per level of
`maxDepth`, at least 256 MiB: 256 MiB at the default).

The core's nesting is not only the input's: the conversion that unfolding
across records builds nests as deep as the records together (10,000 levels from
five records overflow 2 MiB, 40,000 from twenty 8 MiB), and so does a long
string literal met as a constructor, one level per character. That nesting is
bounded by the typing core's recursion fuel (`checkFuel`, 100,000 nested
calls, under 1 KiB of stack each as measured, which the 256 MiB thread holds),
not by the depth limit. Init+Std itself needs more than 2 MiB for this (it
checks on 8 MiB). IxCC's envelope also bounds the depth of each stored record,
shares expanded, at 2,560 (`IxCC.Ixon.V3.withinKernelDepth`), after its own
decoder.

**Limits.** Every bound the entry applies to its input is a field of
`Admission.Limits`, which each entry takes and every host sets:

| field | bounds | past it | default at the command line |
| --- | --- | --- | --- |
| `maxRecords`, `maxBlobs` | the batch's record and blob counts | `.limit .records`, `.limit .blobs` | 2^22 each |
| `maxTotalBytes` | the payload bytes of records and blobs together | `.limit .totalBytes` | 2^34 |
| `maxRecordBytes` | one record's payload | `.limit .recordBytes` | 2^28 |
| `maxRecordUnivNodes` | one record's universe table, expanded | `.limit .recordUnivNodes` | 2^26 |
| `maxDepth` | how deep a record's expressions and universes nest, as stored and with shares expanded | `.limit .depth` | 16,384 (the field's default) |
| `workers` | the tasks phase B of the fold runs on | nothing: no verdict changes | `none`, one task per 64 records (the field's default) |

A limit only turns an answer into a decline: `.limit` is a decline
(`Error.outcome`), and an input accepted under some limits is accepted under
any larger ones. For the batch limits this is their definition (`preflight`
compares counts and sums with them, `preflight_ok_iff`); for `maxRecordBytes`
and `maxRecordUnivNodes`, the decoder's byte check and node budget succeed
under a larger value on what they accept under a smaller one, with the same
result (its budget is only charged, never read otherwise); the decoder reports
both as decode errors with fixed messages, which `decodeWithin` reads as the
limits they are (`ByteError.asLimit`), and `decodeWithin_error` states that it
adds no failure but these declines and `.limit .depth`; for `maxDepth`, both
checks compare levels with the limit and read the same input whatever its value
(argued, not proved); `workers` changes how phase B runs, not what it returns
(`Cached.checkDecls_cfg`, `checkConstantsWith_cfg`, `checkConstantsAt_cfg` and
their tiered and policy twins, all from `checkPendingTasks_eq`). A verifier run
under smaller limits than the producer's may decline what the producer
accepted; the decline names the limit. Statements whose text the depth limit changed:
`Admission.checkBytesWith_eq` (its right side decodes with `decodeWithin`),
`Ixon.Projection.checkBytes_run_iff` and `checkBytes_ok_iff` (a `DepthsWithin`
conjunct), `Ixon.Projection.checkBytes_of_expansion` and `Ix.Cert.Stream.prepareWith_ok` (a
`DepthsWithin` hypothesis), `Ix.Cert.Stream.closure_decodes` (a `DepthsWithin` conjunct, under a
limit no record of the closure reaches); the public theorems about `checkBytes` are unchanged.

Five bounds are fixed: no setting raises them, because the cached core must
return what the reference core returns and these are constants of the
reference core or of the fold's use of it. Each exhausts as a decline
(`.internal "fuel exhausted: …"`): the head-normalisation loop's 1,000,000
steps (`whnfCoreLoopFuel`), the `whnf` and conversion loops' 100,000 each
(`whnfLoopFuel`, `defeqLoopFuel`), the level comparison's depth fuel of 10,000
(`Level.defaultFuel`, which `Level.isEquiv` uses), and the typing core's
recursion fuel of 100,000 nested calls (`checkFuel`, the knot's fuel in the
fold and in the typing tier). Raising `maxDepth` therefore has effect only up to
where `checkFuel` declines first. Measured with `maxDepth` raised to 1,000,000 on a stack of
16 KiB per level (`kernel-depth-case limit1000000-…`): an argument nest, a spine and a `let`
nest are accepted at 98,304 levels and declined at 114,688 with "fuel exhausted: annotate"; λ
and ∀ telescopes are accepted at 196,608 (their loops do not nest the knot). So a `maxDepth`
above about 100,000 admits nothing more of those shapes, and their decline names the fuel, which
no setting raises (a request to make it a parameter of the reference core is with the upstream
workstream).

## The typing tier

The logical fold gives what it accepts a model, so it declines every
declaration that is not safe. The **typing tier** gives Lean's `partial`
definitions (the `_unsafe_rec` companions) and its unsafe definitions,
opaques and axioms a second verdict, `typed`: *the declaration is
well-typed, with every tier constant opaque, including itself and its own
block*. It says nothing about meaning. Unsafe inductives still decline.

- **Data and fold** (`IxCK/Kernel/Tier/{Basic,Check}.lean`). A tier constant
  (`TierConst`) is a checked header stored as `axiomInfo`: it is never
  unfolded. `checkTierC` checks the tier declarations at the index of the
  accepted logical environment, with the logical fold's cached functions and
  no change to them, **staged as Lean's lattice** (`staged`): every partial
  block, then every unsafe opaque, then every unsafe block and axiom, each
  stage in input order. A definition block (partial or unsafe) is added as
  Lean's `add_mutual` adds it: its shape (non-empty, distinct keys, equal
  universe parameters, input keys only), its headers at the index before it,
  the install, then its values at the extension (annotation, inference,
  conversion against the header). An unsafe opaque is checked as
  `add_opaque` checks one, in safe mode: its header and value at the logical
  view, so it names no tier constant, its key fresh at the full index. An
  unsafe axiom is its header at the full index, its type a sort there. So a
  partial block sees the logical environment and the partial constants
  before and in it, never an unsafe one; an unsafe opaque sees none; unsafe
  code sees every tier constant before it and its own block.
- **The guarantee** (`IxCK/Kernel/Verify/Tier.lean`). `checkTierC_typed`: at
  the index of a well-formed environment `env`, an accept returns the index
  of `env.extendOpaque ts` (the tier constants in front, as `axiomInfo`),
  which is well formed; no tier constant is a constant of `env`; and every
  tier constant is the install of its declaration's header and is typed in
  its scope (`TypedIn`, `DeclTyped`, `ScopeOf`: a block member's scope is
  its block and the tier constants before it, all partial for a partial
  block; an unsafe opaque's is the logical environment; an unsafe axiom's,
  the tier constants before it; typed means its type is a sort and its
  value annotates to a term whose type converts to it, for an axiom its type
  a sort; `Rules.Infer`, `Rules.Red`, `Rules.DefEq`).
- **The fence.** A tier constant is never in the logical environment, and
  the logical fold's accept is well formed, so every term it stores resolves
  in it (`checkDecls_closed`): no accepted logical declaration names a tier
  constant. The entries and the drivers also name the reason (`fence: …`).
- **Refused relaxations** (fail closed). Lean's kernel unfolds partial and
  unsafe definitions in conversion (`type_checker.cpp:555-563`); the tier
  does not, so a declaration that types only by such an unfolding declines.
  Unsafe inductives stay declined.
- **Entries.** `Admission.checkBytesTiered` (and `checkConstantsTiered` over
  decoded records, `Ixon.Authenticated.checkBytesTiered` at BLAKE3): the byte
  stage over every record, then `checkConstantsWith` over the logical
  records, unchanged, then the tier reader (the reader's member reader in a
  context over all records, so keys agree; no projection rewrite, no hints)
  and the tier fold. `Ix.LeanIngress.checkSourceTiered` is Source mode's.
  Their theorems (`IxCK/Kernel/Admission/TierTheorems.lean`,
  `Ix/LeanIngress/Theorems.lean`) say the logical part is the existing
  entry's accept, so every theorem above applies to it as stated, and the
  tier part is `TypedIn`. Failures: `Admission.TierError` (and
  `LeanIngress.TierSourceError`) keep the logical entry's errors apart; a
  fence violation and every tier failure decline, and a malformed tier
  record rejects. `checkBytes`, `checkConstantsWith` and `checkSource` are
  unchanged and still decline every tier record: they are the entries
  whose accept is model-backed in full.
- **Rows.** The environment check (`kernel-check-ixe`, the per-record path
  without `--jobs` or the read cache) and `kernel-source-ingress` defer the
  tier records and check them after the logical walk, from its final index,
  staged as the fold stages them: outcome `typed`, reason `partial` or
  `unsafe`; a tier failure declines with reason `tier (<safety>): <message>`; a logical record that names a tier record
  declines with `fence: …`. `--report` and `--summary` count `typed`
  separately, `--paired` flags a lost `typed` as a lost acceptance, and the
  erasure test (`--meta`) runs the tier at both modes.

## Keys, roles and the prelude

**Records** are Ixon v4 constant payloads ([Ixon](Ixon.md), [Ixon v4](Ixon-v4.md)):
TagN integers, and a sharing table per constant. The reader consumes decoded
constants (`IxCK.Ixon.Types`) and never sees the integer code; only the byte
stage (`IxCK/Ixon/{Codec,Bounded/*,Canonical,WireCheck}.lean`) and its proofs
(`IxCK/Ixon/Verify`, including the TagN laws in `IxCK/Ixon/Verify/TagN.lean`) do.

**Sharing tables.** In Ixon v4 the table the compiler writes is canonical:
`Ix.Sharing.Exact.canonicalSharingTiered .tagN` of the constant's expanded
roots ([Ixon](Ixon.md), "Sharing System"). The certified entry does not check
that. It accepts any table whose entries refer only to earlier entries: the
reader expands every `Share` against the record's own table and rejects a
reference that is not to an earlier entry as malformed
(`IxCK/Kernel/Ixon/Reader.lean`), so the declarations it reads do not depend
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

**Modes** (`IxCK/Kernel/Key.lean`). The kernel's types (`Key`, `Expr`,
`ConstantInfo`, `Declaration`, `Env` and what is built from them) take a
`Mode`: `.anon` (Ixon: an input constant is identified by its address),
`.meta` (the same keys, with display data) and `.source` (Lean through
`CanonM`: an input constant is identified by its name). `.meta`'s display is
the reader's output's (`Reader.Read.display`: what the `.ixe`'s metadata says
of the keys a record declares, its Lean names and level names), filled by the
meta reader (`Benchmarks/Kernel/CheckIxeMeta.lean`), and no checker code
reads a display field (`IxCK/Kernel/Audit/Display.lean`). `.meta` never
decides: it explains failures with names.

**Names in terms.** So that a failure can print a term, a reduced
one included, with Lean's names, the names travel inside the terms, as in
Lean, through δ, β and instantiation:
- a binder carries its Lean name and `BinderInfo`
  (`BinderMeta.display : Squash BinderDisplay`) and a let its name
  (`LetMeta.display : Squash Name`). A `Squash` is a subsingleton, so
  structural `=`, the derived `DecidableEq`, `==`, the hash and every
  equation and decision of the checker are blind to the annotation: a named
  term *is* its anonymous erasure, `.meta` and `.source` check exactly what
  `.anon` checks, and no theorem moved. The type is the same in every mode
  (the renaming statement `Ix.Cert.Rename.expr` carries a binder's metadata
  between modes); `.anon` writes none (its reader builds shared anonymous
  objects (see `IxCK/Kernel/PinGen/Defs.lean`), which `BinderMeta.withPw` keeps
  only for an anonymous binder, `shareAlwaysImpl`);
- `.source` names its terms from the Lean terms (`Ix/LeanIngress/Names.lean`,
  `nameExprs`, after `ingressExprs`; `nameExprs_eq` proves the result is the
  conversion), and `.meta` from the `.ixe`'s metadata arenas
  (`Ix/KernelDisplay/MetaNames.lean`, `nameRead`, after the reader): binder,
  let, application and projection nodes. Missing or inconsistent metadata adds
  nothing and is never an error;
- a failure carries the terms it is about and the binders it was thrown under
  (`FailureDisplay`, a `Squash` on its message's first prose part), written
  outside `.anon` by `Msg.withTerms` and `withChain` (each a `@[reducible]`
  identity in the logic with a proved `@[csimp]` substitute), at application
  type mismatch, function expected, expected a sort, let value type mismatch,
  declaration type mismatch and theorem-not-a-proposition;
- the renderer (`Ix/KernelDisplay/Render.lean`, outside the kernel) prints in
  `ppExpr`'s style (names freshened with safe shadowing, `∀` versus `→`,
  implicit arguments hidden, no notation, full names); safe code cannot read
  a `Squash`, so it takes the read as a parameter, and the one display-only
  `unsafe` read is `Ix/KernelDisplay/Peek.lean` (trust-surface allowlisted;
  no certified root reaches it, `IxCK/Kernel/Audit/Roots.lean` and
  `Ix/Cert/RuntimeAudit.lean`).

Known limits: `.meta` keys are addresses, so the members of an alias fiber
(α-equivalent constants, such as `HAdd.hAdd` and `HMul.hMul`) print as its
first name; a memo hit may return an α-equivalent term whose names come from
a sibling occurrence, as Lean's caches do. `kernel-meta-names` is the oracle
against Lean (`ppExpr`, `Kernel.whnf`, the kernel's exceptions).

`Mode.Id md` is what identifies an input constant (an `Address` in `.anon`
and `.meta`, a `Name` in `.source`), `Mode.D md α` the display data (`Unit`
outside `.meta`), and `Mode.Certified` holds of the modes the theorems are
stated at (`.anon`, `.source`; `model_exists` takes it). The checker and its
proofs are generic in the mode. Source mode installs an `Env .source`; the
Ixon entry installs an `Env .anon`.

**Keys** (`IxCK/Kernel/Key.lean`, `IxCK/Kernel/Ixon/Reader.lean`). The kernel's
environment is keyed by `Ix.Kernel.Key md`, an inductive with a cached hash:

- `.id i`, an input constant. In Ixon mode `i` is the address its references
  use, the address in a record's `refs` table: a singleton's (`defn`, `recr`,
  `axio`, `quot`) own record's, a block member's projection record's (`iPrj`,
  `cPrj`, `rPrj`, `dPrj`); a `muts` block's own address is never a key. A
  member whose projection record the input omits is keyed by the address that
  record would have under the entry's hash (`Admission.projectionAddress`).
  The reader keeps the side map from a member's position to its address
  (`Reader.Keys.address`) and resolves an address to its block and position
  (`Reader.resolve`) to group a block. The Lean ingress keys a constant by
  its Lean name (`Ix.LeanIngress.ingressKey`).
- `.role r`, the constant a role is bound to: in Ixon mode the reference the
  role table binds (`Reader.bindingsOf`), in Source mode the constant under
  the role's Lean name (`Role.leanName`, `Key.ofName`).
- `.aux k d`, a constant the checker or the front ends' shared back half
  generates from `k`, of shape `d : Derived` (a model companion, an installed
  projection function or table, the modeller's families and transports). No
  front end makes one, so an input is never `.aux`: the front door's
  reserved-shape tests (`Key.isProjFnShape`, `Key.isModelSuffix`) refuse only
  generated keys, never an input name.

Equality is structural behind a pointer and hash guard (`Key.beq`, `@[csimp]`
on `Key.beqPtr_eq`); the cached hash of an input key is its address's first
eight bytes, or its name's hash. The reader computes every record address's
key ahead (`Reader.Keys.byAddress`), so every occurrence of an address reads
one key object. A key prints per mode (`Key.toName`): an address as `#` and
its first twelve hexadecimal digits, a name as itself, `.role r` as
`r.leanName`, `.aux k d` as `k`'s spelling with `d`'s suffix
(`Derived.spell`). Only the renderers, the reader's messages and the front ends'
name maps read that spelling; the fold never does: a checker failure is a
`CheckError md`, a verdict and a message of prose and keys (`Msg md`), which
a renderer spells (`CheckError.render`) and a renaming maps
(`CheckError.mapKeys`). Level parameters are positions (`LevelParam := Nat`): a
constant's are `0, …, n-1`, and a large eliminator's are `n :: [0, …, n-1]`
after its block's `n`, the shape by which the checker recognises it
(`Reader.recLps`). A recursor is keyed by its own record (a `recr`'s or an
`rPrj`'s address), never after what it eliminates; an inductive block lists
its recursors in motive order, and the stream's index-count check pairs the
recursor of motive `m` with the block's type `m` (`RecCounts.motive`).

**Roles and their specifications** (`IxCK/Kernel/Roles.lean`).
`Ix.Kernel.Role` has 103 roles for basis blocks, literal support, verified
operations, the standard axioms and the inert `sorryAx` role. This includes
the fifteen Nat operations and the typed anchors/equations for decision
procedures, Int, BitVec and String operations. `Role.all`, `Role.spec`,
`Role.block` and `Role.deps` define the exact catalog. A specification and
evidence do not by themselves enable a native acceleration; each execution
backend has its own admission boundary.

Specifications are closed terms over role keys and positional universes, of
five kinds: exact `block` declarations, an `anchor` type, a Nat operation's
type and characterizing equations (`ops`), a standard `axiom` type, or a
definition's type and equations over a typed telescope (`eqns`). An
unconditional definition equation may use definitional equality or a checked
certificate; a conditional equation requires a certificate. `Role.block`
groups roles bound together, `Role.deps` records required groups, and
`Role.usedImplicitly` identifies roles the checker introduces into terms.

The specifications carry no toolchain address. Standard axioms' supporting
families, including Iff and Nonempty, are validated as whole blocks. The
inert `sorryAx` role has an exact type and supplies no usable proof. The
specification version, encoding and digest are pinned in
`IxCK/Kernel/Roles.lean`, `Ix/SpecDigest.lean` and
`IxCK/Kernel/Audit/Roles.lean`; those sources define the current values.

For anchor installation, `Cached.annotDeclStep` checks the bound type through
`installAnchorPin?` and `matchesPin`, up to binder data and level-parameter
names. A mismatch declines with `role specification mismatch`. The compiler
also enforces `RoleRecordKinds` in its report checks. The equation checker
used by pin generation validates actual definitions and checked evidence;
it adds no native rule to IxCK. IxVM validates the role specifications for
its native operations.

**The role table** (`IxCK/Kernel/Ixon/RoleTable.lean`) is input:
`RoleTable` has the version of the specification set it was made for, the
bound roles' addresses (`bound`, by role, ascending) and the operations'
evidence (`evidence`, one entry per equation). Its bytes are a binding
section of their own:

| bytes | field |
| --- | --- |
| `E8 03` | the section's tag |
| `v` | the specification version |
| `n`, `n × (r, a)` | the bound roles: a role's index in `Role.all` and its 32-byte address, indices strictly increasing |
| `m`, `m × (r, k, e₁ … e_k)` | the evidence: a role's index, its entry count and its entries, indices strictly increasing |
| `e` | `00` for `defeq`, `01` and a 32-byte address for `proof` |

Every integer is one byte. The decoder `RoleTable.ofBytes` is canonical
(`ofBytes_eq_some_iff`: it returns `t` exactly when `t.wireWF` and
`t.toBytes` is the input). The entry admits a section (`admitBinding`) when
its address is `hash` of its bytes (the binding hash), it decodes, and the
table is well formed (`RoleTable.check`, decidable): the version is
`specVersion`; no role and no address is bound twice; every bound role's
block and dependencies are bound; and the evidence is exactly the bound
operations', one entry per equation, of the kind the equation fixes
(`.defeq` for an unconditional equation, `.proof thm` for a conditional
one). An unbound role affects coverage only: inputs that need it decline.

**Validation.** The reader names every bound reference by its role key; the
fold validates each bound constant against its role's specification when it
installs it, and a mismatch declines. Basis blocks are compared with their
specification up to `canon`, with a reserved-name reject otherwise; the
standard axioms' families, before their axiom is installed, by kind and type
(`stdAxiomOk`); anchors and axioms by type (`matchesPin`); an operation's type exactly, and its
equations certified by its evidence in the environment before the
operation's insertion, with the operation's self-references replaced by its
value: a `.defeq` entry by definitional equality after opening
(`certifyNatEqs`), a `.proof` entry by checking the theorem's proof against
the equation like a theorem declaration (`checkDivModEvidence`), under a
closure condition (`evidenceLocal`): every constant the proof mentions is
installed and in the operation's dependency closure. The evidence reaches
the fold resolved (`Reader.evidenceOf`: each proof entry's theorem record
read to its key and value); an entry that does not resolve leaves its
operation without evidence, which declines it. The fast path of an
operation (`Nat` literal arithmetic) is enabled exactly when the operation
is installed and validated. `model_exists` holds for every evidence, so the
evidence is untrusted.

**Binder contracts** (`IxCK/Ixon/Types/Contract.lean`). Ixon binders carry
usage, ownership and locality contracts, inside the committed bytes. The
reader keeps a `lam`'s in the binder's `BinderMeta` (`contract`) and an
`all`'s input and result contracts (`contract`, `result`), and a `let`'s
let contract (`nonDep`, value or shared borrow, and the bound variable's
contract) in the `letE`'s `LetMeta`; the Lean ingress gives Lean's lets
`LetContract.lean nonDep`, as the compiler does. They are identity data. A
`let` never reaches conversion: the annotation pass ζ-reduces it. Structural
equality, the expression hash and the specification comparisons see them;
every specification carries the Lean fragment's defaults (`many`, `shared`,
`unrestricted`), so a constant with other contracts does not meet it.
Conversion compares input contracts: the binder congruences and η require
equal input contracts as well as equal `pw` data, so the entry declines
`f : ∀[erased] (x : Nat), Nat := fun[many] x => x`. It never compares result
contracts: a `lam` has none, so the type inferred for one carries the
default, and `fun[linear] x => x` checks against
`∀[linear] (x : Nat), unique Nat`. For the same reason `rfl` proves two arrow
types equal when they differ only in a result contract; resource admission,
not the kernel, refuses a transport along such an equality
([resource checking](resource-checking.md)). The model reads only `pw`, so an
accepted environment says nothing about how a variable is used
(`Tests/Ix/Kernel/Contracts.lean`). The kernel imports these data types
from Ixon, and nothing else
(`kernel-layering`). Source mode gives Lean's binders the defaults and reads
the compiler's resolved contract frames as the compiler lowers them
(`Ix/LeanIngress/Expr.lean`).

**Source mode** uses a fixed table: every role is bound to its own Lean name
(`Ix.LeanIngress.sourceBinding`), and the evidence is the certificate
theorems of `IxCK/Kernel/PinGen/Certs.lean` as they appear in the checked
environment, through the same ingress (`Ix.LeanIngress.sourceEvidence`): an
environment without them declines the well-founded operations.

**Prelude** (`IxCK/Kernel/Ixon/Prelude.lean`). The checker puts twelve
declarations in front of every fold (`preparePrelude`): the basis blocks `Eq`, `Nat`, `PUnit`,
`Empty`, `False`, the quotient package (four `Quot` constants and
`Quot.sound`), `And` and `Bool`. Here they are the compiled Init's own Ixon
records (`RoleData.prelude`, canonical bytes by address), decoded by the
canonical decoder and read by the same reader under the admitted table
(`preludeFor`). The empty stream installs the declarations prescribed by
the admitted prelude. A stream that declares a prelude constant is checked
on its own record (`preparePrelude` moves the stream's copy to the front);
the prelude's copy fills in where
the stream has none.

**The default table** (`IxCK/Kernel/Ixon/RoleData.lean`, generated) binds
every role to the compiled Init's constant of its Lean name, with the
evidence: structural operations' `.defeq` entries and compiled theorem
records for operations that need certificates (`RoleData.evidence`, with
the literal blobs in `RoleData.blobs`). These records hold the certificate
theorems of `IxCK/Kernel/PinGen/Certs.lean` compiled by Ix and closed over
the operations' dependency closure. The evidence records back the reader's
store (`Prelude.evidence`); they are never read as declarations of their
own. Its section is at `RoleData.tableAddress` (BLAKE3 of `RoleData.table`),
`Admission.defaultBinding`. It is untrusted, for tests and the command line.

**Regeneration.** `kernel-pin-gen` (`Benchmarks/Kernel/PinGen.lean`)
generates the default table, checks that the evidence reads back as the
closed proofs, and checks the dependency closure of every bound constant
through the verified fold under the table before writing:

```sh
lake exe ix compile Benchmarks/Compile/CompileInitStd.lean --no-build --out .lake/envs/initstd.ixe
lake exe ix compile IxCK/Kernel/PinGen/Certs.lean --no-build --local --out .lake/envs/certs.ixe
lake exe kernel-pin-gen .lake/envs/initstd.ixe .lake/envs/certs.ixe \
  IxCK/Kernel/Ixon/RoleData.lean
```

(`--no-build`: the files import only `Init`, and the root package does not
know `IxCK/Kernel/PinGen/Certs.lean` as a target of its own.) The exact
certificate inputs and source hashes are recorded in the generated file's
header. The
table names addresses, so a toolchain, compiler or format change that moves
Init's addresses requires regeneration; the specifications, `specVersion`
and the digest stay. Soundness does not depend on the table.

**In IxVM.** The circuit reads a typing claim's roles through the binding its
context names (`Ix/IxVM/Kernel/Roles.lean`) and validates each against the
same specifications, rendered as circuit terms (`Ix/IxVM/Kernel/RoleSpec.lean`,
generated by `Ix/IxVM/RoleSpecGen.lean`). Groups follow `Role.block`, in an
order where every `Role.deps` precedes, and a group is validated the first
time a claim uses one of its roles, under a context that admits only the
groups before it, so an operation's fast path never takes part in its own
validation. The well-founded operations' groups come last and share the
context before the first of them, so their common dependencies are checked
once. A claim's walk checks a constant bound to a basis member or an
operation under the context its group is validated in, whether or not the
claim uses the role: the check is the group's own when it does, and admits
nothing when it does not. Under the standard axiom policy this declines a
reference to such a constant whose dependencies use a standard axiom whose
group comes after its own. Block members (the basis and the standard
axioms' families) are checked as constants, an operation must check and meet its equations (definitionally, or by its
certificate theorems, which are checked), and anchors and axioms are
validated by type, as here. One difference follows from what a claim covers: an IxVM claim
checks a constant with its dependencies, not a whole environment, so the
constants the circuit introduces into a claim's terms without the claim
referencing them (a string literal's type and its constructor form's
`String.ofList`, `List.nil`, `List.cons`, `Char` and `Char.ofNat`, and the
constants a native rule builds its result from) are checked as the claim's
dependencies, under the claim's context. Every native rule fires on a role:
the `Int`, `BitVec`, `String` and decision rules on definitions validated
against their `eqns` specifications, each result an instance of the head's
equations.
The axiom policy is IxCK's: a safe axiom is declared only when the binding
binds it as `propext`, `Classical.choice` or `Quot.sound`, or as `sorryAx`,
which no constant may use (`axiom_standing`, the one place a standard axiom
is recognized), and an unsafe axiom is typed only. Nothing reduces natively:
`Lean.reduceBool` and `Lean.reduceNat` are opaques that never reduce, and a
claim that uses them depends on `Lean.trustCompiler`, which is declined.
A `check` or `checkEnv` claim may instead assume its binding (validator
`4`, `ClaimContext.bindingAssumed`): it reads roles through the same table
but validates no group, and a walk leaves a bound basis member or operation
to the condition, that the table meets the specifications. The `binding`
claim states that condition: the table binds every role and every group is
admitted, under the same contexts. It depends only on the specification
digest and the table hash, so one proof serves every aggregate over the
binding; `ix_aggr` discharges an aggregate's condition once with it (shapes
13 and 14), and the discharged claim is the one a claim that validates its
binding states.

**IxCK's reader obligations at IxVM's boundary.** Six obligations of IxCK's
frontend and reader are recorded for every second checker to mirror or rule
out. IxVM rules each out by what it reads:

- *The rest-only hoist and its split guard* (`hoistNatOpGround`,
  `splitsUnit`, `IxCK/Kernel/Frontend/NatOpGround.lean`) reorder IxCK's input
  stream so that a certified `Nat` operation's ground precedes it, without
  moving the prelude front or splitting a generated unit. IxVM reads no
  stream. A claim names constants by address and checks each with its
  dependencies through the content-addressed reference graph, and an
  operation's evidence is validated under the role groups before it, so
  there is no input order to repair or to split.
- *The whole-unit check* (`checkUnits`, `IxCK/Kernel/Units.lean`) keeps a
  mutual block's generated records together and closed by their block, and
  refuses a base declared twice. IxVM checks a mutual block as one constant
  (`check_muts_all`), its members' projections derived from the block's own
  bytes; a generated auxiliary is an ordinary constant under its own
  address, and content addressing makes a second declaration of a base the
  same constant.
- *The prelude shape and prelude-copy equality* (`checkPreludeShape`,
  `State.keepsPrelude`) tie the reader's prelude to the role table: a role
  is read from the prelude's own record, and a stream's own copy of a
  prelude record must read alike. IxVM has no prelude and no second copy:
  every role is the constant the binding names, validated against its
  specification the first time a claim uses it.
- *The inferer's fuel* (`inferFuel`, 4096, in the in-model generator) bounds
  a syntactic inferer that runs before the fold and declines a block that
  exhausts it. IxVM runs no generator. Its one bound, the lazy-delta loop's
  fuel in definitional equality, only stops unfolding early, and the
  comparison then falls back to its structural cases, which are sound on
  their own; an execution that does not terminate yields no trace and so no
  proof.

## Trust surface

The theorems are about the Lean functions. Trusted beneath them: Lean's
kernel, compiler and runtime, and the inherited `Init`/`Std` primitives the
compiled code reaches (the entry's closure reaches 113 inherited externs,
for example `ByteArray` and `String` primitives and `lean_sarray_dec_eq`,
which implements `ByteArray` equality and therefore `Address` equality).
Among them are Lean's task primitives `Task.spawn` and `Task.get`
(`lean_task_spawn`, `lean_task_get_own`): the fold checks its deferred
records in chunks on pure tasks (`checkPendingTasks`). As Lean functions they
are the resolved task `⟨fn ()⟩` and its field, so the theorems read the
sequential walk (`checkPendingTasks_eq`); execution trusts the runtime to run
a pure closure on another thread, as it trusts it to run any closure. The
runtime sizes the pool (`LEAN_NUM_THREADS`), and no size changes a verdict.
Not in the closure: `ix_rs`, C or Rust BLAKE3, any JSON or lean4export
parser. The entry and its variants hash only through their
`hash` parameter.

The root library's authenticated entries (`Ixon.Authenticated`) add one
substitution, admitted on an assumption rather than a proof: the admission
hash `Address.admissionHash` is defined as pure
BLAKE3 (`Address.blake3Pure`), which every theorem about those entries is
stated at, and executes as the Rust BLAKE3 (`Address.blake3`,
`@[implemented_by]`), whose three foreign primitives
(`Blake3.Rust.hasherInit`, `hasherUpdate`, `hasherFinalize`) it brings into
the compiled closure. The assumption is that the two implementations agree
on every input; `Tests.Ix.Kernel.AddressPure` checks it on fixture inputs.
The runtime audit admits it by name (`Ix.Kernel.Audit.assumedSubstitutions`,
the `assumed` ruling) only for those entries, and the trust-surface fence
scans `Ix/Address/Admission.lean`.

Project-level execution constructs are admitted only as named by
`runtimeRulings` (`IxCK/Kernel/Audit/Roots.lean`):

| Construct | Where | Why admitted |
| --- | --- | --- |
| `@[computed_field]` overrides | `IxCK.Kernel.Level`, `IxCK.Kernel.Expr`, `IxCK.Kernel.Name`, `IxCK.Kernel.Key` | cached hashes, the level's has-parameter bit and packed data; a compiler feature, trusted with the compiler |
| project `@[csimp]` | `IxCK.Kernel` | each replacement theorem depends on the standard axioms only |
| the codec's TagN `@[csimp]` twins (`getTagN_eq_fast`, `putTagN_eq_fast`) | `IxCK.Ixon.Codec` (also `Ixon.Audit.rulings`) | the reader and writer at a fixed flag width with their powers folded; each theorem depends on the standard axioms only |
| `withPtrEq`, `withPtrAddr`, `ptrEq`, `isExclusiveUnsafe` and their unsafe implementations | Lean's `Init` | the continuation carries the obligation that it does not observe the answer |
| `Ix.Kernel.withExclusive` `implemented_by` `withExclusiveUnsafe` | `IxCK/Kernel/Exclusive.lean` | its type carries `k true = k false`, discharged by `Subsingleton.elim` |
| elaboration-time `unsafe`, `implemented_by`, `meta import Lean` | `IxCK.Kernel.BasisGen` | elaboration only; compiled code cannot reach them |
| `Address.admissionHash` `implemented_by` `Address.blake3`, with its three Rust externs | `Ix/Address/Admission.lean` (root library; `assumedSubstitutions`, for `Ixon.Authenticated` only) | an explicit, owner-approved assumption that the Rust BLAKE3 equals pure BLAKE3 |

Import allowlists (`IxCK/Kernel/Audit/Roots.lean`):

- `kernelImportAllowlist`: `Init`, `Std`, `IxCK.Kernel` (the checker and
  Ix's Ixon boundary), `IxCK.Address.Core`, `IxCK.Ixon.Types`. It fences
  the reader, the record store, the projection writer and the pure Ixon
  types.
- `importAllowlist` (the certified API's closure, rooted at
  `IxCK.Kernel.Admission`): the above plus exactly `IxCK.Ixon.{Codec, Wire,
  WireCheck, Bounded.Constant, Bounded.Universe, Canonical}`, without the
  entry's theorem and audit modules and the kernel's audits
  (`importDenylist`; `kernelImportDenylist` likewise keeps
  `IxCK.Kernel.Admission` and `IxCK.Kernel.Audit` out of the kernel-side list).
  No projection hashing, block order, `Ix.Address.Pure`,
  proof module or `Lean` (outside `elaborationImports`).
- `proofImportAllowlist` (the theorem modules): `importAllowlist` plus
  `IxCK.Ixon.Bounded.Size`, `IxCK.Ixon.Verify`, the theorem module and
  `Lean`.
- `elaborationImports`: below `IxCK.Kernel.BasisGen` only `Init`, `Std`,
  `Lean` and `IxCK.Kernel`.

`Std` is admitted for its maps and their lemmas, as the kernel uses them.

## Audits and fences

The audits are Lean modules that fail elaboration on a violation. The core
kernel and codec audits are built by the strict standalone package `IxCK/`
(`lake -d IxCK build --wfail`, sources from the repository, no dependency
beyond the toolchain). The projection, block-order and authenticated-entry
audits, `Ix/Cert/RuntimeAudit.lean` and `Ix/Cert/ModuleAudit.lean` build in
the root package, and the model audit builds in `Models/SetTheory`.

| Module | Checks |
| --- | --- |
| `IxCK/Kernel/Audit/Roots.lean` | presence of every root (`publicRoots`, `fidelityRoots`, the operations); each at exactly the three standard axioms (`#guard_kernel_axioms`); the import closures against the allowlists; frozen runtime closures with their rulings; frozen `#check` statements and the definitions of `Authentic` and `Hashed`; a control showing the fold fails without the rulings |
| `IxCK/Kernel/Admission/Audit.lean` | the byte stage's imports, closure and extern difference, its lemmas' axioms, and the public statements |
| `IxCK/Kernel/Audit/Roles.lean` | the specification set's shape, frozen: every role's kind, levels or equation count, evidence kinds, block and dependencies, and `specVersion` |
| `IxCK/Kernel/Audit/Modules.lean` | every safe declaration of every kernel module it imports (the kernel, and the theorems no root reaches: non-contradiction, the renaming and union development, unit hoisting, the in-model generators, the prelude shape, role-table injectivity) bounded by the three standard axioms (`#guard_module_axioms_under`, `Audit/Axioms.lean`); exact axioms of `nonContradiction`, `Cached.AcceptsRef.union` and the unit and hoisting theorems |
| `Ix/SpecDigest.lean` | the specification digest (BLAKE3 of the set's canonical encoding), frozen |
| `Ix/Ixon/Projection/Audit.lean`, `Ix/Ixon/BlockOrder/Audit.lean` | the projection variant's and the recursor-order check's imports (no hasher), closures, extern differences (none for either) and statements, and the projection writer's guards |
| `Ix/Ixon/Authenticated/Audit.lean` | the BLAKE3 entries' closure with exactly the assumed substitution (and its failure without it), the externs and `implemented_by` they add to the generic entries, their frozen definitions, their theorems' axioms and statements |
| `Ix/Cert/RuntimeAudit.lean` | the compiler's (`Ix.Cert.compile`) runtime closure: every foreign primitive, `unsafe` implementation and `partial` definition it reaches beyond `Init` and `Std`, frozen by name (its axioms are frozen in `Ix/Cert/Audit.lean`) |
| `Ix/Cert/ModuleAudit.lean` | every safe declaration of the proof modules that no statement reaches (Source grouping, ownership, metadata and uses; admission fronts; Source family and identity checks; the artifact and host admission theorems), and of every `Ix.Cert` and `Ix.CompileCert` module they import, bounded by the three standard axioms (`#guard_module_axioms`) |
| `IxCK/Ixon/Audit.lean` | the codec's own import, runtime and axiom audit |
| `Models/SetTheory/IxSetTheoryModel/Audit.lean` | the model package's full dependency closure: standard axioms only |

Each audit owns the exact inventory of functions, foreign primitives and
allowed substitutions reachable from its roots. Its source records the
current counts and explains deliberate changes beside the frozen values.
These inventories cover the checker, reader, byte admission, projection
writer, recursor-order check and BLAKE3 entry separately. The compiler's
runtime audit is a distinct closure rooted at the compiler.

A frozen value or statement changes only deliberately: the change that
re-records it states why the closure or the statement moved.

`lake run check-kernel [--with-model]` is the gate. In order:

1. the strict `IxCK` build with the core kernel and codec audits;
2. the host build of the root audits (`Ix/Ixon/{Projection,BlockOrder,
   Authenticated}/Audit.lean`, `Ix/Cert/{Runtime,Module}Audit.lean`) and the kernel tests
   (`Tests/Ix/Kernel/{Reader, CertifiedEntry, Authentication, Contracts,
   Projection, BlockOrder, AddressPure, ...}`), whose `#guard`s run at elaboration on
   fixtures re-keyed to their BLAKE3 addresses; the certified fixtures
   (`IxCK/Fixtures/*`, authenticated under a hasher-free fixture hash) were
   already built in step 1;
3. with `--with-model`, the `Models/SetTheory` build and its audit;
4. `kernel-layering` (`Tests/Ix/Kernel/Layering.lean`, derived from
   con-leche's `tests/layering.sh`): the kernel's import layering, each file
   of `IxCK/Kernel/` classified by its path (`Tests/Ix/Kernel/KernelLayout.lean`;
   an unclassified file fails): the checker never imports the theory, the
   base never imports the model lane, the rules fence and its five recorded
   doors, and the boundary: the checker and the theory import only
   themselves, `Init`, `Std`, at elaboration time `Lean`, and of Ixon only
   the binder-contract data types `IxCK.Ixon.Types.{Modes,Contract}` that
   `BinderMeta` carries (Ix's boundary modules `Admission`, `Ixon`, `Audit`,
   `Ingress`, `Egress`, `Ref` and `Search` import the kernel, not the
   reverse);
5. `kernel-trust-surface` (`Tests/Ix/Kernel/TrustSurface.lean`, derived from
   con-leche's `tests/trust-surface.sh`, with its lexer self-test on
   `Tests/Fixtures/trust-surface/lexer.lean`): a lexer-based scan of the
   checker, the theory, the admission hash (`Ix/Address/Admission.lean`) and
   the display modules (`Ix/KernelDisplay/*`, `Ix/LeanIngress/Names.lean`)
   for compiler escapes (`unsafe`, `implemented_by`,
   `computed_field`, `native_decide`, `extern`, `sorry`, `axiom`, ...); the
   escapes in the allowlisted files (`IxCK/Kernel/{Expr,Name,Key,Exclusive,
   BasisGen}.lean`, `Ix/Address/Admission.lean`, and the display-only read
   `Ix/KernelDisplay/Peek.lean`) are permitted, each with its justification
   in the tool's header;
6. `kernel-entry-cases`: Lean declarations of
   `Tests/Ix/Kernel/EntryCaseDefs.lean` compiled by Ix's compiler and
   submitted as canonical bytes to `Ixon.Authenticated.checkBytes`, each with
   an exact expected verdict (accepts: a definition, a theorem, an inductive
   with its recursor, a structure with a projection, a quotient reduction,
   `Nat` literals and a certified `Nat` operation, a `String` literal, a nested
   inductive, a mutual inductive with definitions by structural recursion
   over it, a mutual and nested inductive, the opaque face of a `partial`
   definition; rejects: truncated bytes under their own hash, the same bytes
   under the record's address, a blob changed under its address, a duplicate
   constant, a duplicate blob, `Nat.rec` with a wrong K flag and `Nat.add`
   with another value under their addresses (refused at authentication);
   declines: a `partial` definition's `_unsafe_rec` body, a non-standard
   axiom, a theorem of `False`). Rows go to
   `.lake/build/kernel-entry-cases.jsonl`;
7. `kernel-meta-names`: the `.meta` and `.source` names against Lean's, on
   ill-typed declarations and the fixtures.

The CI job runs the same gate and keeps the entry-case log.

### On a toolchain bump

When `lean-toolchain` changes, by hand or by the toolchain bot
(`.github/workflows/update.yml`, which moves the toolchain files and the
Mathlib tag but regenerates nothing), the change also does the following.

1. **Toolchains.** `lean-toolchain`, `Benchmarks/Compile/lean-toolchain`,
   `IxCK/lean-toolchain`, `IxCC/lean-toolchain` and `Models/SetTheory/lean-toolchain` name the
   same release (CI's `lean-test` job compares them). The model's `mathlib`
   `rev` in `Models/SetTheory/lakefile.toml` is Mathlib's tag for that
   release; after changing it, `lake -d Models/SetTheory update mathlib`
   refreshes `Models/SetTheory/lake-manifest.json`.
2. **The default role table.** A new toolchain moves Init's addresses:
   regenerate `RoleData.lean` with the three commands under "Regeneration"
   above (the exact certificate inputs are recorded in the generated header). The
   specifications, `specVersion` and the digest do not change. Until then
   the moved constants are not bound, and the inputs and entry cases that
   need them decline.
3. **Frozen audit records.** The runtime closures (`N compiled functions;
   inherited externs M, ...`), the extern differences and the frozen
   `#check` statements are `#guard_msgs` records in
   `IxCK/Kernel/Audit/Roots.lean`, `IxCK/Ixon/Audit.lean` and
   `IxCK/Kernel/Admission/Audit.lean` (built by `lake -d IxCK build
   --wfail`), and in `Ix/Ixon/Projection/Audit.lean` and
   `Ix/Ixon/BlockOrder/Audit.lean` (built by `lake build --wfail
   Ix.Ixon.Projection.Audit Ix.Ixon.BlockOrder.Audit`). A record that no
   longer matches fails the build and prints the message its command now
   produces; re-record it by replacing the record's docstring with that
   message, and update the closure table above and the counts in
   `Roots.lean`'s module docstring. Any other `#guard_msgs` that fails (the
   controls in `IxCK/Kernel/Audit/Runtime.lean`, the axiom records in
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

1. **Codec proofs.** `IxCK/Ixon/Verify` proves the codec the byte stage runs.
   Re-prove it for the new grammar keeping the name and statement of every
   lemma used outside `IxCK/Ixon/Verify` (the `#check` records in
   `IxCK/Ixon/Audit.lean` list them; the byte stage's theorems in
   `IxCK/Kernel/Admission/Bytes/Theorems.lean` must then build unchanged).
   `lake -d IxCK build --wfail IxCK` is the acceptance.
2. **Primitive addresses.** `lake exe ixon-v4-primitives` compiles the
   primitive closure into `$IX_IXON_V4_DIR` and fails if
   `Tests/Fixtures/ixon-v4/primitives.tsv` differs from the live addresses;
   copy the file it names over the fixture. Mirror every changed address
   into `crates/common/src/prim_addrs.rs` (`PrimAddrs::new`),
   `Ix/PrimAddrs.lean`. IxVM reads every primitive through the claim's
   binding and has no address literal but its specification digest, which
   `prim-addrs` checks. The suites
   `prim-addrs` and `primitive-address-parity` and
   `lake exe ixon-v4-tests --primitives` must pass.
3. **Generated IxVM Rust.** `lake exe ix codegen` regenerates
   `crates/ixvm-codegen/src/*.rs` from the IxVM sources and `Ix/IxVM/Kernel/RoleSpec.lean`, the role specifications
   rendered as circuit terms (`Ix/IxVM/RoleSpecGen.lean`), which also
   changes with `specVersion` or the specification digest; `lake exe ix
   codegen --check` must pass.
4. **Fixtures.** `lake exe ixon-v4-tests --export-fixtures --export-handoff`
   writes `claims.tsv`, `addressed.tsv`, `resource.tsv` and the handoff set
   to `$IX_IXON_V4_DIR`; copy them into `Tests/Fixtures/ixon-v4/` after
   `lake exe ixon-v4-tests` validates them. If they moved, so did the
   catalog claim digest (`Tests/Ix/Claim.lean`, `crates/ixon/src/proof.rs`);
   re-pin it from the serializers' output. The independent expression vectors
   (`Tests/Fixtures/ixon-v4/expressions.txt`) are written by hand from the
   specification.
5. **The default role table**, as step 2 of a toolchain bump: the three commands under
   "Regeneration" above. Write the two environments to fresh files, never
   to paths that are symbolic links to another format's stored environments:
   the commands write through a link.
6. **The reader test's frozen records.** `Tests/Ix/Kernel/Reader.lean`
   holds compiled records as bytes. `lake exe kernel-entry-cases --records
   nested-through-nested` and `--records level-comparison` print them
   (`lTreeRecords`, `levelRecords`) with the names of the blocks they
   belong to; replace the lists and the owner addresses with the output. The
   byte vectors of `IxCK/Fixtures/{Codec,ParserWork,ByteAdmission}.lean`
   are the codec's: rewrite them for the new grammar (their `#guard`s run
   when `lake -d IxCK build --wfail` elaborates them).
7. **IxVM costs.** `lake test --wfail -- --ignored ixvm` reports every
   kernel-check FFT-cost pin of `Tests/Ix/IxVM.lean` and the shard pin in
   `Tests/Main.lean` that moved; set each to the measured value.
8. **Frozen audit records**, as step 3 of a toolchain bump, including the
   codec's own closure in `IxCK/Ixon/Audit.lean`.
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
`ConLeche/Kernel/NatOpPins.lean` is not included: Ix validates the bound
constants against fixed specifications (`IxCK/Kernel/Roles.lean`) with the
role table's evidence (the default table: `IxCK/Kernel/Ixon/RoleData.lean`).

**What was changed.** Every file was moved (`ConLeche/Kernel/X` and
`ConLeche/X` to `IxCK/Kernel/X`) and its namespace and module prefix renamed
(`ConLeche.Kernel` and `ConLeche` to `Ix.Kernel`, as whole names). These
files carry further changes:

| File | Change | Why |
| --- | --- | --- |
| `IxCK/Kernel/{CheckerBase,Checker,DeclCheck}.lean`, `IxCK/Kernel/Cached/ParsedC.lean` and the proofs that consume them; the former `TrustAxioms.lean` was removed | `Roles` replaces `NatOpPins`; the operations' install gate checks the role table's evidence (`checkDivModEvidence`, `evidenceLocal`); compiler-trust support is excluded from the certified theory; the proofs take `Evidences` where they took pin lists | upstream's `NatOpPins` splices JSON pin dumps; Ix binds primitives by a role table and validates them against fixed specifications |
| `IxCK/Kernel/Verify/Cached/{AgreeFloor,PushChain}.lean` | `import all Init.LetFun` | Lean 4.34.0 no longer exposes `letFun`'s body, which these proofs unfold |
| `IxCK/Kernel/Frontend/InModel/Nested.lean` | container groups formed largest family first | Larger container families claim their members first, preventing overlapping nested-model groups from emitting a member twice |
| `IxCK/Kernel/Level.lean`, `IxCK/Kernel/Verify/Level.lean` | the `(param, max)` case falls back on Géran's sublevels, with its soundness case | nanoda's comparison is incomplete there, and Ixon's canonical levels reach the gap (Mathlib's `RatFunc.liftOn_def`) |
| `IxCK/Kernel/Expr.lean`, `IxCK/Kernel/Cached/ExprNodes.lean` | `Level` caches its has-parameter bit (`hasParamData`), and `levelHasParam` runs as it (`levelHasParam_eq_csimp`) | the walk visited a level shared as a DAG once per path, at every `.sort` node built |
| `IxCK/Kernel/Cached/{StateC,CoreC}.lean`, `IxCK/Kernel/Verify/Cached/{SimCEff,DiscC4,DiscC6}.lean` | the binder-telescope loops' peel fuel is `peelFuelToM` (the binders before the first closed residual the memo holds) in place of the constant `peelFuel`, at the ∀ and λ clauses of inference and annotation, with `peelFuelToM_eff` in place of `peelFuelM_eff`; `isEquivLM` simplifies through `simplifyMemoC` (`Level.simplifyGo` seeded with `lsimpC`; `simplifyMemoC_spec`) | a chain `T (j+1) = T j → T j` re-peeled the telescope below each step and annotation rebuilt it unshared: quadratic time and memory, and quadratic comparison of two annotations ("Running time") |
| `IxCK/Kernel/Cached/{StateC,CoreC}.lean`, `IxCK/Kernel/Verify/Cached/{SimCEff,BinderLoopC,DiscC4}.lean` | the cached core hash-conses the ∀ rule's levels: a table `lvlIntern` in `CState`, and `internLM (.imax u v)` in place of `pure (.imax u v)` in `inferPisOutI` and `inferBodyIOI`; `internLM` returns its argument on every branch (a hit is returned after `==` confirms it), proved by `internLM_eff` (with `CSOK.withIntern`: no clause reads the table), which the two simulation steps take in place of `pureEq_eff`. The rule, the model and the reference core are upstream's | without it the binder loop rebuilds the level of a telescope's tail as a new object equal to the one built before, and a `let` chain over one shared type is cubic ("Running time"). Earlier (`c076298dc`) the rule's level was folded (`Level.mkIMax`); withdrawn so that the rules tier is upstream's |
| `IxCK/Kernel/Expr.lean`, `IxCK/Kernel/Cached/ExprNodes.lean` | the executed level equality (`Level.beqPtr`, through `Level.beq_eq_beqPtr`) decides its structural case by a descent memoised on the pairs it proves equal (`Level.decMemo`, `Expr.beqMemo`'s arrangement); `Level.beqPtr_eq` is unchanged in statement | the folds compare two levels, and on equal levels built apart as DAGs the structural walk visited their trees ("Running time") |
| `IxCK/Kernel/Level.lean` | the executed `simplify`, `leqCore`, `zeronessOf` and `isNeverZero` are memoised per call on the nodes (for `leqCore`, the subproblems) they finish (`simplifyFast`, `leqCoreFast`, `zeronessOfFast`, `isNeverZeroFast`, each swapped in by a `@[csimp]` theorem proving it equal to the unchanged specification), and the memoised `leqCore`'s case split substitutes with a memoised `subst` (`substMemo`); below a small tree size each runs an exact copy of the plain recursion | the walks visited a level shared as a DAG once per path, and `leqCore` re-solved the subproblems its distributions meet again ("Running time") |
| `IxCK/Kernel/Cached/CoreC.lean`, `IxCK/Kernel/FEnv.lean`, `IxCK/Kernel/Units.lean` | the executed `whnfCoreLoopI`, `whnfLoopI` and `defeqLoopI` are loops over a twin of the step that returns its tail call of the continuation (`whnfCoreLoopFast`, `whnfLoopFast`, `defeqLoopFast`), and the executed `mkFEnvGo` and `unitsGo` a fold and an accumulator loop (`mkFEnvGoFast`, `unitsGoFast`), each swapped in by a `@[csimp]` theorem proving it equal to the unchanged function | the loops called their continuation through a closure, which kept native frames per reduction step, and the two recursions one per constant ("Native stack") |
| `IxCK/Kernel/Expr.lean` | the node hash is 64 bits in a computed field of its own (`Expr.hashW`, the untruncated `mixHash` recurrence); the packed word keeps the ranges and the flag, its upper 33 bits reserved; equality's fast reject tests both words (`beqMemo_eq` unchanged in statement) | a chain built by one step cycled through the 32-bit hash, and memo probes then descended equal-hash terms ("Running time") |
| `IxCK/Kernel/Cached/{Installed,Policy}.lean` | `checkPendingTasks` takes a bound on its tasks (`workers`: `none` keeps one task per 64 records, `some 0` walks on the calling thread, `some w` cuts the walk into at most `w` contiguous chunks, `phaseBChunkFor`), and `checkDecls`, `checkDeclsUnder` and `checkDeclsWithUserAxioms` take the fold's settings (`FoldConfig`, defaulted) that carry it; `checkPendingTasks_eq` now holds for every bound, and `checkDecls_cfg`, `checkDeclsUnder_cfg` state that the settings change no result | phase B spawned one task per 64 records, so the threads a run could start (each reserving its stack) grew with the input, and a run under an address-space limit aborted creating one ("Limits") |
| `IxCK/Kernel/MainTheorem.lean` | only `model_exists` kept | the NDJSON corollary needs a frontend Ix does not use |

Ix's own files under `IxCK/Kernel/` are `Admission.lean` and the `Admission`
directory (the certified entry, its byte stage, theorems and audit),
`Roles.lean` (the role specifications), `Ref.lean`, `Search.lean`, the `Audit`, `Ingress`, `Egress` and `Ixon`
directories (the Ixon reader and its specification, the role table, the
default table and prelude, the record store, the projection writer and the audits), and
`LevelGeran.lean` and
`Verify/LevelGeran.lean` (Géran's sublevels and their soundness and
completeness), which the changed `Level` files import.

**Notices.** `IxCK/Kernel/LICENSE-CON-LECHE` is con-leche's Apache-2.0 licence
and `IxCK/Kernel/NOTICE` states the origin, the revisions and the changes;
`Models/SetTheory` carries its own copy for the file it takes from con-leche.

**Builds.** `IxCK/lakefile.lean` owns the certified modules, whose module
names live under the `IxCK` root inside the package directory:
`IxCK.Kernel` is `IxCK.Kernel` and everything under
`IxCK/Kernel/`, `IxCK.Ixon` is the pure address and codec modules
(`IxCK.Address.Core`, `IxCK.Ixon.*`), and `IxCK.Fixtures` is the
four certified fixtures. Declaration namespaces are unchanged: the kernel
still declares `Ix.Kernel.*` and the codec `Ixon.*`; only `import` lines name
the `IxCK.` modules. The root package depends on `ix-ck`, every
workspace that requires it reuses its artifacts in the repository's
`.lake/kernel` directory, and the standalone build checks that these sources,
fixtures included, need only the Lean toolchain.

In the root package, `Ix` is the main library, with Lake's default roots and
globs, and carries the Rust linkage; a default build follows `Ix.lean`'s
imports. Nothing the dependency owns is under the `Ix.` module root, so `Ix`
never shadows it. `IxSharingVerify` owns the sharing proofs under the
`IxSharingVerify` module root (namespace `Ix.Sharing.Verify`), and
`KernelEntry` owns the benchmark helpers. The root test library imports the
certified fixtures from `IxCK.Fixtures`.

`IxCK.Kernel` has one special option:
`linter.deprecated` is off, so the con-leche-derived sources, written for
Lean 4.33.0, build under `--wfail` on 4.34.1 without renaming the deprecated
`if_pos`/`if_neg`/`dif_pos`/`dif_neg` lemmas they use (2,885 uses in 209
files). Ix's own files there do not rely on it: they build without warnings
with the linter on.

**Bringing over an upstream change.** By hand: take upstream's diff between
the recorded revision and the new one for the files concerned, map its
paths (`ConLeche/Kernel/X` and `ConLeche/X` to `IxCK/Kernel/X`) and names
(`ConLeche` to `Ix.Kernel`), apply it, update the revisions in
`IxCK/Kernel/NOTICE`, and run the full gate. A module the closure newly
imports is added the same way. A changed closure moves the frozen counts;
re-record each with its explanation, and re-record changed statements.

## Limits at the command line, and exit codes

Every host that runs the kernel on input it did not make reads each field of
`Admission.Limits` ("Limits" above) as a setting (`IxCK/Host/Limits.lean`,
namespace `Ix.Kernel.Host`, outside the certified closure): its flag if given,
else its environment variable, else the host's default (`resolve`). A value must
be a positive whole number in decimal; anything else, `0` included, is a usage
error that names the flag or the variable (exit 2). The settings given by a flag
or a variable are printed, with their sources, before the kernel runs
(`kernel limits: max-depth 20000 (--max-depth), …`); nothing is printed when all
are at their defaults.

| field | flag | variable | `ix check-lean`, `ix verify-host`, `ix compile`, `kernel-check-ixe` default | `ixcc` default |
| --- | --- | --- | --- | --- |
| `maxRecords` | `--max-records` | `IX_KERNEL_MAX_RECORDS` | 2^22 | 16,384 |
| `maxBlobs` | `--max-blobs` | `IX_KERNEL_MAX_BLOBS` | 2^22 | 16,384 |
| `maxTotalBytes` | `--max-total-bytes` | `IX_KERNEL_MAX_TOTAL_BYTES` | 2^34 | 16 MiB |
| `maxRecordBytes` | `--max-record-bytes` | `IX_KERNEL_MAX_RECORD_BYTES` | 2^28 | 1 MiB |
| `maxRecordUnivNodes` | `--max-record-univ-nodes` | `IX_KERNEL_MAX_RECORD_UNIV_NODES` | 2^26 | IxCC's decoder's node budget |
| `maxDepth` | `--max-depth` | `IX_KERNEL_MAX_DEPTH` | 16,384 | 16,384 |
| `workers` | `--workers` | `IX_KERNEL_WORKERS` | unbounded (one phase-B task per 64 records) | unbounded |

`kernel-check-ixe` reads the variables only (it is a measurement harness; its
flags are its own). `--workers` keeps the meaning it had on `ix check-lean`
(the requested worker count) and on `ix compile` (the compiler's worker count,
default 32), and, given, also bounds the tasks of the kernel's phase B;
`IX_KERNEL_WORKERS` applies to the kernel when the flag is absent. A host passes
a bound to phase B only when the flag or the variable is given: by default the
entry runs as it did, one task per 64 records over the runtime's pool.

**A decline by a limit** is reported in one form by every host, and exits 6:

```text
declined by the depth limit (16384, default); raise it with --max-depth N or IX_KERNEL_MAX_DEPTH=N
```

naming the limit, its value, its source (`default`, the flag or the variable)
and how to raise it. A limit only turns an answer into a decline: an input
accepted under some limits is accepted under any larger ones with the same
result, so an artifact, object or certificate made under raised limits is the
one the defaults give, and a verifier run under lower limits than its producer
declines (exit 6); it does not reject. A host statement (`docs/host-admission.md`)
does not record the limits it was issued under. The fixed bounds ("Five bounds
are fixed" above: the reference core's loop fuels, `Level.defaultFuel`,
`checkFuel`) are not settings; their exhaustion is a fixed decline, exit 3.

**Exit codes** of the hosts that run the kernel (the one table; the sections
below refer to it):

| exit | meaning |
| --- | --- |
| 0 | `ix check-lean`: everything asked for passed; for a whole bound run, through the certified entry. `ix verify-host`: the statement replayed. `ix compile`, `ixcc`: the output written. `kernel-check-ixe`: the run completed; its rows carry each record's outcome, a rejection included |
| 1 | an infrastructure failure: an unreadable file, an artifact the loader refuses; `ix compile`: also a failure of the compile or of its typing; `kernel-check-ixe`: also a check that raises an error other than a decline by a limit; `ixcc`: also its own refusals and declines, as before, a record nested past IxCC's own envelope bound among them ("Which limit a deep record meets in `ixcc`" below) |
| 2 | a usage error: a bad flag or selector, a malformed limit setting (`0` included), a run that certainly cannot fit the address-space limit ("Under an address-space limit" below), `ixcc` unable to re-run itself; `ix check-lean`: also a selected name that resolves to no declaration, or a host statement the run cannot issue (a selected, capped, unbound, `--allow-declined` or conditional run); `kernel-check-ixe --allow-user-axioms`: an artifact whose binding does not bind `sorryAx`, `propext` and `Classical.choice` |
| 3 | `ix check-lean`: a declaration failed (or, under `--allow-declined`, a declaration or dependency record was rejected), or the artifact was refused. `ix verify-host`: the replay rejected or failed. Both: a fixed decline (a fixed bound's exhaustion, above) |
| 4 | `ix check-lean`, partial: every declaration passed, but the whole artifact asked for carries no role binding, so its admission did not run |
| 5 | `ix check-lean`, conditional: everything passed, but only with the listed user axioms admitted |
| 6 | declined by a limit a setting raises (every host, `ixcc` included): the message names the limit, its value and source, and the flag and variable that raise it |
| 7 | `kernel-check-ixe`'s watchdog (`CHECK_IXE_WATCH_MS`, `CHECK_IXE_WATCH_MB`, "Environment check" below); `--guarded` reruns on it |
| 128 + n | `ixcc`: its second process (below) died by signal n (Lean's `wait` reports a death by signal so; `tests-kernel-front` kills the second process with `SIGKILL` and reads 137) |

**Threads.** `ix check-lean`, `ix verify-host` and `ix compile` set the stack of
every thread started afterwards to `Limits.stackFor` (16 KiB per level of
`maxDepth`, at least 256 MiB) before they start any task
(`Ix.Cli.KernelLimits.prepareThreads`), and run everything after option
parsing, the loading of the artifact included, on one dedicated thread of that
size. `kernel-check-ixe` keeps its caller's stack (`LEAN_STACK_SIZE_KB`, else
the runtime's default, 1 GiB: measured on Lean 4.34.1, its thread stacks are
mappings of 1,048,576 KiB, and of 8,320 KiB with `LEAN_STACK_SIZE_KB=8192`),
which `initstd-stack` relies on. `ixcc` links no native code and so re-runs
itself once on a stack of `stackFor` (`IxCC/IxCC/Cli/Main.lean`:
`LEAN_STACK_SIZE_KB`, `IXCC_REEXECED`, the off switch `IXCC_REEXEC=0`), giving
the second process `LEAN_NUM_THREADS` set to `--workers` when the caller gave
`--workers` and left the variable unset, so that `--workers` alone bounds the
runtime's pool there.

**Under an address-space limit** (`ulimit -v`), the Lean runtime aborts the
process when it cannot create a thread ("failed to create thread", exit 134),
which no host can intercept, and the number of threads is the runtime's: its
pool is `LEAN_NUM_THREADS`, else the processor count, and it starts another
worker when one blocks on a task, whatever `--workers` says (on a 64-processor
machine `ix check-lean` ran 38-39 threads, with `--workers 1` too, and
`kernel-check-ixe` 91-133, with `IX_KERNEL_WORKERS=1` too). So every host
(`Ix.Kernel.Host.spaceCheck`, with the stack its threads will have) refuses a
run only when it certainly cannot fit: one stack over the soft limit, or, when
the caller gave `--workers` or `IX_KERNEL_WORKERS` = w, w stacks over it
(exit 2, naming the settings that lower it). Otherwise, when the estimate
(twice the pool plus 8 threads, each with its stack and a 64 MiB malloc arena,
plus 1 GiB) does not fit, it prints one line on standard error before it starts,
`warning: this run may fail to create a thread under the address-space limit
…`, with the estimate and the settings that lower it (`LEAN_NUM_THREADS` first,
then `--workers`/`IX_KERNEL_WORKERS`, `--max-depth`/`IX_KERNEL_MAX_DEPTH`, and
for `kernel-check-ixe` `LEAN_STACK_SIZE_KB`), and runs. To run under a cap,
bound the pool and the workers together, `LEAN_NUM_THREADS=n` with `--workers n`
(`IX_KERNEL_WORKERS=n`), and give `kernel-check-ixe` a stack,
`LEAN_STACK_SIZE_KB=8192` for example. Measured on KI's Task 4 artifacts
(248 records each; 64 processors; job `KK-pm`): under 32 GiB, `ix check-lean`
at its defaults ran (38-39 threads, peak address space 13.7-16.9 GB; the
estimate, 43.5 GiB, prints the warning);
`kernel-check-ixe` with no `LEAN_STACK_SIZE_KB` aborted under 32 GiB and 16 GiB
(91 and 76 threads), and ran with `LEAN_STACK_SIZE_KB=8192` (97-133 threads,
8.9-11.6 GB).

**Which limit a deep record meets in `ixcc`.** IxCC reads the whole envelope
itself before the kernel sees it (`IxCC.Ixon.V3.decodeAnonymousEnv`): each
record with the kernel package's canonical decoder, then IxCC's own depth bound
(`withinKernelDepth`, 2,560 levels with shares expanded). A record nested past
2,560 levels is therefore IxCC's refusal (exit 1, `ixcc: ingress: decode: …
nests deeper than the kernel reads (2560, shares expanded)`) before the
kernel's depth limit (16,384) could decline it (exit 6); `ixcc` meets the
kernel's limit only under a lowered setting. IxCC's decoder recurses once per
level before that bound: the re-executed stack (256 MiB at the defaults) holds
a record of IxCC's 1 MiB budget at any nesting its bytes allow, and with
`IXCC_REEXEC=0` on 8 MiB the same record overflows the stack
(`tests-kernel-front`'s command-line part). Scanning before IxCC's decoder, as
the root's loaders now do, is open (IxCC's roadmap, "Hardening").

**The loaders scan before they decode.** The root's artifact loaders
(`Ixon.deEnvVerifiedLazy`, used by `ix check-lean` and `ix verify-host`;
`Ixon.deEnv`; the streaming load of `Ix/KernelCheck/Stream.lean`) decode each
record with the codec, which recurses once per level, before any entry runs.
Each record's bytes are now scanned first with the entry's own scan
(`Depth.within`, at the run's `maxDepth`), and a record nested past it is
refused as a decline by the depth limit (`Ixon.depthLimitError`, exit 6)
without being decoded.

## Environment check

The environment check measures coverage on a compiled environment (an
`.ixe`); it is not a certified verdict. `kernel-check-ixe`
(`Benchmarks/Kernel/CheckIxe.lean`, entry `CheckIxeMain.lean`) reads an
`.ixe`, orders its primary constants (the prelude's first, then dependencies,
`Nat`-operation grounds and literal edges), reads each constant with the Ixon
reader and installs and checks it one constant at a time with an incremental
step of the verified fold (`Ix/KernelCheck/Step.lean`),
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

Usage: `kernel-check-ixe [--load stream|eager] [--jobs <n>] [--allow-user-axioms]
<input.ixe> <output.jsonl> [limit]`. The records are streamed by default
(`Ix/KernelCheck/Stream.lean`): the order and the record views
are built over record skeletons, and each record is decoded in full at its
turn and dropped once it is read. `--load eager` decodes and keeps the whole
environment up front. `--jobs <n>` installs every record first and then runs
the recorded checks on `n` worker threads
(`Ix/KernelCheck/Pool.lean`). All three write the same rows
(`kernel-check-ixe --compare` shows it); with `--jobs`, a row's `micros` is
its install plus its checks. The check is strict: a safe axiom other than the
standard three declines. `--allow-user-axioms` admits such axioms on every
path, the read cache's included, after refusing (exit code 2) an artifact
whose binding does not bind `sorryAx`, `propext` and `Classical.choice`, and
ends its log with `CONDITIONAL on K user axioms:` and the axioms it admitted
("User axioms (uncertified)" above). A checker failure's reason is rendered by
`.meta`: its keys spelled with the names the `.ixe`'s metadata gives them and
the first eight hexadecimal digits of their addresses, `Nat.add@a1b2c3d4`
(`Reader.spellWith`); the verdict is the `.anon` run's.
`kernel-check-ixe --meta <input.ixe> <output.jsonl> [limit]` is the erasure
test: every record read and checked at `.anon` and at `.meta` (named from the
metadata) and the runs compared record by record (readings by hash and term
by term, outcome, fold position, failure with its keys mapped), failing on
any difference or on a name coverage under 99% (Init+Std: 97,906 records, no
difference, 99.998% of 2,576,066 binders and lets named, about 230 s). Its
rows print a failure with its terms and Lean's names
(`Ix.KernelDisplay.renderFailure`). Environment:

- `CHECK_IXE_WATCH_MS` (default 60000) and `CHECK_IXE_WATCH_MB` (default 20000):
  a watchdog ends the run with exit code 7 when one constant's check exceeds
  the time or the process's resident memory exceeds the size, and appends
  the constant's address to `<output>.runaway` (with `--jobs`, every
  worker's check is watched). A run whose check raises an error ends with that
  error: exit code 6 for a decline by a limit (the artifact's admission, or the
  loader's depth scan), 1 for anything else (an artifact the loader refuses); until
  the watchdog was stopped on every way out, such a run hung with no CPU and
  nothing printed. The resident size includes what the driver
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
  cache (`Benchmarks/Kernel/CheckIxeReadCache.lean`);
- the kernel's limits, by their variables only (`IX_KERNEL_MAX_RECORDS`,
  `IX_KERNEL_MAX_BLOBS`, `IX_KERNEL_MAX_TOTAL_BYTES`, `IX_KERNEL_MAX_RECORD_BYTES`,
  `IX_KERNEL_MAX_RECORD_UNIV_NODES`, `IX_KERNEL_MAX_DEPTH`, `IX_KERNEL_WORKERS`;
  "Limits at the command line, and exit codes" above), and `LEAN_STACK_SIZE_KB`,
  the stack it keeps (it does not resize its threads).

Run one environment check at a time, under a memory cap, with no concurrent build.
`kernel-check-ixe --report` and `--summary` summarize a run's rows, and
`--compare` and `--paired` compare runs (`Benchmarks/Kernel/README.md`).
Mathlib's `.ixe` comes from `Benchmarks/Compile/CompileMathlib.lean`
(`Benchmarks/Compile/README.md`).

### `ix check-lean`

`ix check-lean <input.ixe>` (`Ix/Cli/CheckLeanCmd.lean`) is the host checker
behind the merge-queue gate `initstd-reference` and the `ooc` benchmark. It
authenticates the bytes and checks every declaration, or a selection
(`--consts`, `--consts-file`, `--max`), with the same incremental step as the
environment check. When a whole run of a bound artifact passes, it runs the
certified entry (`Ix.HostAdmission.certify`) and reports the host statement,
which `--host-out` and `--host-store` persist (`docs/host-admission.md`). A
whole bound run prints `bound roles: N admitted, M refused`: a role is refused
when the run refused its record. In meta mode, the default, an artifact whose
published role names disagree with its binding is refused before any check
(`Ix.RoleBinding.Compile.roleBindingError`, as the compiler's `finalize`
runs it).

Checking is strict. With `--allow-user-axioms` a whole run runs the entry under
the `allowUser` policy once ("User axioms (uncertified)" above), and the user
axioms it lists choose the verdict. With none, its receipt is the certified
entry's and the run reports and issues the host statement as without the flag.
With some, the run prints

```text
[check-lean] whole artifact: CONDITIONAL on K user axioms:
[check-lean]   <address> <name>
```

one line per axiom, the name in meta mode only, and never the `accepted all`
line of a certified run. A selected run whose declaration checks read a user
axiom prints the same list under `selected checking:`.

Its exit codes, 0 to 6, are in the table of "Limits at the command line, and
exit codes" above.

`--allow-declined` runs the record-by-record check (as the `ooc` whole-env
benchmark uses it on upstream libraries that contain `Lean.trustCompiler` or
`unsafe inductive` declarations): declarations outside `IxCK`'s fragment
(`decline`) and their dependents (`blocked`) are tolerated, whole-artifact
admission does not run and no host statement can be issued, and the run exits 3
only when a checked declaration or support record has outcome `reject`.

`--json <file>` writes benchmark results rows (`Ix.Benchmark.Results`). A run
writes one row, keyed by `--json-name` (default `env`). With a selection it
runs each name's full closure on its own and writes one row per name, keyed
`<json-name>/<name>` when `--json-name` is given; a name that resolves to no
declaration is reported, and the other names still run. In every row,
`constants` is the number of records the run checked or read, and `throughput`
is that number per second; `status` names the run's verdict as its exit does:
`ok` (0), `rejected` (3), `partial` (4) or `conditional` (5). A host statement
the run cannot issue (exit 2) leaves `status` at the verdict.
`--per-const <file>` writes one CSV row per record for the same run or runs. A
run exits with the same status with `--json` as without.

