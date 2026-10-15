# Certified Lean kernel

Ix's certified checker, `Ix.Kernel.Cached.checkDecls` at `.verified`, is
derived from [con-leche](https://github.com/leanprover/con-leche)'s verified
checker: `IxC/Kernel/**` holds a modified copy under the namespace
`Ix.Kernel` (see "Origin and attribution" below), run on Ixon records by Ix's
reader in `IxC/Kernel/Ixon/`. The certified API is
`Ix.Kernel.Admission.checkBytes` (`import IxC.Kernel.Admission`; its theorems
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

Nothing here certifies the Lean-to-Ixon compiler, the Rust checker, `Ix.Tc`
or IxVM. An accepted environment has a model; that it is the environment
the original Lean source meant is outside the claim.

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
entry and its two variants at `Address.admissionHash`
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
theorems and audit beside it: `IxC/Kernel/Admission.lean` (the entry, its
`Error` and `Outcome`), `IxC/Kernel/Admission/Bytes.lean` (the byte stage
and its `ByteError`), `IxC/Kernel/Admission/{Theorems,Bytes/Theorems,
Audit}.lean`; the variants `Ix/Ixon/{Projection,BlockOrder}.lean` with
`Ix/Ixon/{Projection,BlockOrder}/{Theorems,Audit}.lean`; the instantiations
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
| canonical per-record decoding within byte and universe-node limits | `Admission.decodeRecords` | `.decode position address reason` |
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
admits a binding first. Two variants share the
byte stage and the checker, and take the same `hash`:
`Ixon.Projection.checkBytes` reconstructs omitted projection records
(addresses by `hash` of their canonical bytes) before checking, and
`Ixon.BlockOrder.checkBytes` also checks the
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
| `.mismatch` | reject | a key is not the hash of the bytes stored under it |
| `.read _ (.malformed _)` | reject | the records describe no declaration (a missing reference or blob, a bad table index, a recursor header that disagrees with its block, ...) |
| `.read _ (.declined _)` | decline | unsupported: unsafe or `partial` definitions, unsafe axioms, an inductive block whose recursor is not in the input, a mutually recursive definition block, a block the in-process modeller declines |
| `.binding` | reject | the role table's section is not the hash of its bytes, not canonical, or not well formed |
| `.prelude` | decline | a corrupted committed prelude |
| `.kernel` | decline | every checker verdict: the checker reports fuel exhaustion as `internal` and a failed conversion search as `invalid`, and neither is independent evidence that the input is wrong |

The variants keep their own errors (`Ixon.Projection.CheckError`,
`Ixon.BlockOrder.CheckError`) and the same classifier, `e.outcome`: a
checker failure (`.checker e`) as above, the byte stage
(`Admission.ByteError.outcome`) as `.limit`, `.duplicate`, `.mismatch` and
`.decode` above, and their own failures as follows.

| Error | Outcome | Why |
| --- | --- | --- |
| `Projection.Error.limit`, `BlockOrder.Error.exhausted` | decline | coverage bounds (projection requests; comparison and refinement fuel) |
| `Projection.Error.ownerWidth`, `.conflict`, `.projection (.malformed _)` | reject | an owner key that is not a 32-byte hash, a supplied record that differs from the derived one at its key, a projection the writer finds malformed |
| `Projection.Error.projection` (any other search failure) | decline | the writer did not establish the projection |
| `BlockOrder.Error.malformed`, `.nonCanonical`, `.motiveOrder` | reject | a malformed block, or a block out of canonical (or motive) order |

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
order (`Benchmarks/Kernel/CheckIxeStep.lean`, `order`) satisfies it.

## The theorems

All public theorems are in `IxC/Kernel/Admission/Theorems.lean` (namespace
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

The variants have the same theorems at every `hash`
(`Ixon.{Projection,BlockOrder}.checkBytes_{ok_iff,reading,authentic,has_model,no_proof_of_False}`);
their `checkBytes_authentic` adds that every record the checker read, supplied
or reconstructed, is stored under `hash` of its serialization
(`Projection.Expanded.hashed`). `Ixon.Authenticated.Theorems` states them at
the specification hash `Address.blake3Pure` for the BLAKE3 entries (for
example `Ixon.Authenticated.checkBytes_authentic : … →
Authentic Address.blake3Pure records blobs`).

`Ix.Kernel.Model V env` (`IxC/Kernel/Denotes.lean`) assigns a set
`cval c φ` to every constant at every level assignment such that every
stored constant is a member of what its type denotes (`mem`), what the
built-in `False` denotes is empty (`false_empty`), and what the built-in `Eq`
denotes is set equality (`eq_equality`). Definitional equalities need no
clause: an accepted `rfl` theorem's two sides denote the same set. The
model theorem is `Ix.Kernel.model_exists` (`IxC/Kernel/MainTheorem.lean`,
upstream's statement and proof) at the prepared declarations: it holds for
every declaration array the fold accepts, so the reader owes nothing for
consistency. Definition values come from the kernel's model invariant
`defn_reads` through `Ix.Kernel.Cached.checkDecls_model_defn_values`
(`IxC/Kernel/Ixon/Values.lean`). Theorem and opaque bodies have no value
equation, by upstream's design.

**Fidelity** is what `checkBytes_reading` adds to consistency:

- `WithinBatch` and `UniqueKeys` (`IxC/Kernel/Admission/Bytes/Theorems.lean`): the
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
- `Installed` (`IxC/Kernel/Admission/Theorems.lean`): the reader's output is a
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
  (`IxC/Kernel/Ixon/ReaderSpec.lean`): which key a reference and a member are
  read under (the role's key where the table binds the reference, otherwise
  the input key of the address it is keyed by).
- `RoleTable.ofBytes_eq_some_iff` (`IxC/Kernel/Ixon/RoleTable.lean`): the
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
  the axioms by `matchesPin`; the anchors (`Bool`, `True`, `And`, `Iff`,
  `Nonempty`, `List`, `String`, `Char`, ...) by their install only. That the
  default table binds Init's own constants is the generator's
  verification, not a theorem; the no-False theorems are stated at
  `False`'s role key and hold for any table.

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
(`IxC/Kernel/SetTheory/Core.lean`): membership with extensionality,
unordered pairs, unions, power sets, regularity, replacement as a
Lean-level scheme (the image of a set under any `V → V`), and a strictly
increasing ω-chain of Grothendieck universes interpreting the universe
tower. The Mathlib instance above supplies it from ω inaccessible
cardinals, which its corollaries take as a hypothesis, not as an axiom.

**Input policy.** The entry never falls back to `Ix.Tc` or the Rust
checker; neither is in its closure ("Trust surface"). An input may declare
Init's compiler-trust family (`IxC/Kernel/TrustAxioms.lean`):
`Lean.trustCompiler` installs as an opaque with value `True.intro`,
`Lean.reduceBool` and `Lean.reduceNat` as opaques whose stored values are
certified to be the identity (`checkReduceIdentity`; a drifted value
declines), and `Lean.ofReduceBool` and `Lean.ofReduceNat` as bound axioms
over them. `sorryAx` is tolerated as a declaration and installs nothing; any
use of it declines (`IxC/Kernel/Core.lean`). The well-founded `Nat`
operations are admitted through the role table's evidence, which the
checker checks itself ("Roles and the role table" below).

## Keys, roles and the prelude

**Records** are Ixon v4 constant payloads ([Ixon](Ixon.md), [Ixon v4](Ixon-v4.md)):
TagN integers, and a sharing table per constant. The reader consumes decoded
constants (`Ix.Ixon.Types`) and never sees the integer code; only the byte
stage (`Ix/Ixon/{Codec,Bounded/*,Canonical,WireCheck}.lean`) and its proofs
(`IxC/Ixon/Verify`, including the TagN laws in `IxC/Ixon/Verify/TagN.lean`) do.

**Sharing tables.** In Ixon v4 the table the compiler writes is canonical:
`Ix.Sharing.Exact.canonicalSharingTiered .tagN` of the constant's expanded
roots ([Ixon](Ixon.md), "Sharing System"). The certified entry does not check
that. It accepts any table whose entries refer only to earlier entries: the
reader expands every `Share` against the record's own table and rejects a
reference that is not to an earlier entry as malformed
(`IxC/Kernel/Ixon/Reader.lean`), so the declarations it reads do not depend
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

**Modes** (`IxC/Kernel/Key.lean`). The kernel's types (`Key`, `Expr`,
`ConstantInfo`, `Declaration`, `Env` and what is built from them) take a
`Mode`: `.anon` (Ixon: an input constant is identified by its address),
`.meta` (the same keys, with display data) and `.source` (Lean through
`CanonM`: an input constant is identified by its name). `.meta`'s display is
the reader's output's (`Reader.Read.display`: what the `.ixe`'s metadata says
of the keys a record declares, its Lean names and level names), filled by the
meta reader (`Benchmarks/Kernel/CheckIxeMeta.lean`); the checker's own types
carry none, and no checker code reads a display field
(`IxC/Kernel/Audit/Display.lean`). `.meta` never decides: it explains
failures with names (IXC-PLAN §11).
`Mode.Id md` is what identifies an input constant (an `Address` in `.anon`
and `.meta`, a `Name` in `.source`), `Mode.D md α` the display data (`Unit`
outside `.meta`), and `Mode.Certified` holds of the modes the theorems are
stated at (`.anon`, `.source`; `model_exists` takes it). The checker and its
proofs are generic in the mode. Source mode installs an `Env .source`; the
Ixon entry installs an `Env .anon`.

**Keys** (`IxC/Kernel/Key.lean`, `IxC/Kernel/Ixon/Reader.lean`). The kernel's
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

**Roles and their specifications** (`IxC/Kernel/Roles.lean`). The checker
knows 64 roles (`Ix.Kernel.Role`): the basis blocks (`Eq`, `Nat`, `PUnit`,
`Empty`, `False`, the `Quot` package, every member), `Bool`, `True`, `And`,
`Iff`, `Nonempty` with their constructors and recursors, the literal support
(`String`, `String.ofList`, `List`, `List.nil`, `List.cons`, `Char`,
`Char.ofNat`), the fifteen certified `Nat` operations (`pred`, `add`, `sub`,
`mul`, `pow`, `beq`, `ble` structural; `div`, `mod`, `gcd`, `land`, `lor`,
`xor`, `shiftLeft`, `shiftRight` well-founded), the standard and
compiler-trust axioms, `Lean.reduceBool`, `Lean.reduceNat` and `sorryAx`.
Each has a fixed specification (`Role.spec`): a closed term over role keys
and positional levels, of one of five kinds (a basis `block`'s declarations;
an `anchor`'s type; an operation's type and characterizing equations,
`ops`; an `axiom`'s exact type, or none for the inert `sorryAx`; an
`identity`'s type), its block (`Role.block`, the roles bound together) and
its dependencies (`Role.deps`). The specifications are today's checks
respelled, not new ones (`Role.spec_*` are `rfl` against the data the
checker compares). They carry no address and no input key, so one set
serves every toolchain. The set is versioned (`specVersion`, 1) and has a
digest: BLAKE3 of its canonical encoding (`Ix.SpecDigest.specBytes`, 8863
bytes), computed in the root library because the kernel admits no hasher,
`70fedb021efa660e13618a7dbaa8f76ee0a91ac95fbd353ce05100248872e1ec`
(`Ix/SpecDigest.lean` freezes it; `IxC/Kernel/Audit/Roles.lean` freezes the
set's shape). Four anchors are recorded but not validated by the checker:
`Bool.rec`, `And`, `And.intro`, `And.rec`.

**The role table** (`IxC/Kernel/Ixon/RoleTable.lean`) is input:
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
specification up to `canon`, with a reserved-name reject otherwise; anchors
and axioms by type (`matchesPin`); an operation's type exactly, and its
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

**Binder contracts** (`IxC/Ixon/Types/Contract.lean`). Ixon binders carry
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
`∀[linear] (x : Nat), unique Nat`. The model reads only `pw`, so an
accepted environment says nothing about how a variable is used
(`Tests/Ix/Kernel/Contracts.lean`). The kernel imports these data types
from Ixon, and nothing else
(`kernel-layering`). Source mode gives Lean's binders the defaults and reads
the compiler's resolved contract frames as the compiler lowers them
(`Ix/LeanIngress/Expr.lean`).

**Source mode** uses a fixed table: every role is bound to its own Lean name
(`Ix.LeanIngress.sourceBinding`), and the evidence is the certificate
theorems of `IxC/Kernel/PinGen/Certs.lean` as they appear in the checked
environment, through the same ingress (`Ix.LeanIngress.sourceEvidence`): an
environment without them declines the well-founded operations.

**Prelude** (`IxC/Kernel/Ixon/Prelude.lean`). The checker puts twelve
declarations in front of every fold (`preparePrelude`): the basis blocks `Eq`, `Nat`, `PUnit`,
`Empty`, `False`, the quotient package (four `Quot` constants and
`Quot.sound`), `And` and `Bool`. Here they are the compiled Init's own Ixon
records (`RoleData.prelude`, canonical bytes by address), decoded by the
canonical decoder and read by the same reader under the admitted table
(`preludeFor`). The empty stream installs 27 constants. A stream that
declares a prelude constant is checked on its own record (`preparePrelude`
moves the stream's copy to the front); the prelude's copy fills in where
the stream has none.

**The default table** (`IxC/Kernel/Ixon/RoleData.lean`, generated) binds
every role to the compiled Init's constant of its Lean name, with the
evidence: the structural operations' `.defeq` entries and, for the eight
well-founded operations, theorem records (`RoleData.evidence`, 18 records,
and the blobs their literals use, `RoleData.blobs`) holding the certificate
theorems of `IxC/Kernel/PinGen/Certs.lean` compiled by Ix and closed over
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
lake exe ix compile IxC/Kernel/PinGen/Certs.lean --no-build --out .lake/envs/certs.ixe --consts <the certificate theorems>
lake exe kernel-pin-gen .lake/envs/initstd.ixe .lake/envs/certs.ixe \
  IxC/Kernel/Ixon/RoleData.lean
```

(`--no-build`: the files import only `Init`, and the root package does not
know `IxC/Kernel/PinGen/Certs.lean` as a target of its own.) The full
`--consts` list and the source hashes are in the generated file's header. The
table names addresses, so a toolchain, compiler or format change that moves
Init's addresses requires regeneration; the specifications, `specVersion`
and the digest stay. Soundness does not depend on the table.

## Trust surface

The theorems are about the Lean functions. Trusted beneath them: Lean's
kernel, compiler and runtime, and the inherited `Init`/`Std` primitives the
compiled code reaches (the entry's closure reaches 115 inherited externs,
for example `ByteArray` and `String` primitives and `lean_sarray_dec_eq`,
which implements `ByteArray` equality and therefore `Address` equality).
Among them are Lean's task primitives `Task.spawn` and `Task.get`
(`lean_task_spawn`, `lean_task_get_own`): the fold checks its deferred
records in chunks on pure tasks (`checkPendingTasks`). As Lean functions they
are the resolved task `⟨fn ()⟩` and its field, so the theorems read the
sequential walk (`checkPendingTasks_eq`); execution trusts the runtime to run
a pure closure on another thread, as it trusts it to run any closure. The
runtime sizes the pool (`LEAN_NUM_THREADS`), and no size changes a verdict.
Not in the closure: `ix_rs`, C or Rust BLAKE3, `Ix.Tc`, any JSON or
lean4export parser. The entry and its variants hash only through their
`hash` parameter.

The root library's authenticated entries (`Ixon.Authenticated`) add one
substitution, admitted on an assumption rather than a proof (owner,
2026-10-13): the admission hash `Address.admissionHash` is defined as pure
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
`runtimeRulings` (`IxC/Kernel/Audit/Roots.lean`):

| Construct | Where | Why admitted |
| --- | --- | --- |
| `@[computed_field]` overrides | `Ix.Kernel.Level`, `Ix.Kernel.Expr`, `Ix.Kernel.Name`, `Ix.Kernel.Key` | cached hashes and packed data; a compiler feature, trusted with the compiler |
| project `@[csimp]` | `Ix.Kernel` | each replacement theorem depends on the standard axioms only |
| the codec's TagN `@[csimp]` twins (`getTagN_eq_fast`, `putTagN_eq_fast`) | `IxC.Ixon.Codec` (also `Ixon.Audit.rulings`) | the reader and writer at a fixed flag width with their powers folded; each theorem depends on the standard axioms only |
| `withPtrEq`, `withPtrAddr`, `ptrEq`, `isExclusiveUnsafe` and their unsafe implementations | Lean's `Init` | the continuation carries the obligation that it does not observe the answer |
| `Ix.Kernel.withExclusive` `implemented_by` `withExclusiveUnsafe` | `IxC/Kernel/Exclusive.lean` | its type carries `k true = k false`, discharged by `Subsingleton.elim` |
| elaboration-time `unsafe`, `implemented_by`, `meta import Lean` | `Ix.Kernel.BasisGen` | elaboration only; compiled code cannot reach them |
| `partial` | `Ix.Kernel.Frontend.InModel*` | the in-process modeller, as upstream con-leche has it |
| `Address.admissionHash` `implemented_by` `Address.blake3`, with its three Rust externs | `Ix/Address/Admission.lean` (root library; `assumedSubstitutions`, for `Ixon.Authenticated` only) | an explicit, owner-approved assumption that the Rust BLAKE3 equals pure BLAKE3 |

Import allowlists (`IxC/Kernel/Audit/Roots.lean`):

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

The audits are Lean modules that fail elaboration on a violation. The core
kernel and codec audits are built by the strict standalone package `IxC/`
(`lake -d IxC build --wfail`, sources from the repository, no dependency
beyond the toolchain). The projection, block-order and authenticated-entry
audits build in the root package, and the model audit builds in
`Models/SetTheory`.

| Module | Checks |
| --- | --- |
| `IxC/Kernel/Audit/Roots.lean` | presence of every root (`publicRoots` 20, `fidelityRoots` 22, the operations); each at exactly the three standard axioms (`#guard_kernel_axioms`); the import closures against the allowlists; frozen runtime closures with their rulings; frozen `#check` statements and the definitions of `Authentic` and `Hashed`; a control showing the fold fails without the rulings |
| `IxC/Kernel/Admission/Audit.lean` | the byte stage's imports, closure and extern difference, its lemmas' axioms, and the public statements |
| `IxC/Kernel/Audit/Roles.lean` | the specification set's shape, frozen: every role's kind, levels or equation count, evidence kinds, block and dependencies, and `specVersion` |
| `Ix/SpecDigest.lean` | the specification digest (BLAKE3 of the set's canonical encoding), frozen |
| `Ix/Ixon/Projection/Audit.lean`, `Ix/Ixon/BlockOrder/Audit.lean` | the variants' imports (no hasher), closures, extern differences (none for reconstruction) and statements, and the projection writer's guards |
| `Ix/Ixon/Authenticated/Audit.lean` | the BLAKE3 entries' closure with exactly the assumed substitution (and its failure without it), the externs and `implemented_by` they add to the generic entries, their frozen definitions, their theorems' axioms and statements |
| `Ix/Cert/RuntimeAudit.lean` | the compiler's (`Ix.Cert.compile`) runtime closure: every foreign primitive, `unsafe` implementation and `partial` definition it reaches beyond `Init` and `Std`, frozen by name (its axioms are frozen in `Ix/Cert/Audit.lean`) |
| `IxC/Ixon/Audit.lean` | the codec's own import, runtime and axiom audit |
| `Models/SetTheory/IxSetTheoryModel/Audit.lean` | the model package's full dependency closure: standard axioms only |

Frozen runtime closures (compiled functions; inherited externs):

| Roots | Functions | Externs |
| --- | ---: | ---: |
| fold `Ix.Kernel.Cached.checkDecls` | 3352 | 67 |
| reader `readRecords`, `readStream` | 2134 | 89 |
| entry: `checkBytes{,With}`, `checkConstants{,With}` | 5788 | 113 |
| byte admission: `preflight`, `uniqueKeys`, `authenticate`, `decodeRecords`, `checkBytes` | 5785 | 113 |
| projection: `address`, `reconstruct`, `Projection.checkBytes` | 5810 | 113 |
| block order: `checkBytes`, `canonicalClasses`, `compareExpr` | 5944 | 114 |
| at BLAKE3: `Authenticated.checkBytes{,Projection,BlockOrder}`, `Address.admissionHash` | 5963 | 117 |

IxC step 6's structured errors (`CheckError md`: prose and keys, rendered
outside the checker) moved them from 3446, 5570, 5567, 5592, 5726 and 5745,
and the externs from 92, 115, 115, 115, 116 and 119; the reader's 2134 is
unchanged:
- the fold no longer spells keys or prints terms: `Key.toName`,
  `Derived.spell`, `Role.leanName`'s 121 closed terms, `Name`'s computed-field
  overrides, `Repr`/`Std.Format` and 25 string and printing externs left it
  (130 functions fewer), and every fixed message is a one-part list (two more
  closed objects per message site, 36 more closed terms);
- the entry and everything above it: the term printing and two string externs
  left, the fold's message sites add their closed objects (257 more closed
  terms), and the key rendering stays, reached from the reader's own
  `ReadError` messages.

The IxC performance series (PERF P16, P14, P3, P2) moved them from 3439, 2127,
5552, 5549, 5574, 5708 and 5727, and the externs of all but the reader by two:
- the memo state reset at every step of the fold (P16): 7 fewer in the fold
  and everything above it (the converted-constant cache `ienv` went);
- shared binder metadata (P14): 2 more in the fold, 3 in the reader, 5 in the
  entry (the shared objects and their closed terms);
- the codec's TagN twins (P3): 4 more in the reader, 8 in the entry
  (`getTagNFast`, `putTagNFast` and their copies at widths 0, 2 and 4), with
  their two `@[csimp]` theorems ruled (`IxC.Ixon.Codec`); the codec's own
  closure went from 351 to 359;
- phase B on tasks (P2): 12 more in the fold and above it, among them the
  `Init` externs `Task.spawn` and `Task.get` (see "Trust surface").

Step 5b's address keys (an `.anon` input key is the address its references
use) moved them from 3412, 2030, 5578, 5575, 5610, 5745 and 5764, and the
inherited externs from 82, 79, 111, 111, 111, 112 and 115, all `Init`'s: the
fold compares, hashes and prints addresses (`ByteArray.decEq`,
`ByteArray.get!`, the hexadecimal digits of a message); the reader serializes
the projection record of a member the input omits one of, to key it by that
record's address; the hexadecimal key spelling and the recursors' spelled
keys left.

Step 5b's mode index (the kernel's types take a `Mode`) moved them from 3364,
2066, 5566, 5563, 5598, 5733 and 5752, externs unchanged: the pinned names and
the basis declarations are generic in the mode, so their closed terms are
hoisted where they are used rather than where they are defined, and `Key.id`'s
override left the fold, which never builds an input key.

Step 5b's walk change moved them from 3303, 2025, 5474, 5471, 5505, 5638 and
5657, externs unchanged: the walk visits the source `f` of every
arity-reduced `f._redArg` it reaches (`Ix.Kernel.Audit.reducedAritySource?`).
The code generator calls `f._redArg` directly, and `f` is where an `unsafe`,
`implemented_by`, `csimp` or `partial` status is recorded; none came in with
these sources. The codec's closure (`IxC/Ixon/Audit.lean`) moved from 339 to
351 the same way.

Step 5b's `LetMeta` (a `letE` keeps its Ixon let contract) moved them from
3274, 2021, 5447, 5444, 5478, 5611 and 5630: the let contract's equality, hash
and `Repr`.

Step 5a (typed keys) moved them from 3350, 2018, 5656, 5653, 5687, 5820 and
5839, externs unchanged: `Key`'s three computed-field overrides came in,
ruled with `Key`; the closed name terms that spelled role and derived keys
left (a role key is a constructor now), and the rendering that prints keys
in messages came in (`Key.toName`, `Role.leanName`, `Derived.spell`).

Step 4 (primitives by specification) moved them from 3086, 1886, 5224 (120),
5222 (120), 5255 (120), 5389 (121) and 5407 (124): the fold gained the
specification set and the evidence checks, the reader the role bindings and
the evidence resolution, the entry the binding section's admission; nine
externs left with the retired Nat-operation pin decoder (eight string
scanners) and the pin table's derived-shape check (`memcmpStr`).

A frozen value or statement changes only deliberately: the change that
re-records it states why the closure or the statement moved.

`lake run check-kernel [--with-model]` is the gate. In order:

1. the strict `IxC` build with the core kernel and codec audits;
2. the host build of the root audits (`Ix/Ixon/{Projection,BlockOrder,
   Authenticated}/Audit.lean`, `Ix/Cert/RuntimeAudit.lean`) and the kernel tests
   (`Tests/Ix/Kernel/{Reader, CertifiedEntry, Authentication, Contracts,
   Projection, BlockOrder, AddressPure, ...}`), whose `#guard`s run at elaboration on
   fixtures re-keyed to their BLAKE3 addresses; the certified fixtures
   (`IxC/Fixtures/*`, authenticated under a hasher-free fixture hash) were
   already built in step 1;
3. `kernel-codec` (production codec against Rust) and `kernel-order`
   (canonical block order against Rust);
4. with `--with-model`, the `Models/SetTheory` build and its audit;
5. `kernel-layering` (`Tests/Ix/Kernel/Layering.lean`, derived from
   con-leche's `tests/layering.sh`): the kernel's import layering, each file
   of `IxC/Kernel/` classified by its path (`Tests/Ix/Kernel/KernelLayout.lean`;
   an unclassified file fails): the checker never imports the theory, the
   base never imports the model lane, the rules fence and its five recorded
   doors, and the boundary: the checker and the theory import only
   themselves, `Init`, `Std`, at elaboration time `Lean`, and of Ixon only
   the binder-contract data types `IxC.Ixon.Types.{Modes,Contract}` that
   `BinderMeta` carries (Ix's boundary modules `Admission`, `Ixon`, `Audit`,
   `Ingress`, `Egress`, `Ref` and `Search` import the kernel, not the
   reverse);
6. `kernel-trust-surface` (`Tests/Ix/Kernel/TrustSurface.lean`, derived from
   con-leche's `tests/trust-surface.sh`, with its lexer self-test on
   `Tests/Fixtures/trust-surface/lexer.lean`): a lexer-based scan of the
   checker, the theory and the admission hash (`Ix/Address/Admission.lean`)
   for compiler escapes (`unsafe`, `implemented_by`, `computed_field`,
   `native_decide`, `extern`, `sorry`, `axiom`, ...); the escapes in five
   allowlisted files (`IxC/Kernel/{Expr,Name,Exclusive,BasisGen}.lean`,
   `Ix/Address/Admission.lean`) are permitted, each with its justification
   in the tool's header;
7. `kernel-level-comparison`: the level comparison (`Level.leq`,
   `Level.isEquiv` and its Géran fallback) against brute-force evaluation,
   on random levels and on Ixon's canonical forms;
8. `kernel-entry-cases`: Lean declarations of
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
   `IxC/lean-toolchain` and `Models/SetTheory/lean-toolchain` name the
   same release (CI's `lean-test` job compares them). The model's `mathlib`
   `rev` in `Models/SetTheory/lakefile.toml` is Mathlib's tag for that
   release; after changing it, `lake -d Models/SetTheory update mathlib`
   refreshes `Models/SetTheory/lake-manifest.json`.
2. **The default role table.** A new toolchain moves Init's addresses:
   regenerate `RoleData.lean` with the three commands under "Regeneration"
   above (the full `--consts` list is in the generated header). The
   specifications, `specVersion` and the digest do not change. Until then
   the moved constants are not bound, and the inputs and entry cases that
   need them decline.
3. **Frozen audit records.** The runtime closures (`N compiled functions;
   inherited externs M, ...`), the extern differences and the frozen
   `#check` statements are `#guard_msgs` records in
   `IxC/Kernel/Audit/Roots.lean`, `IxC/Ixon/Audit.lean` and
   `IxC/Kernel/Admission/Audit.lean` (built by `lake -d IxC build
   --wfail`), and in `Ix/Ixon/Projection/Audit.lean` and
   `Ix/Ixon/BlockOrder/Audit.lean` (built by `lake build --wfail
   Ix.Ixon.Projection.Audit Ix.Ixon.BlockOrder.Audit`). A record that no
   longer matches fails the build and prints the message its command now
   produces; re-record it by replacing the record's docstring with that
   message, and update the closure table above and the counts in
   `Roots.lean`'s module docstring. Any other `#guard_msgs` that fails (the
   controls in `IxC/Kernel/Audit/Runtime.lean`, the axiom records in
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

1. **Codec proofs.** `IxC/Ixon/Verify` proves the codec the byte stage runs.
   Re-prove it for the new grammar keeping the name and statement of every
   lemma used outside `IxC/Ixon/Verify` (the `#check` records in
   `IxC/Ixon/Audit.lean` list them; the byte stage's theorems in
   `IxC/Kernel/Admission/Bytes/Theorems.lean` must then build unchanged).
   `lake -d IxC build --wfail IxC` is the acceptance.
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
5. **The default role table**, as step 2 of a toolchain bump: the three commands under
   "Regeneration" above. Write the two environments to fresh files, never
   to paths that are symbolic links to another format's stored environments:
   the commands write through a link.
6. **The reader test's frozen records.** `Tests/Ix/Kernel/Reader.lean`
   holds compiled records as bytes. `lake exe kernel-entry-cases --records
   nested-through-nested` and `--records level-comparison` print them
   (`lTreeRecords`, `levelRecords`) with the names of the blocks they
   belong to; replace the lists and the owner addresses with the output. The
   byte vectors of `IxC/Fixtures/{Codec,ParserWork,ByteAdmission}.lean`
   are the codec's: rewrite them for the new grammar (`kernel-codec`
   compares the Lean codec with Rust's on them).
7. **IxVM costs.** `lake test --wfail -- --ignored ixvm` reports every
   kernel-check FFT-cost pin of `Tests/Ix/IxVM.lean` and the shard pin in
   `Tests/Main.lean` that moved; set each to the measured value.
8. **Frozen audit records**, as step 3 of a toolchain bump, including the
   codec's own closure in `IxC/Ixon/Audit.lean`.
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
constants against fixed specifications (`IxC/Kernel/Roles.lean`) with the
role table's evidence (the default table: `IxC/Kernel/Ixon/RoleData.lean`).

**What was changed.** Every file was moved (`ConLeche/Kernel/X` and
`ConLeche/X` to `IxC/Kernel/X`) and its namespace and module prefix renamed
(`ConLeche.Kernel` and `ConLeche` to `Ix.Kernel`, as whole names). These
files carry further changes:

| File | Change | Why |
| --- | --- | --- |
| `IxC/Kernel/{CheckerBase,Checker,TrustAxioms,DeclCheck}.lean`, `IxC/Kernel/Cached/ParsedC.lean` and the proofs that consume them | imports `Roles` instead of `NatOpPins`; the operations' install gate checks the role table's evidence (`checkDivModEvidence`, `evidenceLocal`), the reduce opaques keep their identity certificate, the pin variants and pin comparisons are gone; the proofs take `Evidences` where they took pin lists | upstream's `NatOpPins` splices JSON pin dumps; Ix binds primitives by a role table and validates them against fixed specifications (IXC-PLAN step 4) |
| `IxC/Kernel/Verify/Cached/{AgreeFloor,PushChain}.lean` | `import all Init.LetFun` | Lean 4.34.0 no longer exposes `letFun`'s body, which these proofs unfold |
| `IxC/Kernel/Frontend/InModel/Nested.lean` | container groups formed largest family first | Ix's compiler orders a nested block's auxiliary motives canonically |
| `IxC/Kernel/Level.lean`, `IxC/Kernel/Verify/Level.lean` | the `(param, max)` case falls back on Géran's sublevels, with its soundness case | nanoda's comparison is incomplete there, and Ixon's canonical levels reach the gap (Mathlib's `RatFunc.liftOn_def`) |
| `IxC/Kernel/MainTheorem.lean` | only `model_exists` kept | the NDJSON corollary needs a frontend Ix does not use |

Ix's own files under `IxC/Kernel/` are `Admission.lean` and the `Admission`
directory (the certified entry, its byte stage, theorems and audit),
`Roles.lean` (the role specifications), `Ref.lean`, `Search.lean`, the `Audit`, `Ingress`, `Egress` and `Ixon`
directories (the Ixon reader and its specification, the role table, the
default table and prelude, the record store, the projection writer and the audits), and
`LevelGeran.lean` and
`Verify/LevelGeran.lean` (Géran's sublevels and their soundness and
completeness), which the changed `Level` files import.

**Notices.** `IxC/Kernel/LICENSE-CON-LECHE` is con-leche's Apache-2.0 licence
and `IxC/Kernel/NOTICE` states the origin, the revisions and the changes;
`Models/SetTheory` carries its own copy for the file it takes from con-leche.

**Builds.** `IxC/lakefile.lean` owns the certified modules, whose module
names live under the `IxC` root inside the package directory:
`IxC.Kernel` is `IxC.Kernel` and everything under
`IxC/Kernel/`, `IxC.Ixon` is the pure address and codec modules
(`IxC.Address.Core`, `IxC.Ixon.*`), and `IxC.Fixtures` is the
four certified fixtures. Declaration namespaces are unchanged: the kernel
still declares `Ix.Kernel.*` and the codec `Ixon.*`; only `import` lines name
the `IxC.` modules. The root package depends on `ix-kernel`, every
workspace that requires it reuses its artifacts in the repository's
`.lake/kernel` directory, and the standalone build checks that these sources,
fixtures included, need only the Lean toolchain.

In the root package, `Ix` is the main library, with Lake's default roots and
globs, and carries the Rust linkage; a default build follows `Ix.lean`'s
imports. Nothing the dependency owns is under the `Ix.` module root, so `Ix`
never shadows it. `IxSharingVerify` owns the sharing proofs under the
`IxSharingVerify` module root (namespace `Ix.Sharing.Verify`), and
`KernelEntry` owns the benchmark helpers. The root test library imports the
certified fixtures from `IxC.Fixtures`.

`IxC.Kernel` has one special option:
`linter.deprecated` is off, so the con-leche-derived sources, written for
Lean 4.33.0, build under `--wfail` on 4.34.1 without renaming the deprecated
`if_pos`/`if_neg`/`dif_pos`/`dif_neg` lemmas they use (2,885 uses in 209
files). Ix's own files there do not rely on it: they build without warnings
with the linter on.

**Bringing over an upstream change.** By hand: take upstream's diff between
the recorded revision and the new one for the files concerned, map its
paths (`ConLeche/Kernel/X` and `ConLeche/X` to `IxC/Kernel/X`) and names
(`ConLeche` to `Ix.Kernel`), apply it, update the revisions in
`IxC/Kernel/NOTICE`, and run the full gate. A module the closure newly
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
its install plus its checks. A checker failure's reason is rendered by
`.meta`: its keys spelled with the names the `.ixe`'s metadata gives them and
the first eight hexadecimal digits of their addresses, `Nat.add@a1b2c3d4`
(`Reader.spellWith`); the verdict is the `.anon` run's.
`kernel-check-ixe --meta <input.ixe> <output.jsonl> [limit]` is the erasure
test: every record read and checked at `.anon` and at `.meta` and the runs
compared record by record (readings, outcome, fold position, failure with
its keys mapped), failing on any difference (Init+Std: 97,906 records, no
difference, about 220 s and 4 GB). Environment:

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
intrinsic, proof-carrying kernel in `IxC/Kernel/**` (`Ix.Kernel.check`,
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
`IxC/Kernel/LevelGeran.lean`'s algorithm.

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
| `Ix/Compile/Verify/{Codec,ExprCodec,ExprSpineCodec,ConstantCodec,ConstantTablesCodec,NonrecursiveConstantCodec,RecursorConstantCodec,MutualConstantCodec}.lean` | Preserved under `IxC/Ixon/Verify` (`Basic`, `Expr`, `ExprSpine`, `Constant`, `ConstantTables`, `NonrecursiveConstant`, `RecursorConstant`, `MutualConstant`), for the Ixon v4 codec, with complete wire domains, frozen contracts, and independent audits | Done; old copies deleted |
| `Ix/Compile/Verify/TagN.lean` (the TagN bijection and rejection laws) | `IxC/Ixon/Verify/TagN.lean` (namespace `Ixon.Verify.TagN`), built with the codec proofs by `lake -d IxC build --wfail` | Done |
| `Ix/Compile/Verify/{SharingExact,SharingExactCanon,SharingExactPasses}.lean`, `Tiered*`, `Uniform*` and `Audit/CompiledCode.lean` (the canonical sharing construction) | Moved to `IxSharingVerify` (namespace `Ix.Sharing.Verify`; deprecated lemma names replaced for Lean 4.34.0; no statement changed), library `IxSharingVerify` (`lake build --wfail IxSharingVerify`, also built by `lake lint`); audits `IxSharingVerify/Audit/{Statements,SorryFrontier,CompiledCode}.lean` | Done; no theorem of these files dropped |
| `Ix/Compile/Verify/CompileSharingCodec.lean` | Its builder part (`buildConstantWithSharing_wireWF`, `SharingRunOK`, the singleton-driver tail) is `IxSharingVerify/Builder.lean`; its expression-compilation roundtrips are retired with the compiler chain they rest on | Done |
| `Ix/Compile/Verify/{Catalog,IxonValue,SourceValue,Reference}.lean` | Structural predicates live in `IxC/Ixon/Wire`; the intrinsic kernel's exact readings covered resolved values; the old semantic square is retired | Done |
| Remaining `Ix/Compile/Verify/**`, including `Compile*` (the per-declaration compiler endpoint theorems among them), `Arena`, the former heuristic `Sharing`, `Statements`, and its audits | Retired compiler/specification machinery; no Ix.Kernel compiler-correctness theorem is claimed | Done |
| Root `lakefile.lean` / `lake-manifest.json` | Removed dependency, proof libraries, replay benchmark, proof loader, and `build-all` exception; Lake regenerated the manifest | Done; the remaining targets build strictly |
| `ix_ffi_dyn`, `crates/ffi-dyn`, workspace `Cargo.toml` / `Cargo.lock` | Removed the proof-only crate and loader; ordinary runtime FFI remains | Done; Cargo regenerated the lockfile |
| `Benchmarks/Lean4Lean.lean`, `Benchmarks/Lean4LeanMain.lean`, `Tests/Ix/Lean4Lean.lean`, `Tests/Main.lean` | Removed replay library, executable, smoke runner and registration; fixture dispositions below | Done |
| `Ix/Cli/BenchCmd.lean`, `Ix/BenchConstants.lean`, `docs/benchmarking.md` | Removed backend registry, dispatch, help, and active commands; measurements use the existing certified harness and Rust driver | Done; removed backend exits 2 as unknown |
| `Benchmarks/TruthMinesSpec/{Catalog,Spec}.lean` | Removed package/member at the generator source | Done; generator checks pass |
| `Benchmarks/TruthMines/{lakefile.lean,lake-manifest.json,Drivers/Lean4Lean.lean}` | Regenerated configuration without the independent upstream dependency; deleted the generated driver | Done; 78 retained package entries |
| `Benchmarks/Compile/{lake-manifest.json,TruthMines/lake-manifest.json,TruthMines/Members/Lean4Lean.lean}` | Removed inherited package entries and generated member; retained unrelated pins | Done; 24 and 80 retained package entries |
| `.github/workflows/merge-tests.yml`, `.github/workflows/ci.yml` | Removed old proof jobs and runner; the `Certified kernel` partition of merge-tests runs `check-kernel --with-model` on the lean-test sticky-disk lineage in the merge queue; runtime parity jobs remain | Done |
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
| Tag0/Tag2/Tag4 integer laws and their minimal-width checks | the TagN writer and reader laws `Ixon.Verify.Codec.{putTagN_writes, getTagN_reads}` over the byte specification `tagNBytes` (`IxC/Ixon/Verify/Basic.lean`), and `Ixon.Verify.TagN`: `runGetExact_getTagN_iff` (a read succeeds exactly on the written bytes), `putTagN_inj`, `getTagN_rejects_code`, `getTagN_rejects_overflow` (implemented) | Ixon v4 has one integer code, and it is bijective, so no minimal-width check remains |
| `ExprTableWF`, decreasing sharing bounds, reference/universe table resolution | Checked resolution in the canonical decoder and the Ixon reader (a bad index or a missing payload is a malformed record) | Detect bad indexes, missing payloads, sharing cycles/forward entries, and unsupported modes before certification |
| Binder-mode erasure relation | An explicit accepted mode policy: the Ixon reader keeps `lam` and `all` contracts as identity data, conversion compares input contracts and not result contracts, and `let` contracts are erased ("Binder contracts" above) | No Lean4Lean interpretation is retained as a hidden premise; an accept checks no use of a variable against its contract |
| Production compiler refinement/value-preservation and end-to-end semantic square | Retired; a separate compiler-correctness project would need new source semantics and proofs | Ix.Kernel acceptance does not prove that the compiler preserved the original Lean declaration |

These contracts are stated about the Ixon v4 codec (TagN integers), with the
same names and statements as for v3, as is every codec lemma the byte stage
uses. The byte stage's resource proofs (`IxC/Ixon/Verify/Work*`,
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
`IxC/Kernel/Admission/Bytes/Theorems.lean`).
