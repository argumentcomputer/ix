import IxC.Kernel.Admission.Bytes
import IxC.Kernel.Ixon.Prelude
import IxC.Kernel.Cached.Installed

/-! # Admission from ordered Ixon record bytes

The certified Ixon entry (`docs/kernel.md`): `checkBytes hash binding` checks
exactly the declarations described by the supplied canonical record bytes
with the verified checker `Ix.Kernel` (derived from con-leche,
`IxC/Kernel/NOTICE`), under the supplied role table:

    preflight → uniqueKeys → authenticate hash → admitBinding hash
              → decodeRecords → Ixon reader → evidenceOf
              → preparePrelude → Ix.Kernel.Cached.checkDecls .verified ev

* `preflight`, `uniqueKeys`, `authenticate` and `decodeRecords` are the byte
  stage (`Ix.Kernel.Admission.Bytes`): the batch limits, key uniqueness (no
  two records and no two blobs under one address), authentication (every
  record and blob under `hash` of its supplied bytes) and canonical
  per-record decoding, with their error positions.
* `admitBinding` admits the role table (`Ix.Kernel.RoleTable`): its binding
  section is authenticated (the section's address is `hash` of its bytes, the
  binding hash a claim commits to), decoded canonically
  (`RoleTable.ofBytes`) and checked for well-formedness
  (`RoleTable.check`). Each failure is a reject.
* The reader is `Ix.Kernel.Reader` (address keys as reserved names, the
  table's bound addresses renamed to their role keys, regrouping of `muts`
  blocks and projection records, the in-process modeller and the projection
  rewrite), against the supplied records with the prelude's and the default
  evidence's records as a fallback store. `evidenceOf` resolves the table's
  evidence to the theorems' values.
* `preparePrelude` is `Ix.Kernel.Frontend.preparePrelude`
  (`IxC/Kernel/Frontend/Prepare.lean`), with the Ixon prelude read under the
  same table (`Ix.Kernel.Reader.preludeFor`).
* The fold is `Ix.Kernel.Cached.checkDecls` at `.verified`, at the table's
  evidence: the theorem holds at every evidence, so the table is untrusted.

The content hash is the parameter `hash : ByteArray → Address`: the kernel
admits no hasher, and every theorem holds at every `hash`. The root library
instantiates the entry at BLAKE3 (`Ixon.Authenticated`).

This module holds definitions only, so that running the entry does not
build the proof tree; its theorems are in `Ix.Kernel.Admission.Theorems`.
There `checkBytes_has_model` is `Ix.Kernel.model_exists` at the prepared
declarations: the reader owes nothing, because the main theorem holds for
every declaration array and every evidence. The host supplies record order,
address keys, literal blobs and the role table; each key is authenticated as
`hash` of its supplied bytes, and blobs retain those exact bytes. No host
decoder or verdict participates in this path. The entry does not reorder
beyond `preparePrelude`: a host order is a dependency order in which each
record follows its references, a certified `Nat` operation's certificate
ground, and the constants its literals reference (`Reader.literalEdges`; the
checker declines a string literal before the string-support declarations), as
the environment-check driver's order is.
-/

namespace Ix.Kernel.Admission

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader

/-- **The role table as the entry receives it**: the binding section's
bytes, under the address a claim commits to. -/
structure Binding where
  address : Address
  bytes : ByteArray

/-- Failures of the role table's admission; each is a reject. -/
inductive BindingError where
  /-- the section's address is not `hash` of its bytes -/
  | mismatch (address : Address)
  /-- the bytes are not a canonical binding section (`RoleTable.ofBytes`) -/
  | decode
  /-- the table is not well formed (`RoleTable.check`) -/
  | malformed (reason : String)

/-- **The role table's admission**: authentication of its section under
`hash`, canonical decoding, and well-formedness. -/
def admitBinding (hash : ByteArray → Address) (b : Binding) :
    Except BindingError Ix.Kernel.RoleTable := do
  unless decide (hash b.bytes = b.address) do throw (.mismatch b.address)
  let some t := Ix.Kernel.RoleTable.ofBytes b.bytes | throw .decode
  t.check.mapError .malformed
  pure t

/-- Byte, binding, reader and checker failures, kept apart. Positions are the
supplied records' (authentication, decoding, reading) or the fold's
(checking). -/
inductive Error where
  | limit (resource : Resource)
  | duplicate (table : Table) (position : Nat) (address : Address)
  | mismatch (table : Table) (position : Nat) (address : Address)
  | decode (position : Nat) (address : Address) (reason : String)
  /-- the role table's section does not admit -/
  | binding (error : BindingError)
  /-- the committed prelude does not load (a corrupted file) -/
  | prelude (reason : String)
  | read (position : Nat) (error : ReadError)
  | kernel (error : Ix.Kernel.CheckError) (position : Nat)

instance : ToString Error where
  toString
    | .limit r => s!"limit: {repr r}"
    | .duplicate t p a => s!"duplicate {repr t} address at {p} ({a})"
    | .mismatch t p a => s!"{repr t} address at {p} is not the hash of its bytes ({a})"
    | .decode p a r => s!"decode at {p} ({a}): {r}"
    | .binding (.mismatch a) => s!"binding: the role table's address is not the hash of its bytes ({a})"
    | .binding .decode => "binding: the role table is not a canonical binding section"
    | .binding (.malformed r) => s!"binding: {r}"
    | .prelude r => s!"prelude: {r}"
    | .read p e => s!"read at {p}: {e}"
    | .kernel e p => s!"kernel at {p}: {e}"

/-- The byte stage's failures, unchanged. -/
def Error.ofBytes : ByteError → Error
  | .limit r => .limit r
  | .duplicate t p a => .duplicate t p a
  | .mismatch t p a => .mismatch t p a
  | .decode p a r => .decode p a r

/-- The reader's context for decoded records under a role table and a
prelude, as `readStream` builds it: the records' store backed by the
prelude's records and its evidence records, and the recursor index of all. -/
def streamContext (t : Ix.Kernel.RoleTable) (pre : Prelude md)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) : Ctx md :=
  contextOf t constants.toArray blobs (pre.records ++ pre.evidence) pre.blobs hint

/-- The reading of decoded records under a role table: the prelude's state
continues into the stream, and the prelude's records back the store. The
result is the table's evidence resolved against the reading
(`evidenceOf`), and the declarations. -/
def readStream (t : Ix.Kernel.RoleTable) (pre : Prelude md)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Evidences md × Array (Ix.Kernel.Declaration md)) := do
  let cx := streamContext t pre constants blobs hint
  match readRecords cx pre.state constants.toArray with
  | .ok (st, decls) => pure (evidenceOf cx st t, decls)
  | .error (e, i) => throw (.read i e)

/-- The evidence and the declarations the fold runs over, from the bytes. -/
def prepareWith (hash : ByteArray → Address) (binding : Binding) (pre : Prelude md)
    (limits : Limits) (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Evidences md × Array (Ix.Kernel.Declaration md)) := do
  (preflight limits records blobs).mapError Error.ofBytes
  (uniqueKeys records blobs).mapError Error.ofBytes
  (authenticate hash records blobs).mapError Error.ofBytes
  let t ← (admitBinding hash binding).mapError .binding
  let constants ← (decodeRecords limits records).mapError Error.ofBytes
  let (ev, decls) ← readStream t pre constants blobs hint
  pure (ev, Ix.Kernel.Frontend.preparePrelude pre.ix decls)

/-- The entry over an explicit prelude (tests inject one). -/
def checkBytesWith (hash : ByteArray → Address) (binding : Binding) (pre : Prelude md)
    (limits : Limits) (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Env md) := do
  let (ev, decls) ← prepareWith hash binding pre limits records blobs hint
  (Ix.Kernel.Cached.checkDecls .verified ev decls).mapError
    fun (e, i) => .kernel e i

/-- `checkBytes` over a source of preludes: the prelude for the admitted
table is `prelude t` (`preludeFor`, the committed prelude, in `checkBytes`).
The theorems are stated over it, so that no proof unfolds the committed
prelude's data. -/
def checkBytesUsing (prelude : Ix.Kernel.RoleTable → Except String (Prelude md))
    (hash : ByteArray → Address) (binding : Binding) (limits : Limits)
    (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Env md) := do
  let t ← (admitBinding hash binding).mapError .binding
  let pre ← (prelude t).mapError Error.prelude
  checkBytesWith hash binding pre limits records blobs hint

/-- **The certified Ixon entry**: check exactly the declarations described by
the supplied canonical record bytes with the verified checker, after the
batch limits, key uniqueness, authentication of every record and blob
address as `hash` of its bytes, the role table's admission (its section
authenticated under `hash`, decoded canonically, well formed) and canonical
per-record decoding, behind the committed Ixon prelude read under that table.
`hint` is the host's optional (untrusted) reducibility hint per constant. -/
def checkBytes (hash : ByteArray → Address) (binding : Binding) (limits : Limits)
    (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Env md) :=
  checkBytesUsing preludeFor hash binding limits records blobs hint

/-- The verified fold over decoded records under an admitted role table: the
reader, the prelude, the fold. `checkBytesWith` is byte admission followed by
this (`checkBytesWith_eq`). Decoded records carry no bytes to authenticate: a
caller that starts here vouches for its keys and its table. -/
def checkConstantsWith (t : Ix.Kernel.RoleTable) (pre : Prelude md)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Env md) := do
  let (ev, decls) ← readStream t pre constants blobs hint
  (Ix.Kernel.Cached.checkDecls .verified ev (Ix.Kernel.Frontend.preparePrelude pre.ix decls)).mapError
    fun (e, i) => .kernel e i

/-- `checkConstantsWith` under a role table, behind the prelude `prelude t`. -/
def checkConstantsUsing (prelude : Ix.Kernel.RoleTable → Except String (Prelude md))
    (t : Ix.Kernel.RoleTable) (constants : List (Address × Ixon.Constant))
    (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Env md) := do
  let pre ← (prelude t).mapError Error.prelude
  checkConstantsWith t pre constants blobs hint

/-- `checkConstantsWith` under a role table, behind the committed prelude read
under it. -/
def checkConstants (t : Ix.Kernel.RoleTable) (constants : List (Address × Ixon.Constant))
    (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Env md) :=
  checkConstantsUsing preludeFor t constants blobs hint

/-- `checkConstants` under a role table's section: the table admitted
(`admitBinding`: authentic under `hash`, canonical, well formed), then
`checkConstants`. The root library's variants (`Ixon.Projection`,
`Ixon.BlockOrder`) end in it. -/
def checkConstantsAt (hash : ByteArray → Address) (binding : Binding)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Ix.Kernel.Env md) := do
  let t ← (admitBinding hash binding).mapError .binding
  checkConstants t constants blobs hint

/-- The default role table's section, under the address the generator
committed it at (`RoleData.tableAddress`, BLAKE3 of its bytes). For tests and
the command line: the entry's theorems hold for every table. -/
def defaultBinding : Except String Binding := do
  pure ⟨← defaultTableAddress, ← defaultTableBytes⟩

/-- How an Ix caller classifies a failure of the certified entry
(`docs/kernel.md`, "Outcomes"):
`reject` only where an independent check establishes that the
input is wrong (the batch limits are a coverage bound and decline; a key
used twice in one table, a key that is not the hash of its bytes, a role
table that does not admit, a non-canonical record and a record the reader
finds malformed reject); every checker verdict declines, because the checker
reports fuel exhaustion as `internal` and a failed conversion search as
`invalid`, and neither is evidence that the input is wrong. -/
inductive Outcome where
  | rejected
  | declined
  deriving Repr, DecidableEq

/-- The classification of a failure of `checkBytes` (call it as
`e.outcome`). -/
def Error.outcome : Error → Outcome
  | .limit _ => .declined
  | .duplicate .. => .rejected
  | .mismatch .. => .rejected
  | .decode .. => .rejected
  | .binding _ => .rejected
  | .prelude _ => .declined
  | .read _ (.malformed _) => .rejected
  | .read _ (.declined _) => .declined
  | .kernel _ _ => .declined

/-- The classification of a byte-stage failure, as `Error.outcome` makes it:
a batch limit declines; a key used twice in one table, a key that is not the
hash of its bytes and a record that does not decode canonically reject. The
variants (`Ixon.Projection`, `Ixon.BlockOrder`) classify their byte stage
with it. -/
def ByteError.outcome : ByteError → Outcome
  | .limit _ => .declined
  | .duplicate .. => .rejected
  | .mismatch .. => .rejected
  | .decode .. => .rejected

end Ix.Kernel.Admission
