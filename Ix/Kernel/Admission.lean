import Ix.Kernel.Admission.Bytes
import Ix.Kernel.Ixon.Prelude
import Ix.Kernel.Cached.Installed

/-! # Admission from ordered Ixon record bytes

The certified Ixon entry (`docs/kernel.md`): `checkBytes` checks exactly the
declarations described by the supplied canonical record bytes with the
verified checker `Ix.Kernel` (derived from con-leche, `Ix/Kernel/NOTICE`):

    preflight → uniqueKeys → decodeRecords → Ixon reader → preparePrelude
              → Ix.Kernel.Cached.checkDecls .verified natPins

* `preflight`, `uniqueKeys` and `decodeRecords` are the byte stage
  (`Ix.Ixon.Admission.Bytes`): the batch limits, key uniqueness (no two
  records and no two blobs under one address) and canonical per-record
  decoding, with their error positions.
* The reader is `Ix.Kernel.IxonReader` (address keys as reserved names, regrouping of
  `muts` blocks and projection records, the in-process modeller and the
  projection rewrite), against the supplied records with the Ixon prelude's
  records as a fallback store.
* `preparePrelude` is `Ix.Kernel.Frontend.preparePrelude`
  (`Ix/Kernel/Frontend/Prepare.lean`), with the Ixon prelude (`Ix.Kernel.IxonReader.builtinPrelude`).
* The fold is `Ix.Kernel.Cached.checkDecls` at `.verified`, at the committed
  Nat-operation pin variant generated from Ixon records
  (`Ix.Kernel.IxonReader.builtinNatOpPins`, decoded from
  `Ix/Kernel/Ixon/NatOpPinData.lean`; the theorem holds at every pin
  list, so the pins are untrusted).

This module holds definitions only, so that running the entry does not
build the proof tree; its theorems are in `Ix.Ixon.Admission.Theorems`.
There `checkBytes_has_model` is `Ix.Kernel.model_exists` at the prepared
declarations: the reader owes nothing, because the main theorem holds for
every declaration array. The host supplies record order, address keys
and literal blobs; addresses are keys, not authenticated content hashes, and
blobs retain their exact supplied bytes. No host decoder or verdict
participates in this path. The
entry does not reorder beyond `preparePrelude`: a host order is a dependency
order in which each record follows its references, a pinned `Nat` operation's
certificate ground, and the constants its literals reference
(`IxonReader.literalEdges`; the checker declines a string literal before the
string-support declarations), as the environment-check driver's order is.
-/

namespace Ix.Ixon.Admission

open Ix.Kernel (ConstRef)
open Ix.Kernel.IxonReader

/-- Byte, reader and checker failures, kept apart. Positions are the
supplied records' (decoding, reading) or the fold's (checking). -/
inductive Error where
  | limit (resource : Resource)
  | duplicate (table : Table) (position : Nat) (address : Address)
  | decode (position : Nat) (address : Address) (reason : String)
  /-- the committed prelude or pin table does not load (a corrupted file) -/
  | prelude (reason : String)
  | read (position : Nat) (error : ReadError)
  | kernel (error : Ix.Kernel.CheckError) (position : Nat)

instance : ToString Error where
  toString
    | .limit r => s!"limit: {repr r}"
    | .duplicate t p a => s!"duplicate {repr t} address at {p} ({a})"
    | .decode p a r => s!"decode at {p} ({a}): {r}"
    | .prelude r => s!"prelude: {r}"
    | .read p e => s!"read at {p}: {e}"
    | .kernel e p => s!"kernel at {p}: {e}"

/-- The byte stage's failures, unchanged. -/
def Error.ofBytes : ByteError → Error
  | .limit r => .limit r
  | .duplicate t p a => .duplicate t p a
  | .decode p a r => .decode p a r

/-- The reading of decoded records: the prelude's state continues into the
stream, and the prelude's records back the store. -/
def readStream (pins : Pins) (pre : Prelude)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Array Ix.Kernel.Declaration) := do
  let records := constants.toArray
  let cx := contextOf pins records blobs pre.records hint
  match readRecords cx pre.state records with
  | .ok (_, decls) => pure decls
  | .error (e, i) => throw (.read i e)

/-- The declarations the fold runs over, from the bytes. -/
def prepareWith (pins : Pins) (pre : Prelude)
    (limits : Limits) (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Array Ix.Kernel.Declaration) := do
  (preflight limits records blobs).mapError Error.ofBytes
  (uniqueKeys records blobs).mapError Error.ofBytes
  let constants ← (decodeRecords limits records).mapError Error.ofBytes
  let decls ← readStream pins pre constants blobs hint
  pure (Ix.Kernel.Frontend.preparePrelude pre.ix decls)

/-- The entry over an explicit pin table, prelude and Nat-operation pin list
(tests inject them). -/
def checkBytesWith (pins : Pins) (pre : Prelude) (natPins : List Ix.Kernel.NatOpPinSet)
    (limits : Limits) (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error Ix.Kernel.Env := do
  let decls ← prepareWith pins pre limits records blobs hint
  (Ix.Kernel.Cached.checkDecls .verified natPins decls).mapError
    fun (e, i) => .kernel e i

/-- **The certified Ixon entry**: check exactly the declarations described by
the supplied canonical record bytes with the verified checker, after the
batch limits, key uniqueness and canonical per-record decoding, under the
committed pin table, Ixon prelude and Nat-operation pin variant. `hint` is
the host's optional (untrusted) reducibility hint per constant. -/
def checkBytes (limits : Limits) (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error Ix.Kernel.Env := do
  let pins ← defaultPins.mapError Error.prelude
  let pre ← builtinPrelude.mapError Error.prelude
  let natPins ← builtinNatOpPins.mapError Error.prelude
  checkBytesWith pins pre natPins limits records blobs hint

/-- The reader's context for decoded records under a pin table and a
prelude, as `readStream` builds it: the records' store backed by the
prelude's records, and the recursor index of both. -/
def streamContext (pins : Pins) (pre : Prelude) (constants : List (Address × Ixon.Constant))
    (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) : Ctx :=
  contextOf pins constants.toArray blobs pre.records hint

/-- The verified fold over decoded records: the reader, the prelude,
the fold. `checkBytesWith` is byte admission followed by this
(`checkBytesWith_eq`). -/
def checkConstantsWith (pins : Pins) (pre : Prelude) (natPins : List Ix.Kernel.NatOpPinSet)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error Ix.Kernel.Env := do
  let decls ← readStream pins pre constants blobs hint
  (Ix.Kernel.Cached.checkDecls .verified natPins (Ix.Kernel.Frontend.preparePrelude pre.ix decls)).mapError
    fun (e, i) => .kernel e i

/-- `checkConstantsWith` under the committed pin table, Ixon prelude and
Nat-operation pin variant (as `checkBytes`). -/
def checkConstants (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error Ix.Kernel.Env := do
  let pins ← defaultPins.mapError Error.prelude
  let pre ← builtinPrelude.mapError Error.prelude
  let natPins ← builtinNatOpPins.mapError Error.prelude
  checkConstantsWith pins pre natPins constants blobs hint

/-- How an Ix caller classifies a failure of the certified entry
(`docs/kernel.md`, "Outcomes"):
`reject` only where an independent check establishes that the
input is wrong (the batch limits are a coverage bound and decline; a key
used twice in one table, a non-canonical record and a record the reader
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
  | .decode .. => .rejected
  | .prelude _ => .declined
  | .read _ (.malformed _) => .rejected
  | .read _ (.declined _) => .declined
  | .kernel _ _ => .declined

end Ix.Ixon.Admission
