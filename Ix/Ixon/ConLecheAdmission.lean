/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Admission.Bytes
import Ix.Kernel.ConLeche.Prelude
import ConLeche.MainTheorem

/-! # Admission from ordered Ixon record bytes through con-leche (plan v4, L4)

The `checkBytes`-shaped entry of con-leche's verified checker, which the
certified API's `Ix.Ixon.Admission.checkBytes` runs from L5 (the intrinsic
kernel's entry is `Ix.Ixon.Admission.checkBytesIntrinsic` until L6):

    preflight → decodeRecords → Ixon reader → preparePrelude
              → ConLeche.Cached.checkDecls .verified natPins

* `preflight` and `decodeRecords` are `Ix.Ixon.Admission`'s: the same batch
  limits, the same canonical per-record decoding, the same error positions.
* The reader is `Ix.Kernel.ConLecheReader` (keys per D1 (b), regrouping of
  `muts` blocks and projection records, the in-process modeller and the
  projection rewrite), against the supplied records with the Ixon prelude's
  records as a fallback store.
* `preparePrelude` is con-leche's (`ConLeche/Frontend/Prepare.lean`,
  verbatim), with the Ixon prelude (`Ix.Kernel.ConLecheReader.builtinPrelude`).
* The fold is con-leche's `checkDecls` at `.verified`, at the committed
  Nat-operation pin variant generated from Ixon records
  (`Ix.Kernel.ConLecheReader.builtinNatOpPins`, decoded from
  `Ix/Kernel/ConLeche/NatOpPinData.lean`; the theorem holds at every pin
  list, so the pins are untrusted).

`checkBytes_has_model` is `ConLeche.model_exists` at the prepared
declarations: the reader owes nothing, because the main theorem holds for
every declaration array. The host still supplies record order, address keys
and literal blobs; addresses are keys, not authenticated content hashes. The
entry does not reorder beyond `preparePrelude`: a host order is a dependency
order in which each record follows its references, a pinned `Nat` operation's
certificate ground, and the constants its literals reference
(`ConLecheReader.literalEdges`; con-leche declines a string literal before the
string-support declarations), as the census driver's order is.
-/

namespace Ix.Ixon.ConLecheAdmission

open Ix.Kernel (ConstRef)
open Ix.Kernel.ConLecheReader
open Ix.Ixon.Admission (Limits Records Resource preflight decodeRecords)

/-- Byte, reader and checker failures, kept apart. Positions are the
supplied records' (decoding, reading) or the fold's (checking). -/
inductive Error where
  | limit (resource : Resource)
  | decode (position : Nat) (address : Address) (reason : String)
  /-- the committed prelude or pin table does not load (a corrupted file) -/
  | prelude (reason : String)
  | read (position : Nat) (error : ReadError)
  | kernel (error : ConLeche.CheckError) (position : Nat)

instance : ToString Error where
  toString
    | .limit r => s!"limit: {repr r}"
    | .decode p a r => s!"decode at {p} ({a}): {r}"
    | .prelude r => s!"prelude: {r}"
    | .read p e => s!"read at {p}: {e}"
    | .kernel e p => s!"kernel at {p}: {e}"

def Error.ofAdmission : Ix.Ixon.Admission.Error → Error
  | .limit r => .limit r
  | .decode p a r => .decode p a r
  | .kernel e => .prelude s!"unexpected kernel error from the decoder: {repr e}"

/-- The reading of decoded records: the prelude's state continues into the
stream, and the prelude's records back the store. -/
def readStream (pins : Pins) (pre : Prelude)
    (constants : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint := fun _ => none) :
    Except Error (Array ConLeche.Declaration) := do
  let records := constants.toArray
  let cx := contextOf pins records blobs pre.records hint
  match readRecords cx pre.state records with
  | .ok (_, decls) => pure decls
  | .error (e, i) => throw (.read i e)

/-- The declarations the fold runs over, from the bytes. -/
def prepareWith (pins : Pins) (pre : Prelude)
    (limits : Limits) (records : Records) (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint := fun _ => none) :
    Except Error (Array ConLeche.Declaration) := do
  (preflight limits records blobs).mapError Error.ofAdmission
  let constants ← (decodeRecords limits records).mapError Error.ofAdmission
  let decls ← readStream pins pre constants blobs hint
  pure (ConLeche.Frontend.preparePrelude pre.ix decls)

/-- The entry over an explicit pin table, prelude and Nat-operation pin list
(tests inject them). -/
def checkBytesWith (pins : Pins) (pre : Prelude) (natPins : List ConLeche.NatOpPinSet)
    (limits : Limits) (records : Records) (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint := fun _ => none) :
    Except Error ConLeche.Env := do
  let decls ← prepareWith pins pre limits records blobs hint
  (ConLeche.Cached.checkDecls .verified natPins decls).mapError
    fun (e, i) => .kernel e i

/-- Check exactly the declarations described by the supplied canonical record
bytes with con-leche's verified checker, under the committed pin table, Ixon
prelude and Nat-operation pin variant. -/
def checkBytes (limits : Limits) (records : Records) (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint := fun _ => none) :
    Except Error ConLeche.Env := do
  let pins ← defaultPins.mapError Error.prelude
  let pre ← builtinPrelude.mapError Error.prelude
  let natPins ← builtinNatOpPins.mapError Error.prelude
  checkBytesWith pins pre natPins limits records blobs hint

/-- The reader's context for decoded records under a pin table and a
prelude, as `readStream` builds it: the records' store backed by the
prelude's records, and the recursor index of both. -/
def streamContext (pins : Pins) (pre : Prelude) (constants : List (Address × Ixon.Constant))
    (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint) : Ctx :=
  contextOf pins constants.toArray blobs pre.records hint

/-- Con-leche's verified fold over decoded records: the reader, the prelude,
the fold. `checkBytesWith` is byte admission followed by this
(`checkBytesWith_eq`). -/
def checkConstantsWith (pins : Pins) (pre : Prelude) (natPins : List ConLeche.NatOpPinSet)
    (constants : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint := fun _ => none) :
    Except Error ConLeche.Env := do
  let decls ← readStream pins pre constants blobs hint
  (ConLeche.Cached.checkDecls .verified natPins (ConLeche.Frontend.preparePrelude pre.ix decls)).mapError
    fun (e, i) => .kernel e i

/-- `checkConstantsWith` under the committed pin table, Ixon prelude and
Nat-operation pin variant (as `checkBytes`). -/
def checkConstants (constants : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint := fun _ => none) :
    Except Error ConLeche.Env := do
  let pins ← defaultPins.mapError Error.prelude
  let pre ← builtinPrelude.mapError Error.prelude
  let natPins ← builtinNatOpPins.mapError Error.prelude
  checkConstantsWith pins pre natPins constants blobs hint

universe u

/-- Every accept of the entry, at any pin table and prelude, is an accept
of con-leche's fold on the prepared declarations. -/
theorem checkBytesWith_checkDecls {pins : Pins} {pre : Prelude}
    {natPins : List ConLeche.NatOpPinSet}
    {limits : Limits} {records : Records} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytesWith pins pre natPins limits records blobs hint = .ok env) :
    ∃ decls, prepareWith pins pre limits records blobs hint = .ok decls ∧
      ConLeche.Cached.checkDecls .verified natPins decls = .ok env := by
  unfold checkBytesWith at h
  cases hp : prepareWith pins pre limits records blobs hint with
  | error e => simp [hp, bind, Except.bind] at h
  | ok decls =>
    simp only [hp, bind, Except.bind] at h
    cases hc : ConLeche.Cached.checkDecls .verified natPins decls with
    | error e => simp [hc, Except.mapError] at h
    | ok env' =>
      simp only [hc, Except.mapError, Except.ok.injEq] at h
      exact ⟨decls, rfl, h ▸ hc⟩

/-- **Model existence for the Ixon entry** (any pin table, prelude and
Nat-operation pin list). -/
theorem checkBytesWith_has_model (V : Type u) [ConLeche.SetTheory V]
    {pins : Pins} {pre : Prelude} {natPins : List ConLeche.NatOpPinSet}
    {limits : Limits} {records : Records} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytesWith pins pre natPins limits records blobs hint = .ok env) :
    Nonempty (ConLeche.Model V env) := by
  obtain ⟨decls, _, hc⟩ := checkBytesWith_checkDecls h
  exact ConLeche.model_exists V natPins decls env hc

/-- **Model existence for the Ixon entry**: every environment `checkBytes`
accepts has a model in every set theory. -/
theorem checkBytes_has_model (V : Type u) [ConLeche.SetTheory V]
    {limits : Limits} {records : Records} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    Nonempty (ConLeche.Model V env) := by
  unfold checkBytes at h
  cases hp : defaultPins with
  | error e => simp [hp, bind, Except.bind, Except.mapError] at h
  | ok pins =>
    cases hq : builtinPrelude with
    | error e => simp [hp, hq, bind, Except.bind, Except.mapError] at h
    | ok pre =>
      cases hn : builtinNatOpPins with
      | error e => simp [hp, hq, hn, bind, Except.bind, Except.mapError] at h
      | ok natPins =>
        simp only [hp, hq, hn, bind, Except.bind, Except.mapError] at h
        exact checkBytesWith_has_model V h

end Ix.Ixon.ConLecheAdmission
