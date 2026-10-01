/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Admission.Bytes
import Ix.Kernel.Ixon.Prelude
import Ix.Kernel.MainTheorem

/-! # Admission from ordered Ixon record bytes through con-leche

The `checkBytes`-shaped entry of con-leche's verified checker, which the
certified API `Ix.Ixon.Admission.checkBytes` runs:

    preflight → uniqueKeys → decodeRecords → Ixon reader → preparePrelude
              → Ix.Kernel.Cached.checkDecls .verified natPins

* `preflight`, `uniqueKeys` and `decodeRecords` are `Ix.Ixon.Admission`'s:
  the same batch limits, key uniqueness (no two records and no two blobs
  under one address), the same canonical per-record decoding, the same
  error positions.
* The reader is `Ix.Kernel.IxonReader` (keys per D1 (b), regrouping of
  `muts` blocks and projection records, the in-process modeller and the
  projection rewrite), against the supplied records with the Ixon prelude's
  records as a fallback store.
* `preparePrelude` is con-leche's (`Ix/Kernel/Frontend/Prepare.lean`,
  verbatim), with the Ixon prelude (`Ix.Kernel.IxonReader.builtinPrelude`).
* The fold is con-leche's `checkDecls` at `.verified`, at the committed
  Nat-operation pin variant generated from Ixon records
  (`Ix.Kernel.IxonReader.builtinNatOpPins`, decoded from
  `Ix/Kernel/Ixon/NatOpPinData.lean`; the theorem holds at every pin
  list, so the pins are untrusted).

`checkBytes_has_model` is `Ix.Kernel.model_exists` at the prepared
declarations: the reader owes nothing, because the main theorem holds for
every declaration array. The host still supplies record order, address keys
and literal blobs; addresses are keys, not authenticated content hashes. The
entry does not reorder beyond `preparePrelude`: a host order is a dependency
order in which each record follows its references, a pinned `Nat` operation's
certificate ground, and the constants its literals reference
(`IxonReader.literalEdges`; con-leche declines a string literal before the
string-support declarations), as the environment-check driver's order is.
-/

namespace Ix.Ixon.KernelAdmission

open Ix.Kernel (ConstRef)
open Ix.Kernel.IxonReader
open Ix.Ixon.Admission (Limits Records Resource Table preflight uniqueKeys decodeRecords)

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

def Error.ofAdmission : Ix.Ixon.Admission.Error → Error
  | .limit r => .limit r
  | .duplicate t p a => .duplicate t p a
  | .decode p a r => .decode p a r

/-- The reading of decoded records: the prelude's state continues into the
stream, and the prelude's records back the store. -/
def readStream (pins : Pins) (pre : Prelude)
    (constants : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Array Ix.Kernel.Declaration) := do
  let records := constants.toArray
  let cx := contextOf pins records blobs pre.records hint
  match readRecords cx pre.state records with
  | .ok (_, decls) => pure decls
  | .error (e, i) => throw (.read i e)

/-- The declarations the fold runs over, from the bytes. -/
def prepareWith (pins : Pins) (pre : Prelude)
    (limits : Limits) (records : Records) (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error (Array Ix.Kernel.Declaration) := do
  (preflight limits records blobs).mapError Error.ofAdmission
  (uniqueKeys records blobs).mapError Error.ofAdmission
  let constants ← (decodeRecords limits records).mapError Error.ofAdmission
  let decls ← readStream pins pre constants blobs hint
  pure (Ix.Kernel.Frontend.preparePrelude pre.ix decls)

/-- The entry over an explicit pin table, prelude and Nat-operation pin list
(tests inject them). -/
def checkBytesWith (pins : Pins) (pre : Prelude) (natPins : List Ix.Kernel.NatOpPinSet)
    (limits : Limits) (records : Records) (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error Ix.Kernel.Env := do
  let decls ← prepareWith pins pre limits records blobs hint
  (Ix.Kernel.Cached.checkDecls .verified natPins decls).mapError
    fun (e, i) => .kernel e i

/-- Check exactly the declarations described by the supplied canonical record
bytes with con-leche's verified checker, under the committed pin table, Ixon
prelude and Nat-operation pin variant. -/
def checkBytes (limits : Limits) (records : Records) (blobs : List (Address × ByteArray))
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
    (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) : Ctx :=
  contextOf pins constants.toArray blobs pre.records hint

/-- Con-leche's verified fold over decoded records: the reader, the prelude,
the fold. `checkBytesWith` is byte admission followed by this
(`checkBytesWith_eq`). -/
def checkConstantsWith (pins : Pins) (pre : Prelude) (natPins : List Ix.Kernel.NatOpPinSet)
    (constants : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error Ix.Kernel.Env := do
  let decls ← readStream pins pre constants blobs hint
  (Ix.Kernel.Cached.checkDecls .verified natPins (Ix.Kernel.Frontend.preparePrelude pre.ix decls)).mapError
    fun (e, i) => .kernel e i

/-- `checkConstantsWith` under the committed pin table, Ixon prelude and
Nat-operation pin variant (as `checkBytes`). -/
def checkConstants (constants : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Error Ix.Kernel.Env := do
  let pins ← defaultPins.mapError Error.prelude
  let pre ← builtinPrelude.mapError Error.prelude
  let natPins ← builtinNatOpPins.mapError Error.prelude
  checkConstantsWith pins pre natPins constants blobs hint

universe u

/-- Every accept of the entry, at any pin table and prelude, is an accept
of con-leche's fold on the prepared declarations. -/
theorem checkBytesWith_checkDecls {pins : Pins} {pre : Prelude}
    {natPins : List Ix.Kernel.NatOpPinSet}
    {limits : Limits} {records : Records} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytesWith pins pre natPins limits records blobs hint = .ok env) :
    ∃ decls, prepareWith pins pre limits records blobs hint = .ok decls ∧
      Ix.Kernel.Cached.checkDecls .verified natPins decls = .ok env := by
  unfold checkBytesWith at h
  cases hp : prepareWith pins pre limits records blobs hint with
  | error e => simp [hp, bind, Except.bind] at h
  | ok decls =>
    simp only [hp, bind, Except.bind] at h
    cases hc : Ix.Kernel.Cached.checkDecls .verified natPins decls with
    | error e => simp [hc, Except.mapError] at h
    | ok env' =>
      simp only [hc, Except.mapError, Except.ok.injEq] at h
      exact ⟨decls, rfl, h ▸ hc⟩

/-- **Model existence for the Ixon entry** (any pin table, prelude and
Nat-operation pin list). -/
theorem checkBytesWith_has_model (V : Type u) [Ix.Kernel.SetTheory V]
    {pins : Pins} {pre : Prelude} {natPins : List Ix.Kernel.NatOpPinSet}
    {limits : Limits} {records : Records} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytesWith pins pre natPins limits records blobs hint = .ok env) :
    Nonempty (Ix.Kernel.Model V env) := by
  obtain ⟨decls, _, hc⟩ := checkBytesWith_checkDecls h
  exact Ix.Kernel.model_exists V natPins decls env hc

/-- **Model existence for the Ixon entry**: every environment `checkBytes`
accepts has a model in every set theory. -/
theorem checkBytes_has_model (V : Type u) [Ix.Kernel.SetTheory V]
    {limits : Limits} {records : Records} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    Nonempty (Ix.Kernel.Model V env) := by
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

end Ix.Ixon.KernelAdmission
