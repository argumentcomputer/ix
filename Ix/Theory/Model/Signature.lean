/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Extension

namespace Ix.Theory.Model

universe u v
variable {β : Type u}

/-- An internal signature overlay does not by itself admit declarations. -/
def Environment.overlay (entries additions : Environment β) : Environment β :=
  fun r => match additions r with
    | some entry => some entry
    | none => entries r

def Assignment.overlay (constants values : Assignment β V) (additions : Environment β) : Assignment β V :=
  fun r levels => match additions r with
    | some _ => values r levels
    | none => constants r levels

def Environment.Fresh (entries additions : Environment β) : Prop :=
  ∀ r entry, additions r = some entry → entries r = none

theorem Environment.overlay_new {entries additions : Environment β} {r : ConstRef β}
    {entry : ConstantEntry β} (h : additions r = some entry) :
    entries.overlay additions r = some entry := by simp only [overlay, h]

theorem Environment.overlay_old {entries additions : Environment β}
    (hf : entries.Fresh additions) {r : ConstRef β} {entry : ConstantEntry β}
    (h : entries r = some entry) : entries.overlay additions r = some entry := by
  cases ha : additions r with
  | none => simpa only [overlay, ha] using h
  | some new => have he := hf r new ha; rw [h] at he; contradiction

theorem Assignment.overlay_agrees {entries additions : Environment β} (hf : entries.Fresh additions)
    (constants values : Assignment β V) : Assignment.AgreesOn entries constants (constants.overlay values additions) := by
  intro r entry hr levels
  cases ha : additions r with
  | none => simp only [overlay, ha]
  | some new => have he := hf r new ha; rw [hr] at he; contradiction

theorem AExpr.ReferencesIn.overlay {entries additions : Environment β} {e : AExpr β}
    (h : e.ReferencesIn entries) : e.ReferencesIn (entries.overlay additions) := by
  intro r hr
  cases ha : additions r with
  | none => simpa only [Environment.overlay, ha] using h r hr
  | some _ => simp only [Environment.overlay, ha, Option.isSome_some]

theorem ConstantFact.ReferencesIn.overlay {entries additions : Environment β} {fact : ConstantFact β}
    (h : fact.ReferencesIn entries) : fact.ReferencesIn (entries.overlay additions) := by
  intro r hr
  cases ha : additions r with
  | none => simpa only [Environment.overlay, ha] using h r hr
  | some _ => simp only [Environment.overlay, ha, Option.isSome_some]

/-- The syntactic closure needed for a signature entry. Formation and the
value's membership are separate obligations and cannot be supplied by data. -/
structure EntryClosed (entries : Environment β) (entry : ConstantEntry β) : Prop where
  typeScope : entry.type.Scope entry.universes 0
  bodyScope : ∀ body, entry.body = some body → body.Scope entry.universes 0
  typeReferences : entry.type.ReferencesIn entries
  bodyReferences : ∀ body, entry.body = some body → body.ReferencesIn entries
  equationScope : ∀ law ∈ entry.equations,
    law.lhs.Scope entry.universes 0 ∧ law.rhs.Scope entry.universes 0
  equationReferences : ∀ law ∈ entry.equations,
    law.lhs.ReferencesIn entries ∧ law.rhs.ReferencesIn entries
  factScope : ∀ fact ∈ entry.facts, fact.Scope entry.universes
  factReferences : ∀ fact ∈ entry.facts, fact.ReferencesIn entries

theorem Environment.WF.overlay {entries additions : Environment β} (hE : entries.WF)
    (hN : ∀ r entry, additions r = some entry → EntryClosed entries entry) :
    (entries.overlay additions).WF := by
  constructor
  · intro r entry hr
    unfold Environment.overlay at hr
    split at hr
    · cases Option.some.inj hr; exact (hN _ _ ‹_›).typeScope
    · exact hE.typeScope r entry hr
  · intro r entry hr body hb
    unfold Environment.overlay at hr
    split at hr
    · cases Option.some.inj hr; exact (hN _ _ ‹_›).bodyScope body hb
    · exact hE.bodyScope r entry hr body hb
  · intro r entry hr
    unfold Environment.overlay at hr
    split at hr
    · cases Option.some.inj hr; exact (hN _ _ ‹_›).typeReferences.overlay
    · exact (hE.typeReferences r entry hr).overlay
  · intro r entry hr body hb
    unfold Environment.overlay at hr
    split at hr
    · cases Option.some.inj hr; exact ((hN _ _ ‹_›).bodyReferences body hb).overlay
    · exact (hE.bodyReferences r entry hr body hb).overlay
  · intro r entry hr law hl
    unfold Environment.overlay at hr
    split at hr
    · cases Option.some.inj hr; exact (hN _ _ ‹_›).equationScope law hl
    · exact hE.equationScope r entry hr law hl
  · intro r entry hr law hl
    unfold Environment.overlay at hr
    split at hr
    · cases Option.some.inj hr
      exact ⟨((hN _ _ ‹_›).equationReferences law hl).1.overlay,
        ((hN _ _ ‹_›).equationReferences law hl).2.overlay⟩
    · exact ⟨(hE.equationReferences r entry hr law hl).1.overlay,
        (hE.equationReferences r entry hr law hl).2.overlay⟩
  · intro r entry hr fact hf
    unfold Environment.overlay at hr
    split at hr
    · cases Option.some.inj hr; exact (hN _ _ ‹_›).factScope fact hf
    · exact hE.factScope r entry hr fact hf
  · intro r entry hr fact hf
    unfold Environment.overlay at hr
    split at hr
    · cases Option.some.inj hr; exact ((hN _ _ ‹_›).factReferences fact hf).overlay
    · exact (hE.factReferences r entry hr fact hf).overlay

variable {V : Type v} [SetTheory V]

theorem Realizes.overlay {entries additions : Environment β} {constants : Assignment β V}
    (hM : Realizes constants entries)
    (hN : ∀ r entry, additions r = some entry → EntryRealization constants r entry) :
    Realizes constants (entries.overlay additions) := by
  constructor
  · intro r entry hr
    unfold Environment.overlay at hr
    split at hr
    · cases Option.some.inj hr; exact (hN _ _ ‹_›).typeValid
    · exact hM.typeValid r entry hr
  · intro r entry hr
    unfold Environment.overlay at hr
    split at hr
    · cases Option.some.inj hr; exact (hN _ _ ‹_›).member
    · exact hM.member r entry hr
  · intro r entry hr
    unfold Environment.overlay at hr
    split at hr
    · cases Option.some.inj hr; exact (hN _ _ ‹_›).bodyValid
    · exact hM.bodyValid r entry hr
  · intro r entry hr
    unfold Environment.overlay at hr
    split at hr
    · cases Option.some.inj hr; exact (hN _ _ ‹_›).bodyValue
    · exact hM.bodyValue r entry hr
  · intro r entry hr
    unfold Environment.overlay at hr
    split at hr
    · cases Option.some.inj hr; exact (hN _ _ ‹_›).equationValue
    · exact hM.equationValue r entry hr
  · intro r entry hr
    unfold Environment.overlay at hr
    split at hr
    · cases Option.some.inj hr; exact (hN _ _ ‹_›).factMeaning
    · exact hM.factMeaning r entry hr

end Ix.Theory.Model
