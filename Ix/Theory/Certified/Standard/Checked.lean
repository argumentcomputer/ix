/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Standard.Realization

namespace Ix.Theory.Certified.Standard

open Model Model.SetTheory

universe u v
variable {β : Type u} [DecidableEq β]

structure Witness (β : Type u) where
  ref : ConstRef β
  spec : Spec β
  level : VLevel
  typing : TypingWitness β

structure Checked (entries : Environment β) (store : Store β) (witness : Witness β) : Prop where
  exactSource : store.lookup witness.ref = some witness.spec.source
  fresh : entries witness.ref = none
  prerequisites : witness.spec.Prerequisites entries
  scope : witness.spec.type.Scope witness.spec.universes 0
  references : witness.spec.type.ReferencesIn entries
  typing : TypingClaim.{u,v} entries [] witness.spec.type (.sort witness.level)

def check (fuel : Nat) (entries : Environment β) (store : Store β) (witness : Witness β) :
    Option (CheckedClaim.{u} (Checked.{u,v} entries store witness)) :=
  if hs : store.lookup witness.ref = some witness.spec.source then
    if hf : entries witness.ref = none then
      if hp : witness.spec.Prerequisites entries then
        if hc : witness.spec.type.Scope witness.spec.universes 0 then
          if hr : witness.spec.type.ReferencesIn entries then do
            let ht ← verifyType.{u,v} fuel witness.spec.universes entries []
              witness.spec.type (.sort witness.level) witness.typing
            return ⟨⟨hs, hf, hp, hc, hr, ht.down⟩⟩
          else none
        else none
      else none
    else none
  else none

theorem check_sound {fuel : Nat} {entries : Environment β} {store : Store β} {witness : Witness β}
    {result} (_ : check.{u,v} fuel entries store witness = some result) :
    Checked.{u,v} entries store witness := result.down

def EntrySource (store : Store β) (ref : ConstRef β) (entry : ConstantEntry β) : Prop :=
  ∃ spec : Spec β, store.lookup ref = some spec.source ∧ entry = spec.entry

variable {entries : Environment β} {store : Store β} {witness : Witness β}

theorem environment_wf (h : Checked.{u,v} entries store witness) (hE : entries.WF) :
    (entries.insert witness.ref witness.spec.entry).WF := by
  apply hE.insert h.scope (by simp [Spec.entry]) h.references
    (by simp [Spec.entry]) (by simp [Spec.entry]) (by simp [Spec.entry])
    (by simp [Spec.entry]) (by simp [Spec.entry])

variable {V : Type v} [SetTheory V]

noncomputable def assignment (constants : Assignment β V) (witness : Witness β) : Assignment β V :=
  constants.insert witness.ref (witness.spec.value constants)

theorem assignment_agrees (h : Checked.{u,v} entries store witness) (constants : Assignment β V) :
    Assignment.AgreesOn entries constants (assignment constants witness) :=
  Assignment.insert_agrees h.fresh _ _

theorem assignment_realizes (h : Checked.{u,v} entries store witness) (hE : entries.WF)
    (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (assignment constants witness) (entries.insert witness.ref witness.spec.entry) := by
  have ha := assignment_agrees h constants
  apply (hM.of_agrees hE ha).insert
  constructor
  · intro levels hn env
    exact (h.typing V (assignment constants witness) (hM.of_agrees hE ha) levels env
      (Context.valid_nil (assignment constants witness) levels env)).1
  · intro levels hn env
    change (assignment constants witness) witness.ref levels ∈ˢ
      interp (assignment constants witness) levels env witness.spec.type
    rw [ha.interp h.references]
    rw [assignment, Assignment.insert_same]
    exact witness.spec.value_mem h.prerequisites hM levels hn env
  · intro body hb; cases hb
  · intro body hb; cases hb
  · intro law hl; simp only [Spec.entry, List.not_mem_nil] at hl
  · intro fact hf; simp only [Spec.entry, List.not_mem_nil] at hf

end Ix.Theory.Certified.Standard
