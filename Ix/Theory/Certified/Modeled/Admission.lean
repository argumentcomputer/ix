/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Admission

namespace Ix.Theory.Certified

open Model

universe u v
variable {β : Type u} [DecidableEq β]

/-- Simultaneous model companions preserve every earlier interpretation.
Models and their equation proofs must already be available through preceding
admissions; the new source block cannot justify its own model. -/
def checkModeledExtension? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : CheckedInterface signature) (witness : Modeled.Witness β) :
    Option (CheckedExtension.{u,v} signature store state) := do
  let checked ← Modeled.check?.{u,v} fuel state.entries store witness
  let entries := Modeled.environment state.entries witness.companions
  have extension : Extends.{u,v} signature state.entries entries := by
    constructor
    · intro ref entry he
      exact Environment.overlay_old checked.down.models.fresh_overlay he
    · intro V _ constants hM
      let constants' := Modeled.assignment constants witness.companions
      have hm := Modeled.assignment_realizes checked.down.models state.wf constants hM.realizes
      have ha := Modeled.assignment_agrees checked.down.models constants
      exact ⟨constants', hM.extend signature state.present hm ha, ha⟩
  let result : CheckedInterface signature := {
    entries
    wf := Modeled.environment_wf checked.down.models state.wf
    present := ⟨extension.lookup _ _ state.present.1, extension.lookup _ _ state.present.2⟩
  }
  return {
    result, extension
    source := by
      intro ref entry he
      dsimp only [result] at he
      rcases Modeled.publishedEntry_source checked.down he with old | new
      · exact Or.inl old
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr new))))))))
  }

def admitModeled? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : AdmittedEnvironment.{u,v} signature store) (witness : Modeled.Witness β) :
    Option { result : AdmittedEnvironment.{u,v} signature store //
      Extends.{u,v} signature state.entries result.entries } := do
  let checked ← checkModeledExtension?.{u,v} fuel (store := store) state.interface witness
  return checked.admit state

theorem admitModeled?_extends {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {state : AdmittedEnvironment.{u,v} signature store} {witness : Modeled.Witness β} {result}
    (_ : admitModeled? fuel state witness = some result) :
    Extends.{u,v} signature state.entries result.val.entries := result.property

end Ix.Theory.Certified
