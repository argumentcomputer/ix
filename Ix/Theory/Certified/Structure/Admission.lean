/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Admission

namespace Ix.Theory.Certified

open Model

universe u v
variable {β : Type u} [DecidableEq β]

/-- Construct the structure and its projection facts in one extension of the
original prefix. This never strengthens an already admitted arbitrary model
by assuming that it used this producer's concrete field representation. -/
def checkStructureExtension? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : CheckedInterface signature) (witness : Structure.Witness β) :
    Option (CheckedExtension.{u,v} signature store state) := do
  let checked ← Structure.check.{u,v} fuel state.entries store witness
  let d := witness.facts.description
  let block := witness.facts.block
  let entries := d.publishedEnvironment state.entries block.source block.recursor block.mode
  have extension : Extends.{u,v} signature state.entries entries := by
    constructor
    · intro r entry hr
      exact d.publishedEnvironment_old checked.down hr
    · intro V _ constants hM
      let constants' := d.ordinary.recursorAssignment constants block.source block.recursor block.mode
      have hm := d.publishedAssignment_realizes checked.down state.wf constants hM.realizes
      have ha := Ordinary.Shape.publishedAssignment_agrees checked.down.facts.block constants
      exact ⟨constants', hM.extend signature state.present hm ha, ha⟩
  let result : CheckedInterface signature := {
    entries
    wf := d.publishedEnvironment_wf checked.down state.wf
    present := ⟨extension.lookup _ _ state.present.1, extension.lookup _ _ state.present.2⟩
  }
  return {
    result, extension
    source := by
      intro r entry hr
      dsimp only [result] at hr
      rcases Structure.publishedEntry_source checked.down hr with hold | hordinary | hstructure
      · exact Or.inl hold
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hordinary))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hstructure)))))))
  }

def admitStructure? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : AdmittedEnvironment.{u,v} signature store) (witness : Structure.Witness β) :
    Option { result : AdmittedEnvironment.{u,v} signature store //
      Extends.{u,v} signature state.entries result.entries } := do
  let checked ← checkStructureExtension?.{u,v} fuel (store := store) state.interface witness
  return checked.admit state

theorem admitStructure?_extends {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {state : AdmittedEnvironment.{u,v} signature store} {witness : Structure.Witness β} {result}
    (_ : admitStructure? fuel state witness = some result) :
    Extends.{u,v} signature state.entries result.val.entries := result.property

end Ix.Theory.Certified
