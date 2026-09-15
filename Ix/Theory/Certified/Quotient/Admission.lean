/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Admission

namespace Ix.Theory.Certified

open Model

universe u v
variable {β : Type u} [DecidableEq β]

/-- Publish the exact quotient primitive package only after all source and
formation checks. Its values and computation laws are produced internally. -/
def checkQuotientExtension? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : CheckedInterface signature) (witness : Quotient.Witness β) :
    Option (CheckedExtension.{u,v} signature store state) := do
  let checked ← Quotient.check.{u,v} fuel state.entries store witness
  let refs := witness.refs
  have extension : Extends.{u,v} signature state.entries (refs.environment state.entries) := by
    constructor
    · exact fun _ _ h => Quotient.environment_old checked.down h
    · intro V _ constants hM
      let constants' := refs.assignment constants
      have ha := Quotient.assignment_agrees checked.down constants
      have hm := Quotient.assignment_realizes checked.down state.wf constants hM.realizes
      exact ⟨constants', hM.extend signature state.present hm ha, ha⟩
  let result : CheckedInterface signature := {
    entries := refs.environment state.entries
    wf := Quotient.environment_wf checked.down state.wf
    present := ⟨extension.lookup _ _ state.present.1, extension.lookup _ _ state.present.2⟩
  }
  return {
    result, extension
    source := by
      intro r entry hr
      dsimp only [result] at hr
      rcases Quotient.environment_source checked.down hr with hold | hnew
      · exact Or.inl hold
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hnew))))))
  }

def admitQuotient? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : AdmittedEnvironment.{u,v} signature store) (witness : Quotient.Witness β) :
    Option { result : AdmittedEnvironment.{u,v} signature store //
      Extends.{u,v} signature state.entries result.entries } := do
  let checked ← checkQuotientExtension?.{u,v} fuel (store := store) state.interface witness
  return checked.admit state

theorem admitQuotient?_extends {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {state : AdmittedEnvironment.{u,v} signature store} {witness : Quotient.Witness β} {result}
    (_ : admitQuotient? fuel state witness = some result) :
    Extends.{u,v} signature state.entries result.val.entries := result.property

end Ix.Theory.Certified
