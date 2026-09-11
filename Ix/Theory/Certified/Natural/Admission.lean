/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Admission

namespace Ix.Theory.Certified

open Model

universe u v
variable {β : Type u} [DecidableEq β]

/-- Literal support is installed with the canonical Nat model in one atomic
extension, at the reference selected by the public primitive signature. -/
def checkNaturalExtension? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : CheckedInterface signature) (witness : Ordinary.BlockWitness β) :
    Option (CheckedExtension.{u,v} signature store state) :=
  match hp : signature.natType with
  | none => none
  | some pin => do
    let checked ← Natural.check.{u,v} fuel state.entries store pin witness
    let entries := Natural.environment state.entries witness.source witness.recursor witness.mode
    have extension : Extends.{u,v} signature state.entries entries := by
      constructor
      · intro r entry hr
        exact Natural.environment_old checked.down hr
      · intro V _ constants hM
        let constants' := Natural.shape.recursorAssignment constants witness.source witness.recursor witness.mode
        have hm := Natural.assignment_realizes checked.down state.wf constants hM.realizes
        have ha := Ordinary.Shape.publishedAssignment_agrees checked.down.block constants
        exact ⟨constants', hM.extend signature state.present hm ha, ha⟩
    let result : CheckedInterface signature := {
      entries
      wf := Natural.environment_wf checked.down state.wf
      present := ⟨extension.lookup _ _ state.present.1, extension.lookup _ _ state.present.2⟩
    }
    return {
      result, extension
      source := by
        intro r entry hr
        dsimp only [result] at hr
        rcases Natural.environment_source checked.down hr with hold | hordinary | hnatural
        · exact Or.inl hold
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hordinary))))
        · rw [← hp] at hnatural
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hnatural))))))))
    }

def admitNatural? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : AdmittedEnvironment.{u,v} signature store) (witness : Ordinary.BlockWitness β) :
    Option { result : AdmittedEnvironment.{u,v} signature store //
      Extends.{u,v} signature state.entries result.entries } := do
  let checked ← checkNaturalExtension?.{u,v} fuel (store := store) state.interface witness
  return checked.admit state

theorem admitNatural?_extends {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {state : AdmittedEnvironment.{u,v} signature store} {witness : Ordinary.BlockWitness β} {result}
    (_ : admitNatural? fuel state witness = some result) :
    Extends.{u,v} signature state.entries result.val.entries := result.property

end Ix.Theory.Certified
