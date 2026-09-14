/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Admission

namespace Ix.Theory.Certified

open Model

universe u v
variable {β : Type u} [DecidableEq β]

/-- Standard axiom schemas acquire values only after exact source, prerequisite
interface, and whole-type checks. No caller-supplied realization is accepted. -/
def checkStandardExtension? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : CheckedInterface signature) (witness : Standard.Witness β) :
    Option (CheckedExtension.{u,v} signature store state) := do
  let checked ← Standard.check.{u,v} fuel state.entries store witness
  have extension : Extends.{u,v} signature state.entries
      (state.entries.insert witness.ref witness.spec.entry) := by
    constructor
    · exact fun _ _ h => Environment.insert_old checked.down.fresh h
    · intro V _ constants hM
      let constants' := Standard.assignment constants witness
      have ha := Standard.assignment_agrees checked.down constants
      have hm := Standard.assignment_realizes checked.down state.wf constants hM.realizes
      exact ⟨constants', hM.extend signature state.present hm ha, ha⟩
  let result : CheckedInterface signature := {
    entries := state.entries.insert witness.ref witness.spec.entry
    wf := Standard.environment_wf checked.down state.wf
    present := state.present.insert signature checked.down.fresh
  }
  return {
    result, extension
    source := by
      intro r entry hr
      dsimp only [result] at hr
      unfold Environment.insert at hr
      split at hr
      next he =>
        subst r
        cases Option.some.inj hr
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨witness.spec, checked.down.exactSource, rfl⟩)))))
      next => exact Or.inl hr
  }

def admitStandard? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : AdmittedEnvironment.{u,v} signature store) (witness : Standard.Witness β) :
    Option { result : AdmittedEnvironment.{u,v} signature store //
      Extends.{u,v} signature state.entries result.entries } := do
  let checked ← checkStandardExtension?.{u,v} fuel (store := store) state.interface witness
  return checked.admit state

theorem admitStandard?_extends {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {state : AdmittedEnvironment.{u,v} signature store} {witness : Standard.Witness β} {result}
    (_ : admitStandard? fuel state witness = some result) :
    Extends.{u,v} signature state.entries result.val.entries := result.property

end Ix.Theory.Certified
