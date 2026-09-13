/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Ordinary.Constructors
import Ix.Theory.Model.Inductive.Recursor

namespace Ix.Theory.Certified.Ordinary

open Model Model.SetTheory Model.SetTheory.Tower

universe u v
variable {β : Type u}

def LargeEvidence (entries : Environment β) (shape : Shape β) : Prop :=
  (∀ levels, shape.level.eval levels ≠ 0) ∨ shape.constructors = [] ∨
    ∃ ctor, shape.constructors = [ctor] ∧
      TelescopeProp.{u,v} entries shape.parameterContext ctor.fields shape.level

def checkLarge [DecidableEq β] (fuel : Nat) (entries : Environment β) (witness : ShapeWitness β) :
    Option (CheckedClaim.{u} (LargeEvidence.{u,v} entries witness.shape)) :=
  if hp : zeroCondition witness.shape.level = .never then
    some ⟨Or.inl (by
      intro levels he
      have hz := zeroCondition_correct witness.shape.level levels
      simp only [hp, PropWhen.holds_never, he, beq_self_eq_true, Bool.false_eq_true] at hz)⟩
  else
    match hc : witness.shape.constructors, witness.constructors with
    | [], [] => some ⟨Or.inr (Or.inl hc)⟩
    | [ctor], [proof] => do
      let fields ← verifyPropTelescope.{u,v} fuel witness.shape.universes entries witness.shape.level
        witness.shape.parameterContext ctor.fields proof.fields
      return ⟨Or.inr (Or.inr ⟨ctor, hc, fields.down⟩)⟩
    | _, _ => none

theorem checkLarge_sound [DecidableEq β] {fuel : Nat} {entries : Environment β} {witness : ShapeWitness β}
    {result} (_ : checkLarge.{u,v} fuel entries witness = some result) :
    LargeEvidence.{u,v} entries witness.shape := result.down

variable {V : Type v} [SetTheory V]

theorem Shape.container_large {entries : Environment β} {shape : Shape β}
    (hlarge : LargeEvidence.{u,v} entries shape) {constants : Assignment β V}
    (hM : Realizes constants entries) {levels : List Nat} {env : Nat → V}
    (hΓ : shape.parameterContext.Valid constants levels env) :
    (shape.container constants levels env).LargeElim (shape.level.eval levels) := by
  intro hw i hi a b ha hb
  rcases hlarge with hpos | hempty | ⟨ctor, hsingle, hprop⟩
  · exact (hpos levels hw).elim
  · obtain ⟨j, ctor, xs, hc, _, _⟩ := Shape.mem_allShapes (mem_sep.mp ha).1
    simp only [hempty, List.getElem?_nil] at hc
    contradiction
  · obtain ⟨j, ca, xs, hca, hxs, rfl⟩ := Shape.mem_allShapes (mem_sep.mp ha).1
    obtain ⟨k, cb, ys, hcb, hys, rfl⟩ := Shape.mem_allShapes (mem_sep.mp hb).1
    have hj : j = 0 := by cases j <;> simp_all
    have hk : k = 0 := by cases k <;> simp_all
    subst j k
    have heca : ctor = ca := by simpa only [hsingle, List.getElem?_cons_zero, Option.some.injEq] using hca
    have hecb : ctor = cb := by simpa only [hsingle, List.getElem?_cons_zero, Option.some.injEq] using hcb
    subst ca cb
    have he := Telescope.fits_unique_of_prop (hprop V constants hM levels env hΓ hw) hxs hys
    rw [he]

end Ix.Theory.Certified.Ordinary
