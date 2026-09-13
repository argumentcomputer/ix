/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Signature
import Ix.Theory.Certified.Basis.Equality

/-! Model equations may follow from checked conversion or from a checked
proof of the realized equality relation. Both complete endpoints and their
common type are checked before an equation can be published. -/

namespace Ix.Theory.Certified.Modeled

open Model Model.SetTheory

universe u v
variable {β : Type u} [DecidableEq β]

inductive EquationProof (β : Type u) where
  | conversion (witness : ConversionWitness β)
  | propositional (family reflexivity recursor : ConstRef β)
      (proof : AExpr β) (witness : TypingWitness β)

structure EquationWitness (β : Type u) where
  formation : Signature.RuleWitness β
  proof : EquationProof β

structure CheckedEquation (entries : Environment β) (rule : Signature.Rule β) : Prop where
  formed : Signature.RuleFormed.{u,v} entries rule
  equality : ConversionClaim.{u,v} entries [] rule.lhs rule.rhs

omit [DecidableEq β] in
theorem propositional_equation {entries : Environment β} {family reflexivity recursor : ConstRef β}
    (interface : Basis.Equality.Interface entries family reflexivity recursor)
    {rule : Signature.Rule β} {level : VLevel} {proof : AExpr β}
    (type : TypingClaim.{u,v} entries [] rule.type (.sort level))
    (lhs : TypingClaim.{u,v} entries [] rule.lhs rule.type)
    (rhs : TypingClaim.{u,v} entries [] rule.rhs rule.type)
    (checked : TypingClaim.{u,v} entries [] proof
      (Basis.Equality.applied family level rule.type rule.lhs rule.rhs)) :
    ConversionClaim.{u,v} entries [] rule.lhs rule.rhs := by
  intro V _ constants hM levels env hΓ
  have htype := (type V constants hM levels env hΓ).2.2
  have hlhs := (lhs V constants hM levels env hΓ).2.2
  have hrhs := (rhs V constants hM levels env hΓ).2.2
  have hproof := (checked V constants hM levels env hΓ).2.2
  apply Basis.Equality.eq_of_mem interface hM (by simpa only [interp] using htype) hlhs hrhs
  simpa only [Basis.Equality.applied, AExpr.appN, interp, List.map_cons, List.map_nil,
    Basis.Equality.value] using hproof

def checkEquation? (fuel : Nat) (entries : Environment β) (rule : Signature.Rule β)
    (witness : EquationWitness β) : Option (CheckedClaim.{u} (CheckedEquation.{u,v} entries rule)) := do
  let formed ← Signature.checkRule.{u,v} fuel entries rule witness.formation
  match witness.proof with
  | .conversion witness =>
    let equality ← verifyConversion.{u,v} fuel rule.universes entries [] rule.lhs rule.rhs witness
    return ⟨formed.down, equality.down⟩
  | .propositional family reflexivity recursor proof typing =>
    if hi : Basis.Equality.Interface entries family reflexivity recursor then do
      let type ← verifyType.{u,v} fuel rule.universes entries [] rule.type
        (.sort witness.formation.level) witness.formation.type
      let checked ← verifyType.{u,v} fuel rule.universes entries [] proof
        (Basis.Equality.applied family witness.formation.level rule.type rule.lhs rule.rhs) typing
      return ⟨formed.down, propositional_equation hi type.down formed.down.lhs formed.down.rhs checked.down⟩
    else none

theorem checkEquation?_sound {fuel : Nat} {entries : Environment β} {rule : Signature.Rule β}
    {witness : EquationWitness β} {result}
    (_ : checkEquation?.{u,v} fuel entries rule witness = some result) :
    CheckedEquation.{u,v} entries rule := result.down

end Ix.Theory.Certified.Modeled
