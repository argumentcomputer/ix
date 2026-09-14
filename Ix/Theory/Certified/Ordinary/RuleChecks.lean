/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Ordinary.RecursorStage

namespace Ix.Theory.Certified.Ordinary

open Model Model.SetTheory Model.SetModel Inductive

universe u v
variable {β : Type u} [DecidableEq β]

structure RuleWitness (β : Type u) where
  typeLevel : VLevel
  typeWitness : TypingWitness β
  lhsWitness : TypingWitness β
  rhsWitness : TypingWitness β

namespace Shape

/-- These checks run against the formed recursor signature with no equations.
They establish the whole closed rule's type, both endpoint memberships, and
the syntactic scope/reference facts needed when its equation is published. -/
structure RuleFormation (entries : Environment β) (shape : Shape β) (source recursor : β)
    (mode : ElimMode) (i : Nat) (ctor : Constructor β) : Prop where
  scope : (shape.ruleLhs source recursor mode i ctor).Scope (mode.recUvars shape.universes) 0 ∧
    (shape.ruleRhs source recursor mode i ctor).Scope (mode.recUvars shape.universes) 0
  references : (shape.ruleLhs source recursor mode i ctor).ReferencesIn entries ∧
    (shape.ruleRhs source recursor mode i ctor).ReferencesIn entries
  type : ∃ l, TypingClaim.{u,v} entries [] (shape.ruleType source mode i ctor) (.sort l) ∧
    (mode = .small → ∀ levels, l.eval levels = 0)
  lhs : TypingClaim.{u,v} entries [] (shape.ruleLhs source recursor mode i ctor) (shape.ruleType source mode i ctor)
  rhs : TypingClaim.{u,v} entries [] (shape.ruleRhs source recursor mode i ctor) (shape.ruleType source mode i ctor)

def checkRule (fuel : Nat) (entries : Environment β) (shape : Shape β) (source recursor : β)
    (mode : ElimMode) (i : Nat) (ctor : Constructor β) (witness : RuleWitness β) :
    Option (CheckedClaim.{u} (RuleFormation.{u,v} entries shape source recursor mode i ctor)) :=
  if hs : (shape.ruleLhs source recursor mode i ctor).Scope (mode.recUvars shape.universes) 0 ∧
      (shape.ruleRhs source recursor mode i ctor).Scope (mode.recUvars shape.universes) 0 then
    if hr : (shape.ruleLhs source recursor mode i ctor).ReferencesIn entries ∧
        (shape.ruleRhs source recursor mode i ctor).ReferencesIn entries then
      if hsmall : mode = .small → LevelEq.check (mode.recUvars shape.universes) witness.typeLevel .zero = true then do
        let ht ← verifyType.{u,v} fuel (mode.recUvars shape.universes) entries []
          (shape.ruleType source mode i ctor) (.sort witness.typeLevel) witness.typeWitness
        let hl ← verifyType.{u,v} fuel (mode.recUvars shape.universes) entries []
          (shape.ruleLhs source recursor mode i ctor) (shape.ruleType source mode i ctor) witness.lhsWitness
        let hh ← verifyType.{u,v} fuel (mode.recUvars shape.universes) entries []
          (shape.ruleRhs source recursor mode i ctor) (shape.ruleType source mode i ctor) witness.rhsWitness
        return ⟨⟨hs, hr, ⟨witness.typeLevel, ht.down, by
          intro he levels
          exact (LevelEq.check_sound (hsmall he)).2.2 levels⟩, hl.down, hh.down⟩⟩
      else none
    else none
  else none

def checkRules (fuel : Nat) (entries : Environment β) (shape : Shape β) (source recursor : β)
    (mode : ElimMode) : (ctors : List (Constructor β × Nat)) → List (RuleWitness β) →
      Option (CheckedClaim.{u} (∀ ctor i, (ctor, i) ∈ ctors →
        RuleFormation.{u,v} entries shape source recursor mode i ctor))
  | [], [] => some ⟨by simp⟩
  | (ctor, i) :: ctors, witness :: witnesses => do
    let rule ← checkRule fuel entries shape source recursor mode i ctor witness
    let rest ← checkRules fuel entries shape source recursor mode ctors witnesses
    return ⟨by
      intro ctor' i' hc
      rcases List.mem_cons.mp hc with he | hc
      · cases he; exact rule.down
      · exact rest.down ctor' i' hc⟩
  | _, _ => none

variable {V : Type v} [SetTheory V]

omit [DecidableEq β] in
theorem small_rule_eq {entries : Environment β} {shape : Shape β} {source recursor : β}
    {i : Nat} {ctor : Constructor β}
    (h : RuleFormation.{u,v} entries shape source recursor .small i ctor)
    (constants : Assignment β V) (hM : Realizes constants entries) (levels : List Nat) (env : Nat → V) :
    interp constants levels env (shape.ruleLhs source recursor .small i ctor) =
      interp constants levels env (shape.ruleRhs source recursor .small i ctor) := by
  obtain ⟨l, ht, hz⟩ := h.type
  have hΓ := Context.valid_nil constants levels env
  have hprop := (ht V constants hM levels env hΓ).2.2
  rw [interp, hz rfl levels, univ_zero] at hprop
  exact subsingleton_of_mem_univZero hprop (h.lhs V constants hM levels env hΓ).2.2
    (h.rhs V constants hM levels env hΓ).2.2

end Shape
end Ix.Theory.Certified.Ordinary
