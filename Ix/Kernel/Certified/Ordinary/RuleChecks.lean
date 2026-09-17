/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Ordinary/RuleChecks.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store and its exact-source facts are removed (comparing the
stored block with the generated one is the caller's check) and the recursor is
member 1 of the family's block; `checkRule` and `checkRules` infer instead of
validating witnesses, and `RuleFormation` records the rule type's scope and
references for the published typed facts.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Ordinary.RecursorStage

namespace Ix.Kernel.Certified.Ordinary

open Model Model.SetTheory Model.SetModel Inductive

universe u v
variable {β : Type u} [DecidableEq β]

namespace Shape

/-- These checks run against the formed recursor signature with no equations.
They establish the whole closed rule's type, both endpoint memberships, and
the syntactic scope/reference facts needed when its equation is published. -/
structure RuleFormation (entries : Environment β) (shape : Shape β) (source : β)
    (mode : ElimMode) (i : Nat) (ctor : Constructor β) : Prop where
  scope : (shape.ruleLhs source mode i ctor).Scope (mode.recUvars shape.universes) 0 ∧
    (shape.ruleRhs source mode i ctor).Scope (mode.recUvars shape.universes) 0
  references : (shape.ruleLhs source mode i ctor).ReferencesIn entries ∧
    (shape.ruleRhs source mode i ctor).ReferencesIn entries
  typeScope : (shape.ruleType source mode i ctor).Scope (mode.recUvars shape.universes) 0
  typeReferences : (shape.ruleType source mode i ctor).ReferencesIn entries
  type : ∃ l, TypingClaim.{u,v} entries [] (shape.ruleType source mode i ctor) (.sort l) ∧
    (mode = .small → ∀ levels, l.eval levels = 0)
  lhs : TypingClaim.{u,v} entries [] (shape.ruleLhs source mode i ctor) (shape.ruleType source mode i ctor)
  rhs : TypingClaim.{u,v} entries [] (shape.ruleRhs source mode i ctor) (shape.ruleType source mode i ctor)

def checkRule (fuel : Nat) (entries : Environment β) (shape : Shape β) (source : β)
    (mode : ElimMode) (i : Nat) (ctor : Constructor β) :
    Option (CheckedClaim.{u} (RuleFormation.{u,v} entries shape source mode i ctor)) :=
  if hs : (shape.ruleLhs source mode i ctor).Scope (mode.recUvars shape.universes) 0 ∧
      (shape.ruleRhs source mode i ctor).Scope (mode.recUvars shape.universes) 0 then
    if hr : (shape.ruleLhs source mode i ctor).ReferencesIn entries ∧
        (shape.ruleRhs source mode i ctor).ReferencesIn entries then do
      if hts : (shape.ruleType source mode i ctor).Scope (mode.recUvars shape.universes) 0 then
      if htr : (shape.ruleType source mode i ctor).ReferencesIn entries then
      let ⟨l, ht⟩ ← checkSort.{u,v} fuel entries [] (shape.ruleType source mode i ctor)
      if hsmall : mode = .small → levelIsZero l = true then
        let hl ← checkType.{u,v} fuel entries [] (shape.ruleLhs source mode i ctor)
          (shape.ruleType source mode i ctor)
        let hh ← checkType.{u,v} fuel entries [] (shape.ruleRhs source mode i ctor)
          (shape.ruleType source mode i ctor)
        return ⟨⟨hs, hr, hts, htr, ⟨l, ht, fun he levels => levelIsZero_sound (hsmall he) levels⟩, hl.down, hh.down⟩⟩
      else none
      else none
      else none
    else none
  else none

def checkRules (fuel : Nat) (entries : Environment β) (shape : Shape β) (source : β)
    (mode : ElimMode) : (ctors : List (Constructor β × Nat)) →
      Option (CheckedClaim.{u} (∀ ctor i, (ctor, i) ∈ ctors →
        RuleFormation.{u,v} entries shape source mode i ctor))
  | [] => some ⟨by simp⟩
  | (ctor, i) :: ctors => do
    let rule ← checkRule fuel entries shape source mode i ctor
    let rest ← checkRules fuel entries shape source mode ctors
    return ⟨by
      intro ctor' i' hc
      rcases List.mem_cons.mp hc with he | hc
      · cases he; exact rule.down
      · exact rest.down ctor' i' hc⟩

variable {V : Type v} [SetTheory V]

omit [DecidableEq β] in
theorem small_rule_eq {entries : Environment β} {shape : Shape β} {source : β}
    {i : Nat} {ctor : Constructor β}
    (h : RuleFormation.{u,v} entries shape source .small i ctor)
    (constants : Assignment β V) (hM : Realizes constants entries) (levels : List Nat) (env : Nat → V) :
    interp constants levels env (shape.ruleLhs source .small i ctor) =
      interp constants levels env (shape.ruleRhs source .small i ctor) := by
  obtain ⟨l, ht, hz⟩ := h.type
  have hΓ := Context.valid_nil constants levels env
  have hprop := (ht V constants hM levels env hΓ).2.2
  rw [interp, hz rfl levels, univ_zero] at hprop
  exact subsingleton_of_mem_univZero hprop (h.lhs V constants hM levels env hΓ).2.2
    (h.rhs V constants hM levels env hΓ).2.2

end Shape
end Ix.Kernel.Certified.Ordinary
