/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Telescope.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the witness validators `verifyTelescope`, `verifyArguments`, and
`verifyPropTelescope` are replaced by `checkTelescope`, `checkArguments`, and
`checkPropTelescope`, which infer sorts and types with `Ix.Kernel.Infer`; the
universe-count parameter and the witness structures are gone; level
comparison uses `Ix.Kernel.Level`.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Checker
import Ix.Kernel.Model.Inductive.Telescope

namespace Ix.Kernel.Certified

open Model Model.SetTheory Model.SetTheory.Tower

universe u v
variable {β : Type u} [DecidableEq β]

/-- A positive carrier bounds each field domain. Prop carriers may quantify
over larger domains; this does not by itself license large elimination. -/
def checkDomainBound (bound : Option VLevel) (level : VLevel) : Bool :=
  match bound with
  | none => true
  | some w => levelIsZero w || levelEquiv (.max level w) w

theorem checkDomainBound_sound {bound : Option VLevel} {level : VLevel}
    (h : checkDomainBound bound level = true) :
    ∀ w, bound = some w → ∀ levels,
      w.eval levels ≠ 0 → level.eval levels ≤ w.eval levels := by
  intro w hw levels hpos
  subst bound
  simp only [checkDomainBound, Bool.or_eq_true] at h
  rcases h with h | h
  · exact (hpos (levelIsZero_sound h levels)).elim
  · have he := levelEquiv_sound h levels
    change max (level.eval levels) (w.eval levels) = w.eval levels at he
    exact he ▸ Nat.le_max_left _ _

/-- Bounds are consequences of checked field sorts, uniformly over every
compatible model and satisfying prefix. -/
def TelescopeBound (entries : Environment β) (Γ : Context β) (domains : List (AExpr β))
    (bound : Option VLevel) : Prop :=
  ∀ w, bound = some w → ∀ (V : Type v) [SetTheory V] (constants : Assignment β V),
    Realizes constants entries → ∀ levels env, Γ.Valid constants levels env →
    w.eval levels ≠ 0 → BoundS (w.eval levels) (Telescope.interpret constants levels env domains)

omit [DecidableEq β] in
theorem TelescopeBound.nil (entries : Environment β) (Γ : Context β) (bound : Option VLevel) :
    TelescopeBound.{u,v} entries Γ [] bound := fun _ _ _ _ _ _ _ _ _ _ => trivial

omit [DecidableEq β] in
theorem TelescopeBound.cons {entries : Environment β} {Γ : Context β}
    {A : AExpr β} {rest : List (AExpr β)} {bound : Option VLevel} {l : VLevel}
    (hA : TypingClaim.{u,v} entries Γ A (.sort l))
    (hl : ∀ w, bound = some w → ∀ levels, w.eval levels ≠ 0 → l.eval levels ≤ w.eval levels)
    (hrest : TelescopeBound.{u,v} entries (Γ.push A) rest bound) :
    TelescopeBound.{u,v} entries Γ (A :: rest) bound := by
  intro w hw V _ constants hM levels env hΓ hpos
  have htype := hA V constants hM levels env hΓ
  refine ⟨univ_mono (hl w hw levels hpos) _ htype.2.2, ?_⟩
  intro x hx
  exact hrest w hw V constants hM levels (Valuation.cons x env) (hΓ.push htype.1 hx) hpos

/-- Every domain is checked in the context extended by its actual
predecessors; its sort is inferred, not supplied. -/
def checkTelescope (fuel : Nat) (entries : Environment β) (bound : Option VLevel) :
    (Γ : Context β) → (domains : List (AExpr β)) →
      Option (CheckedClaim.{u} (Telescope.Formed.{u,v} entries Γ domains ∧
        TelescopeBound.{u,v} entries Γ domains bound))
  | Γ, [] => some ⟨⟨.nil, TelescopeBound.nil entries Γ bound⟩⟩
  | Γ, A :: rest => do
    let ⟨l, hA⟩ ← checkSort.{u,v} fuel entries Γ A
    if hl : checkDomainBound bound l = true then
      let hrest ← checkTelescope fuel entries bound (Γ.push A) rest
      return ⟨⟨.cons l hA hrest.down.1, TelescopeBound.cons hA (checkDomainBound_sound hl) hrest.down.2⟩⟩
    else none

/-- Indices are checked against their actual dependent telescope, with every
earlier argument substituted before the next check. -/
def ArgumentsFit (entries : Environment β) (Γ : Context β)
    (domains args : List (AExpr β)) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V), Realizes constants entries →
    ∀ levels env, Γ.Valid constants levels env →
      FitsS (Telescope.interpret constants levels env domains) (args.map (interp constants levels env))

omit [DecidableEq β] in
theorem ArgumentsFit.nil (entries : Environment β) (Γ : Context β) :
    ArgumentsFit.{u,v} entries Γ [] [] := fun _ _ _ _ _ _ _ => trivial

omit [DecidableEq β] in
theorem ArgumentsFit.cons {entries : Environment β} {Γ : Context β}
    {A a : AExpr β} {domains args : List (AExpr β)}
    (ha : TypingClaim.{u,v} entries Γ a A)
    (hrest : ArgumentsFit.{u,v} entries Γ (Telescope.inst a domains) args) :
    ArgumentsFit.{u,v} entries Γ (A :: domains) (a :: args) := by
  intro V _ constants hM levels env hΓ
  refine ⟨(ha V constants hM levels env hΓ).2.2, ?_⟩
  have h := (Telescope.fits_inst constants levels env a domains 0 _).mp
    (hrest V constants hM levels env hΓ)
  simpa only [Valuation.skip_zero, Valuation.insert_zero] using h

def checkArguments (fuel : Nat) (entries : Environment β) (Γ : Context β) :
    (domains args : List (AExpr β)) →
      Option (CheckedClaim.{u} (ArgumentsFit.{u,v} entries Γ domains args))
  | [], [] => some ⟨ArgumentsFit.nil entries Γ⟩
  | A :: domains, a :: args => do
      let ha ← checkType.{u,v} fuel entries Γ a A
      let hrest ← checkArguments fuel entries Γ (Telescope.inst a domains) args
      return ⟨ArgumentsFit.cons ha.down hrest.down⟩
  | _, _ => none

def checkZeroImplies (a b : VLevel) : Bool :=
  decide ((zeroCondition a).inter (zeroCondition b) = zeroCondition a)

theorem checkZeroImplies_sound {a b : VLevel} (h : checkZeroImplies a b = true)
    (levels : List Nat) (ha : a.eval levels = 0) : b.eval levels = 0 := by
  have he : (zeroCondition a).inter (zeroCondition b) = zeroCondition a := of_decide_eq_true h
  have hv := congrArg (PropWhen.holds (levels.getD · 0)) he
  simpa only [PropWhen.holds_inter, zeroCondition_correct, ha, beq_self_eq_true,
    Bool.true_and, beq_iff_eq] using hv

def TelescopeProp (entries : Environment β) (Γ : Context β) (domains : List (AExpr β))
    (atLevel : VLevel) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V), Realizes constants entries →
    ∀ levels env, Γ.Valid constants levels env → atLevel.eval levels = 0 →
      PropS (Telescope.interpret constants levels env domains)

omit [DecidableEq β] in
theorem TelescopeProp.nil (entries : Environment β) (Γ : Context β) (atLevel : VLevel) :
    TelescopeProp.{u,v} entries Γ [] atLevel := fun _ _ _ _ _ _ _ _ => trivial

omit [DecidableEq β] in
theorem TelescopeProp.cons {entries : Environment β} {Γ : Context β}
    {A : AExpr β} {rest : List (AExpr β)} {atLevel l : VLevel}
    (hA : TypingClaim.{u,v} entries Γ A (.sort l))
    (hl : ∀ levels, atLevel.eval levels = 0 → l.eval levels = 0)
    (htail : TelescopeProp.{u,v} entries (Γ.push A) rest atLevel) :
    TelescopeProp.{u,v} entries Γ (A :: rest) atLevel := by
  intro V _ constants hM levels env hΓ hz
  have htype := hA V constants hM levels env hΓ
  refine ⟨?_, fun x hx => htail V constants hM levels _ (hΓ.push htype.1 hx) hz⟩
  simpa only [interp, hl levels hz, univ_zero] using htype.2.2

/-- The singleton exception checks proof-valued ordinary fields. Merely
having one constructor is insufficient for large elimination from Prop. -/
def checkPropTelescope (fuel : Nat) (entries : Environment β) (atLevel : VLevel) :
    (Γ : Context β) → (domains : List (AExpr β)) →
      Option (CheckedClaim.{u} (TelescopeProp.{u,v} entries Γ domains atLevel))
  | Γ, [] => some ⟨TelescopeProp.nil entries Γ atLevel⟩
  | Γ, A :: rest => do
    let ⟨l, hA⟩ ← checkSort.{u,v} fuel entries Γ A
    if hl : checkZeroImplies atLevel l = true then
      let htail ← checkPropTelescope fuel entries atLevel (Γ.push A) rest
      return ⟨TelescopeProp.cons hA (checkZeroImplies_sound hl) htail.down⟩
    else none

end Ix.Kernel.Certified
