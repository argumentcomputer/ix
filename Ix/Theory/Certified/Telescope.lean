/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Checker
import Ix.Theory.Model.Inductive.Telescope

namespace Ix.Theory.Certified

open Model Model.SetTheory Model.SetTheory.Tower

universe u v
variable {β : Type u} [DecidableEq β]

structure DomainWitness (β : Type u) where
  level : VLevel
  typing : TypingWitness β

/-- A positive carrier bounds each field domain. Prop carriers may quantify
over larger domains; this does not by itself license large elimination. -/
def checkDomainBound (n : Nat) (bound : Option VLevel) (level : VLevel) : Bool :=
  match bound with
  | none => true
  | some w => LevelEq.check n w .zero || LevelEq.check n (.max level w) w

theorem checkDomainBound_sound {n : Nat} {bound : Option VLevel} {level : VLevel}
    (h : checkDomainBound n bound level = true) :
    ∀ w, bound = some w → ∀ levels,
      w.eval levels ≠ 0 → level.eval levels ≤ w.eval levels := by
  intro w hw levels hpos
  subst bound
  simp only [checkDomainBound, Bool.or_eq_true] at h
  rcases h with h | h
  · exact (hpos ((LevelEq.check_sound h).2.2 levels)).elim
  · have he := (LevelEq.check_sound h).2.2 levels
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

/-- A finite witness contains only proposed sorts and typing rule choices.
Every domain is checked in the context extended by its actual predecessors. -/
def verifyTelescope (fuel n : Nat) (entries : Environment β) (bound : Option VLevel) :
    (Γ : Context β) → (domains : List (AExpr β)) → List (DomainWitness β) →
      Option (CheckedClaim.{u} (Telescope.Formed.{u,v} entries Γ domains ∧
        TelescopeBound.{u,v} entries Γ domains bound))
  | Γ, [], [] => some ⟨⟨.nil, TelescopeBound.nil entries Γ bound⟩⟩
  | Γ, A :: rest, witness :: witnesses =>
    if hl : checkDomainBound n bound witness.level = true then do
      let hA ← verifyType.{u,v} fuel n entries Γ A (.sort witness.level) witness.typing
      let hrest ← verifyTelescope fuel n entries bound (Γ.push A) rest witnesses
      return ⟨⟨.cons witness.level hA.down hrest.down.1,
        TelescopeBound.cons hA.down (checkDomainBound_sound hl) hrest.down.2⟩⟩
    else none
  | _, _, _ => none

theorem verifyTelescope_sound {fuel n : Nat} {entries : Environment β} {bound : Option VLevel}
    {Γ : Context β} {domains : List (AExpr β)} {witnesses : List (DomainWitness β)}
    {result} (_ : verifyTelescope.{u,v} fuel n entries bound Γ domains witnesses = some result) :
    Telescope.Formed.{u,v} entries Γ domains ∧ TelescopeBound.{u,v} entries Γ domains bound :=
  result.down

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

def verifyArguments (fuel n : Nat) (entries : Environment β) (Γ : Context β) :
    (domains args : List (AExpr β)) → List (TypingWitness β) →
      Option (CheckedClaim.{u} (ArgumentsFit.{u,v} entries Γ domains args))
  | [], [], [] => some ⟨ArgumentsFit.nil entries Γ⟩
  | A :: domains, a :: args, witness :: witnesses => do
      let ha ← verifyType.{u,v} fuel n entries Γ a A witness
      let hrest ← verifyArguments fuel n entries Γ (Telescope.inst a domains) args witnesses
      return ⟨ArgumentsFit.cons ha.down hrest.down⟩
  | _, _, _ => none

theorem verifyArguments_sound {fuel n : Nat} {entries : Environment β} {Γ : Context β}
    {domains args : List (AExpr β)} {witnesses : List (TypingWitness β)}
    {result} (_ : verifyArguments.{u,v} fuel n entries Γ domains args witnesses = some result) :
    ArgumentsFit.{u,v} entries Γ domains args := result.down

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
def verifyPropTelescope (fuel n : Nat) (entries : Environment β) (atLevel : VLevel) :
    (Γ : Context β) → (domains : List (AExpr β)) → List (DomainWitness β) →
      Option (CheckedClaim.{u} (TelescopeProp.{u,v} entries Γ domains atLevel))
  | Γ, [], [] => some ⟨TelescopeProp.nil entries Γ atLevel⟩
  | Γ, A :: rest, witness :: witnesses =>
    if hl : checkZeroImplies atLevel witness.level = true then do
      let hA ← verifyType.{u,v} fuel n entries Γ A (.sort witness.level) witness.typing
      let htail ← verifyPropTelescope fuel n entries atLevel (Γ.push A) rest witnesses
      return ⟨TelescopeProp.cons hA.down (checkZeroImplies_sound hl) htail.down⟩
    else none
  | _, _, _ => none

end Ix.Theory.Certified
