import IxVMRefinement.Decl.TelescopeConversionPins
import IxVMRefinement.Decl.NativeWrapperCoherence
import IxC.Kernel.Verify.Inductives.StructBody

/-! # Result sorts of actual telescope conversions

A conversion between two product telescopes ending in sorts retains a conversion between
those exact result sorts. Each step uses the derivation's original opener; closing/opening
cannot change a sort. No independent conversion chain is composed.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

universe u

private theorem strip_sort_open {md : Mode} {count : Nat} {e value : Expr md}
    {binders : List (Expr md × BinderMeta)} {sortLevel : Level}
    (stripped : e.stripPis count = some (binders, .sort sortLevel)) :
    ∃ openedBinders, (e.instantiate1 value).stripPis count = some (openedBinders, .sort sortLevel) := by
  obtain ⟨openedBinders, opened, _⟩ := stripPis_instantiate1_full (v := value) count 0 stripped
  exact ⟨openedBinders, by simpa only [Expr.instantiate1] using opened⟩

/-- The residual conversion of two checked telescope shapes is an actual rules derivation. -/
theorem converted_telescope_result_sort {md : Mode} {env : Env md}
    {count depth : Nat} {left right : Expr md} {leftBinders rightBinders : List (Expr md × BinderMeta)}
    {leftSort rightSort : Level}
    (converted : Rules.DefEq env depth left right)
    (leftStrip : left.stripPis count = some (leftBinders, .sort leftSort))
    (rightStrip : right.stripPis count = some (rightBinders, .sort rightSort)) :
    Rules.DefEq env (depth + count) (.sort leftSort) (.sort rightSort) := by
  induction count generalizing depth left right leftBinders rightBinders with
  | zero =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj leftStrip)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj rightStrip)
    simpa only [Nat.add_zero] using converted
  | succ count ih =>
    cases left with
    | forallE leftDomain leftBody leftMeta =>
      cases right with
      | forallE rightDomain rightBody rightMeta =>
        simp only [Expr.stripPis, Option.map_eq_some_iff] at leftStrip rightStrip
        obtain ⟨⟨leftTail, leftResidual⟩, leftTailStrip, leftEq⟩ := leftStrip
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj leftEq
        obtain ⟨⟨rightTail, rightResidual⟩, rightTailStrip, rightEq⟩ := rightStrip
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj rightEq
        obtain ⟨_, _, bodyLeft | bodyRight⟩ := forall_conversion_components converted
        · obtain ⟨_, openedLeft⟩ := strip_sort_open (value := .fvar depth leftDomain) leftTailStrip
          obtain ⟨_, openedRight⟩ := strip_sort_open (value := .fvar depth leftDomain) rightTailStrip
          simpa only [Nat.add_succ, Nat.succ_add] using ih bodyLeft openedLeft openedRight
        · obtain ⟨_, openedLeft⟩ := strip_sort_open (value := .fvar depth rightDomain) leftTailStrip
          obtain ⟨_, openedRight⟩ := strip_sort_open (value := .fvar depth rightDomain) rightTailStrip
          simpa only [Nat.add_succ, Nat.succ_add] using ih bodyRight openedLeft openedRight
      | _ => cases rightStrip
    | _ => cases leftStrip

/-- Actual telescope comparison fixes the canonical zero-ness of its result sort. -/
theorem converted_telescope_result_zero {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {count depth : Nat} {left right : Expr md}
    {leftBinders rightBinders : List (Expr md × BinderMeta)} {leftSort rightSort : Level}
    (converted : Rules.DefEq env depth left right)
    (leftStrip : left.stripPis count = some (leftBinders, .sort leftSort))
    (rightStrip : right.stripPis count = some (rightBinders, .sort rightSort)) :
    Level.zeronessOf leftSort = Level.zeronessOf rightSort := by
  have residual := converted_telescope_result_sort converted leftStrip rightStrip
  apply PropWhen.eq_of_holds
  intro φ
  rw [PropWhen.zeronessOf_sound, PropWhen.zeronessOf_sound, converted_sort_levels_at model residual φ]

end IxVM.Refinement.Decl
