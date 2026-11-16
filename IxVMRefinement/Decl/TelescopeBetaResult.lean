import IxVMRefinement.Decl.SortBetaConversion
import IxVMRefinement.Decl.TelescopeConversionPins
import IxC.Kernel.Verify.Inductives.StructBody

/-! # Actual telescope comparison with a constant-sort motive result

The left telescope ends in an inferred sort. The right may end in that motive applied to
an arbitrary constructor expression. Opening either telescope preserves the motive's literal
sort body, so the existing oriented body comparisons determine the same universe level.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- Actual dependent telescope conversion determines the level of a constant-sort beta result. -/
theorem converted_telescope_beta_levels {md : Mode} {env : Env md}
    {count depth : Nat} {left right result : Expr md} {leftBinders rightBinders : List (Expr md × BinderMeta)}
    {leftSort rightSort : Level}
    (converted : Rules.DefEq env depth left right)
    (leftStrip : left.stripPis count = some (leftBinders, .sort leftSort))
    (rightStrip : right.stripPis count = some (rightBinders, result))
    (resultShape : SortBeta rightSort result) : ∀ φ, leftSort.eval φ = rightSort.eval φ := by
  induction count generalizing depth left right result leftBinders rightBinders with
  | zero =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj leftStrip)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj rightStrip)
    exact sort_beta_levels converted resultShape
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
        · obtain ⟨_, openedLeft, _⟩ := stripPis_instantiate1_full (v := .fvar depth leftDomain) count 0 leftTailStrip
          obtain ⟨_, openedRight, _⟩ := stripPis_instantiate1_full (v := .fvar depth leftDomain) count 0 rightTailStrip
          simp only [Expr.instantiate1] at openedLeft
          exact ih bodyLeft openedLeft openedRight (resultShape.instantiate1 _ _)
        · obtain ⟨_, openedLeft, _⟩ := stripPis_instantiate1_full (v := .fvar depth rightDomain) count 0 leftTailStrip
          obtain ⟨_, openedRight, _⟩ := stripPis_instantiate1_full (v := .fvar depth rightDomain) count 0 rightTailStrip
          simp only [Expr.instantiate1] at openedLeft
          exact ih bodyRight openedLeft openedRight (resultShape.instantiate1 _ _)
      | _ => cases rightStrip
    | _ => cases leftStrip

/-- The same actual comparison fixes its result's canonical zero-ness. -/
theorem converted_telescope_beta_zero {md : Mode} {env : Env md}
    {count depth : Nat} {left right result : Expr md} {leftBinders rightBinders : List (Expr md × BinderMeta)}
    {leftSort rightSort : Level}
    (converted : Rules.DefEq env depth left right)
    (leftStrip : left.stripPis count = some (leftBinders, .sort leftSort))
    (rightStrip : right.stripPis count = some (rightBinders, result))
    (resultShape : SortBeta rightSort result) : Level.zeronessOf leftSort = Level.zeronessOf rightSort := by
  apply PropWhen.eq_of_holds
  intro φ
  rw [PropWhen.zeronessOf_sound, PropWhen.zeronessOf_sound,
    converted_telescope_beta_levels converted leftStrip rightStrip resultShape φ]

end IxVM.Refinement.Decl
