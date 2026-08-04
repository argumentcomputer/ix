import Ix.Tc.Verify.Check.DefEqLazyDeltaPolicy

/-!
# Operational policy for the DefEq comparison pipeline

This module composes the proved primitive, normalization, proposition, and
lazy-delta policies across the exact production `isDefEqInner` tier order.
It stops at the cache/depth shell owned by `isDefEq` itself.
-/

namespace Ix.Tc

namespace RecM

theorem isDefEqInnerAfterNoDeltaPass_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqInnerAfterNoDeltaPass left right).run
      methods).PreservesInferOnly := by
  unfold isDefEqInnerAfterNoDeltaPass
  refine bind_preservesInferOnly
    (tryProofIrrel_preservesInferOnly hmethods hwhnf left right) ?_
  intro proofIrrelevant
  cases proofIrrelevant with
  | true => exact TcM.PreservesInferOnly.pure true
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      exact isDefEqInnerAfterProofIrrelevance_preservesInferOnly hmethods
        hwhnf hcore hnoDelta hcheapNoDelta left right

theorem isDefEqInnerAfterCorePass_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqInnerAfterCorePass left right).run
      methods).PreservesInferOnly := by
  unfold isDefEqInnerAfterCorePass
  refine bind_preservesInferOnly (hcheapNoDelta left) ?_
  intro normalizedLeft
  refine bind_preservesInferOnly (hcheapNoDelta right) ?_
  intro normalizedRight
  by_cases haddress : normalizedLeft.addr == normalizedRight.addr
  · simp only [haddress, if_true]
    exact TcM.PreservesInferOnly.pure true
  · simp only [haddress, Bool.false_eq_true, if_false, pure_bind]
    refine bind_preservesInferOnly
      (quickDefEq_preservesInferOnly hmethods normalizedLeft normalizedRight) ?_
    intro quick
    cases quick with
    | true => exact TcM.PreservesInferOnly.pure true
    | false =>
        simp only [Bool.false_eq_true, if_false]
        exact isDefEqInnerAfterNoDeltaPass_preservesInferOnly hmethods hwhnf
          hcore hnoDelta hcheapNoDelta normalizedLeft normalizedRight

theorem isDefEqInnerAfterStringExpansion_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (hcheapCore : ∀ source,
      ((whnfCoreForDefEq source).run methods).PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqInnerAfterStringExpansion left right).run
      methods).PreservesInferOnly := by
  unfold isDefEqInnerAfterStringExpansion
  refine bind_preservesInferOnly (hcheapCore left) ?_
  intro coreLeft
  refine bind_preservesInferOnly (hcheapCore right) ?_
  intro coreRight
  by_cases haddress : coreLeft.addr == coreRight.addr
  · simp only [haddress, if_true]
    exact TcM.PreservesInferOnly.pure true
  · simp only [haddress, Bool.false_eq_true, if_false, pure_bind]
    refine bind_preservesInferOnly
      (quickDefEq_preservesInferOnly hmethods coreLeft coreRight) ?_
    intro quick
    cases quick with
    | true => exact TcM.PreservesInferOnly.pure true
    | false =>
        simp only [Bool.false_eq_true, if_false]
        exact isDefEqInnerAfterCorePass_preservesInferOnly hmethods hwhnf
          hcore hnoDelta hcheapNoDelta left right

theorem isDefEqInnerAfterBoolTrue_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (hcheapCore : ∀ source,
      ((whnfCoreForDefEq source).run methods).PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqInnerAfterBoolTrue left right).run
      methods).PreservesInferOnly := by
  unfold isDefEqInnerAfterBoolTrue
  by_cases hstring : hasStringLiteralPair left right
  · simp only [hstring, if_true]
    refine bind_preservesInferOnly
      (tryStringLitExpansion_preservesInferOnly hmethods left right) ?_
    intro forward
    cases forward with
    | true => exact TcM.PreservesInferOnly.pure true
    | false =>
        simp only [Bool.false_eq_true, if_false, pure_bind]
        refine bind_preservesInferOnly
          (tryStringLitExpansion_preservesInferOnly hmethods right left) ?_
        intro backward
        cases backward with
        | true => exact TcM.PreservesInferOnly.pure true
        | false =>
            simp only [Bool.false_eq_true, if_false]
            exact isDefEqInnerAfterStringExpansion_preservesInferOnly
              hmethods hwhnf hcore hnoDelta hcheapCore hcheapNoDelta left right
  · simp only [hstring, Bool.false_eq_true, if_false]
    exact isDefEqInnerAfterStringExpansion_preservesInferOnly hmethods hwhnf
      hcore hnoDelta hcheapCore hcheapNoDelta left right

theorem isDefEqInnerAfterFirstBoolGuardMiss_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (hcheapCore : ∀ source,
      ((whnfCoreForDefEq source).run methods).PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqInnerAfterFirstBoolGuardMiss left right).run
      methods).PreservesInferOnly := by
  unfold isDefEqInnerAfterFirstBoolGuardMiss
  refine bind_preservesInferOnly (isBoolTrue_preservesInferOnly left) ?_
  intro leftIsTrue
  refine bind_preservesInferOnly
    (boolTrueReductionAllowed_preservesInferOnly right) ?_
  intro rightAllowed
  by_cases hguard : leftIsTrue && rightAllowed
  · simp only [hguard, if_true]
    refine bind_preservesInferOnly
      (whnfIsBoolTrue_preservesInferOnly hwhnf right) ?_
    intro normalizedTrue
    cases normalizedTrue with
    | true => exact TcM.PreservesInferOnly.pure true
    | false =>
        simp only [Bool.false_eq_true, if_false, pure_bind]
        exact isDefEqInnerAfterBoolTrue_preservesInferOnly hmethods hwhnf
          hcore hnoDelta hcheapCore hcheapNoDelta left right
  · simp only [hguard, Bool.false_eq_true, if_false]
    exact isDefEqInnerAfterBoolTrue_preservesInferOnly hmethods hwhnf hcore
      hnoDelta hcheapCore hcheapNoDelta left right

theorem isDefEqInnerAfterQuick_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (hcheapCore : ∀ source,
      ((whnfCoreForDefEq source).run methods).PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqInnerAfterQuick left right).run
      methods).PreservesInferOnly := by
  unfold isDefEqInnerAfterQuick
  refine bind_preservesInferOnly (isBoolTrue_preservesInferOnly right) ?_
  intro rightIsTrue
  refine bind_preservesInferOnly
    (boolTrueReductionAllowed_preservesInferOnly left) ?_
  intro leftAllowed
  by_cases hguard : rightIsTrue && leftAllowed
  · simp only [hguard, if_true]
    refine bind_preservesInferOnly
      (whnfIsBoolTrue_preservesInferOnly hwhnf left) ?_
    intro normalizedTrue
    cases normalizedTrue with
    | true => exact TcM.PreservesInferOnly.pure true
    | false =>
        simp only [Bool.false_eq_true, if_false, pure_bind]
        exact isDefEqInnerAfterBoolTrue_preservesInferOnly hmethods hwhnf
          hcore hnoDelta hcheapCore hcheapNoDelta left right
  · simp only [hguard, Bool.false_eq_true, if_false]
    exact isDefEqInnerAfterFirstBoolGuardMiss_preservesInferOnly hmethods
      hwhnf hcore hnoDelta hcheapCore hcheapNoDelta left right

theorem isDefEqInner_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (hcheapCore : ∀ source,
      ((whnfCoreForDefEq source).run methods).PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqInner left right).run methods).PreservesInferOnly := by
  unfold isDefEqInner
  refine bind_preservesInferOnly
    (quickDefEq_preservesInferOnly hmethods left right) ?_
  intro quick
  cases quick with
  | true => exact TcM.PreservesInferOnly.pure true
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      exact isDefEqInnerAfterQuick_preservesInferOnly hmethods hwhnf hcore
        hnoDelta hcheapCore hcheapNoDelta left right

end RecM

end Ix.Tc
