import Ix.Tc.Verify.Check.DefEqProjectionDeltaPolicy

/-!
# Operational policy for the main DefEq lazy-delta loop

This module covers the production Tier-4 bounded loop: Nat-offset and
primitive accelerators, delta classification and ranking, same-head cache
probes, one- and two-sided unfolding, projection-app probes, and the stopped
continuation into final WHNF comparison.
-/

namespace Ix.Tc

namespace RecM

theorem tryReduceNat_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (source : KExpr .anon) :
    ((tryReduceNat source).run methods).PreservesInferOnly := by
  unfold tryReduceNat
  exact tryReduceNatWithSuccMode_preservesInferOnly hmethods source .collapse

theorem finishDefEqLazyDeltaStep_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((finishDefEqLazyDeltaStep left right).run
      methods).PreservesInferOnly := by
  unfold finishDefEqLazyDeltaStep
  by_cases haddress : left.addr == right.addr
  · simp only [haddress, if_true]
    exact TcM.PreservesInferOnly.pure
      (BoundedStep.done (LazyDeltaLoopResult.answer true))
  · simp only [haddress, Bool.false_eq_true, if_false, pure_bind]
    refine bind_preservesInferOnly
      (quickDefEq_preservesInferOnly hmethods left right) ?_
    intro equal
    cases equal with
    | true =>
        exact TcM.PreservesInferOnly.pure
          (BoundedStep.done (LazyDeltaLoopResult.answer true))
    | false =>
        exact TcM.PreservesInferOnly.pure (BoundedStep.next (left, right))

theorem defEqLazyDeltaStepAfterSameHeadMiss_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((defEqLazyDeltaStepAfterSameHeadMiss left right).run
      methods).PreservesInferOnly := by
  unfold defEqLazyDeltaStepAfterSameHeadMiss
  refine bind_preservesInferOnly
    (deltaUnfoldOne_preservesInferOnly left) ?_
  intro leftUnfolded
  refine bind_preservesInferOnly
    (deltaUnfoldOne_preservesInferOnly right) ?_
  intro rightUnfolded
  cases leftUnfolded with
  | none =>
      cases rightUnfolded with
      | none =>
          exact TcM.PreservesInferOnly.pure
            (BoundedStep.done (LazyDeltaLoopResult.stopped left right))
      | some rightBody =>
          refine bind_preservesInferOnly (hcheapNoDelta rightBody) ?_
          intro rightReduced
          exact finishDefEqLazyDeltaStep_preservesInferOnly hmethods left
            rightReduced
  | some leftBody =>
      cases rightUnfolded with
      | none =>
          refine bind_preservesInferOnly (hcheapNoDelta leftBody) ?_
          intro leftReduced
          exact finishDefEqLazyDeltaStep_preservesInferOnly hmethods
            leftReduced right
      | some rightBody =>
          refine bind_preservesInferOnly (hcheapNoDelta leftBody) ?_
          intro leftReduced
          refine bind_preservesInferOnly (hcheapNoDelta rightBody) ?_
          intro rightReduced
          exact finishDefEqLazyDeltaStep_preservesInferOnly hmethods
            leftReduced rightReduced

theorem defEqLazyDeltaStepWithLeftDelta_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((defEqLazyDeltaStepWithLeftDelta left right).run
      methods).PreservesInferOnly := by
  unfold defEqLazyDeltaStepWithLeftDelta
  refine bind_preservesInferOnly
    (deltaUnfoldOne_preservesInferOnly left) ?_
  intro result
  cases result with
  | none =>
      exact TcM.PreservesInferOnly.pure
        (BoundedStep.done (LazyDeltaLoopResult.stopped left right))
  | some unfolded =>
      refine bind_preservesInferOnly (hcheapNoDelta unfolded) ?_
      intro reduced
      exact finishDefEqLazyDeltaStep_preservesInferOnly hmethods reduced right

theorem defEqLazyDeltaStepWithRightDelta_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((defEqLazyDeltaStepWithRightDelta left right).run
      methods).PreservesInferOnly := by
  unfold defEqLazyDeltaStepWithRightDelta
  refine bind_preservesInferOnly
    (deltaUnfoldOne_preservesInferOnly right) ?_
  intro result
  cases result with
  | none =>
      exact TcM.PreservesInferOnly.pure
        (BoundedStep.done (LazyDeltaLoopResult.stopped left right))
  | some unfolded =>
      refine bind_preservesInferOnly (hcheapNoDelta unfolded) ?_
      intro reduced
      exact finishDefEqLazyDeltaStep_preservesInferOnly hmethods left reduced

theorem defEqLazyDeltaStepWithEqualRank_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon)
    (leftHead rightHead : Option (KId .anon)) :
    ((defEqLazyDeltaStepWithEqualRank left right leftHead rightHead).run
      methods).PreservesInferOnly := by
  unfold defEqLazyDeltaStepWithEqualRank
  cases leftHead with
  | none =>
      exact defEqLazyDeltaStepAfterSameHeadMiss_preservesInferOnly hmethods
        hcheapNoDelta left right
  | some leftId =>
      cases rightHead with
      | none =>
          exact defEqLazyDeltaStepAfterSameHeadMiss_preservesInferOnly hmethods
            hcheapNoDelta left right
      | some rightId =>
          refine bind_preservesInferOnly
            (isRegular_preservesInferOnly leftId) ?_
          intro regular
          by_cases hguard : leftId.addr == rightId.addr && regular
          · simp only [hguard, if_true]
            refine bind_preservesInferOnly
              (trySameHeadSpineCached_preservesInferOnly hmethods left right) ?_
            intro result
            cases result with
            | some answer =>
                exact TcM.PreservesInferOnly.pure
                  (BoundedStep.done (LazyDeltaLoopResult.answer answer))
            | none =>
                exact
                  defEqLazyDeltaStepAfterSameHeadMiss_preservesInferOnly
                    hmethods hcheapNoDelta left right
          · simp only [hguard, Bool.false_eq_true, if_false, pure_bind]
            exact defEqLazyDeltaStepAfterSameHeadMiss_preservesInferOnly
              hmethods hcheapNoDelta left right

theorem defEqLazyDeltaStepAfterProjectionMiss_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon)
    (leftHead rightHead : Option (KId .anon))
    (leftDelta rightDelta : Bool) :
    ((defEqLazyDeltaStepAfterProjectionMiss left right leftHead rightHead
      leftDelta rightDelta).run methods).PreservesInferOnly := by
  unfold defEqLazyDeltaStepAfterProjectionMiss
  by_cases hboth : leftDelta && rightDelta
  · simp only [hboth, if_true]
    refine bind_preservesInferOnly
      (rankDeltaHead_preservesInferOnly leftHead) ?_
    intro leftRank
    refine bind_preservesInferOnly
      (rankDeltaHead_preservesInferOnly rightHead) ?_
    intro rightRank
    by_cases hequal : leftRank == rightRank
    · simp only [hequal, if_true]
      exact defEqLazyDeltaStepWithEqualRank_preservesInferOnly hmethods
        hcheapNoDelta left right leftHead rightHead
    · simp only [hequal, Bool.false_eq_true, if_false]
      split
      · exact defEqLazyDeltaStepWithLeftDelta_preservesInferOnly hmethods
          hcheapNoDelta left right
      · exact defEqLazyDeltaStepWithRightDelta_preservesInferOnly hmethods
          hcheapNoDelta left right
  · simp only [hboth, Bool.false_eq_true, if_false]
    by_cases hleft : leftDelta
    · simp only [hleft, if_true]
      exact defEqLazyDeltaStepWithLeftDelta_preservesInferOnly hmethods
        hcheapNoDelta left right
    · simp only [hleft, Bool.false_eq_true, if_false]
      exact defEqLazyDeltaStepWithRightDelta_preservesInferOnly hmethods
        hcheapNoDelta left right

theorem defEqLazyDeltaStepAfterDeltaClassification_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon)
    (leftHead rightHead : Option (KId .anon))
    (leftDelta rightDelta : Bool) :
    ((defEqLazyDeltaStepAfterDeltaClassification left right leftHead rightHead
      leftDelta rightDelta).run methods).PreservesInferOnly := by
  unfold defEqLazyDeltaStepAfterDeltaClassification
  by_cases hleftOnly : leftDelta && !rightDelta
  · simp only [hleftOnly, if_true]
    refine bind_preservesInferOnly
      (tryUnfoldProjApp_preservesInferOnly hnoDelta right) ?_
    intro result
    cases result with
    | some reduced =>
        exact TcM.PreservesInferOnly.pure
          (BoundedStep.next (left, reduced))
    | none =>
        exact defEqLazyDeltaStepAfterProjectionMiss_preservesInferOnly hmethods
          hcheapNoDelta left right leftHead rightHead leftDelta rightDelta
  · simp only [hleftOnly, Bool.false_eq_true, if_false]
    by_cases hrightOnly : rightDelta && !leftDelta
    · simp only [hrightOnly, if_true]
      refine bind_preservesInferOnly
        (tryUnfoldProjApp_preservesInferOnly hnoDelta left) ?_
      intro result
      cases result with
      | some reduced =>
          exact TcM.PreservesInferOnly.pure
            (BoundedStep.next (reduced, right))
      | none =>
          exact
            defEqLazyDeltaStepAfterProjectionMiss_preservesInferOnly hmethods
              hcheapNoDelta left right leftHead rightHead leftDelta rightDelta
    · simp only [hrightOnly, Bool.false_eq_true, if_false, pure_bind]
      exact defEqLazyDeltaStepAfterProjectionMiss_preservesInferOnly hmethods
        hcheapNoDelta left right leftHead rightHead leftDelta rightDelta

theorem defEqLazyDeltaStepAfterAcceleratorMiss_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((defEqLazyDeltaStepAfterAcceleratorMiss left right).run
      methods).PreservesInferOnly := by
  unfold defEqLazyDeltaStepAfterAcceleratorMiss
  refine bind_preservesInferOnly
    (classifyDeltaHead_preservesInferOnly left) ?_
  intro leftDelta
  refine bind_preservesInferOnly
    (classifyDeltaHead_preservesInferOnly right) ?_
  intro rightDelta
  by_cases hnone : !leftDelta && !rightDelta
  · simp only [hnone, if_true]
    exact TcM.PreservesInferOnly.pure
      (BoundedStep.done (LazyDeltaLoopResult.stopped left right))
  · simp only [hnone, Bool.false_eq_true, if_false, pure_bind]
    exact defEqLazyDeltaStepAfterDeltaClassification_preservesInferOnly
      hmethods hnoDelta hcheapNoDelta left right (headConstId left)
      (headConstId right) leftDelta rightDelta

theorem defEqLazyDeltaStepAfterNatMiss_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((defEqLazyDeltaStepAfterNatMiss left right).run
      methods).PreservesInferOnly := by
  unfold defEqLazyDeltaStepAfterNatMiss
  refine bind_preservesInferOnly
    (tryReduceNative_preservesInferOnly hmethods left) ?_
  intro leftNative
  cases leftNative with
  | some reduced =>
      refine bind_preservesInferOnly
        (isDefEqCall_preservesInferOnly hmethods reduced right) ?_
      intro answer
      exact TcM.PreservesInferOnly.pure
        (BoundedStep.done (LazyDeltaLoopResult.answer answer))
  | none =>
      simp only [pure_bind]
      refine bind_preservesInferOnly
        (tryReduceNative_preservesInferOnly hmethods right) ?_
      intro rightNative
      cases rightNative with
      | some reduced =>
          refine bind_preservesInferOnly
            (isDefEqCall_preservesInferOnly hmethods left reduced) ?_
          intro answer
          exact TcM.PreservesInferOnly.pure
            (BoundedStep.done (LazyDeltaLoopResult.answer answer))
      | none =>
          refine bind_preservesInferOnly
            (tryReduceDecidable_preservesInferOnly hmethods left) ?_
          intro leftDecidable
          cases leftDecidable with
          | some reduced =>
              refine bind_preservesInferOnly
                (isDefEqCall_preservesInferOnly hmethods reduced right) ?_
              intro answer
              exact TcM.PreservesInferOnly.pure
                (BoundedStep.done (LazyDeltaLoopResult.answer answer))
          | none =>
              refine bind_preservesInferOnly
                (tryReduceDecidable_preservesInferOnly hmethods right) ?_
              intro rightDecidable
              cases rightDecidable with
              | some reduced =>
                  refine bind_preservesInferOnly
                    (isDefEqCall_preservesInferOnly hmethods left reduced) ?_
                  intro answer
                  exact TcM.PreservesInferOnly.pure
                    (BoundedStep.done (LazyDeltaLoopResult.answer answer))
              | none =>
                  exact
                    defEqLazyDeltaStepAfterAcceleratorMiss_preservesInferOnly
                      hmethods hnoDelta hcheapNoDelta left right

theorem defEqLazyDeltaStepAfterOffsetMiss_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((defEqLazyDeltaStepAfterOffsetMiss (left, right)).run
      methods).PreservesInferOnly := by
  unfold defEqLazyDeltaStepAfterOffsetMiss
  simp only [ReaderT.run_bind]
  apply TcM.PreservesInferOnly.bind TcM.PreservesInferOnly.get
  intro state
  by_cases hnat : (!left.hasFVars && !right.hasFVars) || state.eagerReduce
  · simp only [hnat, if_true]
    apply TcM.PreservesInferOnly.bind
      (tryReduceNat_preservesInferOnly hmethods left)
    intro leftNat
    cases leftNat with
    | some reduced =>
        apply TcM.PreservesInferOnly.bind
          (isDefEqCall_preservesInferOnly hmethods reduced right)
        intro answer
        exact TcM.PreservesInferOnly.pure
          (BoundedStep.done (LazyDeltaLoopResult.answer answer))
    | none =>
        apply TcM.PreservesInferOnly.bind
          (tryReduceNat_preservesInferOnly hmethods right)
        intro rightNat
        cases rightNat with
        | some reduced =>
            apply TcM.PreservesInferOnly.bind
              (isDefEqCall_preservesInferOnly hmethods left reduced)
            intro answer
            exact TcM.PreservesInferOnly.pure
              (BoundedStep.done (LazyDeltaLoopResult.answer answer))
        | none =>
            exact defEqLazyDeltaStepAfterNatMiss_preservesInferOnly hmethods
              hnoDelta hcheapNoDelta left right
  · simp only [hnat, Bool.false_eq_true, if_false, pure_bind]
    exact defEqLazyDeltaStepAfterNatMiss_preservesInferOnly hmethods hnoDelta
      hcheapNoDelta left right

theorem defEqLazyDeltaStep_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (state : KExpr .anon × KExpr .anon) :
    ((defEqLazyDeltaStep state).run methods).PreservesInferOnly := by
  rcases state with ⟨left, right⟩
  unfold defEqLazyDeltaStep
  refine bind_preservesInferOnly
    (tryDefEqOffset_preservesInferOnly hmethods left right) ?_
  intro result
  cases result with
  | some answer =>
      exact TcM.PreservesInferOnly.pure
        (BoundedStep.done (LazyDeltaLoopResult.answer answer))
  | none =>
      exact defEqLazyDeltaStepAfterOffsetMiss_preservesInferOnly hmethods
        hnoDelta hcheapNoDelta left right

theorem runDefEqLazyDelta_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (hcheapNoDelta : ∀ source,
      ((whnfNoDeltaForDefEq source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((runDefEqLazyDelta left right).run methods).PreservesInferOnly := by
  unfold runDefEqLazyDelta
  exact runBounded_preservesInferOnly
    (defEqLazyDeltaStep_preservesInferOnly hmethods hnoDelta hcheapNoDelta) _
      (left, right)

theorem isDefEqAfterLazyDeltaStopped_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hwhnf : ∀ source,
      ((whnf source).run methods).PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((isDefEqAfterLazyDeltaStopped left right).run
      methods).PreservesInferOnly := by
  unfold isDefEqAfterLazyDeltaStopped
  refine bind_preservesInferOnly
    (tryStructuralCongruence_preservesInferOnly hmethods hcore hnoDelta left
      right) ?_
  intro structural
  cases structural with
  | true => exact TcM.PreservesInferOnly.pure true
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      refine bind_preservesInferOnly (hcore left) ?_
      intro leftCore
      refine bind_preservesInferOnly (hcore right) ?_
      intro rightCore
      by_cases hchanged :
          (leftCore.addr != left.addr) || (rightCore.addr != right.addr)
      · simp only [hchanged, if_true]
        exact isDefEqCall_preservesInferOnly hmethods leftCore rightCore
      · simp only [hchanged, Bool.false_eq_true, if_false]
        by_cases haddress : leftCore.addr == rightCore.addr
        · simp only [haddress, if_true]
          exact TcM.PreservesInferOnly.pure true
        · simp only [haddress, Bool.false_eq_true, if_false]
          refine bind_preservesInferOnly
            (quickDefEq_preservesInferOnly hmethods leftCore rightCore) ?_
          intro quick
          cases quick with
          | true => exact TcM.PreservesInferOnly.pure true
          | false =>
              simp only [Bool.false_eq_true, if_false]
              refine bind_preservesInferOnly
                (tryDefEqApp_preservesInferOnly hmethods leftCore rightCore) ?_
              intro application
              cases application with
              | true => exact TcM.PreservesInferOnly.pure true
              | false =>
                  simp only [Bool.false_eq_true, if_false]
                  exact isDefEqWhnf_preservesInferOnly hmethods hwhnf hnoDelta
                    leftCore rightCore

theorem isDefEqInnerAfterProofIrrelevance_preservesInferOnly
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
    ((isDefEqInnerAfterProofIrrelevance left right).run
      methods).PreservesInferOnly := by
  unfold isDefEqInnerAfterProofIrrelevance
  refine bind_preservesInferOnly
    (runDefEqLazyDelta_preservesInferOnly hmethods hnoDelta hcheapNoDelta left
      right) ?_
  intro result
  cases result with
  | answer answer => exact TcM.PreservesInferOnly.pure answer
  | stopped stoppedLeft stoppedRight =>
      exact isDefEqAfterLazyDeltaStopped_preservesInferOnly hmethods hwhnf
        hcore hnoDelta stoppedLeft stoppedRight

end RecM

end Ix.Tc
