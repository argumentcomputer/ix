import Ix.Tc.Verify.Check.DefEqFinalWhnfPolicy

/-!
# Operational policy for projection-directed DefEq delta reduction

This module verifies the compact lazy-delta loop used by projection
congruence, together with its app-spine comparator.  Delta lookups, WHNF
callbacks, projection reduction, bounded iteration, and recursive equality
all preserve the inference-policy bit on success and error.
-/

namespace Ix.Tc

namespace RecM

theorem tryUnfoldProjApp_preservesInferOnly
    {methods : Methods .anon}
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (source : KExpr .anon) :
    ((tryUnfoldProjApp source).run methods).PreservesInferOnly := by
  rcases hspine : source.collectSpine with ⟨head, arguments⟩
  unfold tryUnfoldProjApp
  simp only [hspine]
  cases head with
  | prj projectionId field value info =>
      simp only [pure_bind]
      refine bind_preservesInferOnly (hnoDelta source) ?_
      intro reduced
      split <;> exact TcM.PreservesInferOnly.pure _
  | var | fvar | sort | const | app | lam | all | letE | nat | str =>
      exact TcM.PreservesInferOnly.pure none

theorem finishLazyDeltaReductionStep_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((finishLazyDeltaReductionStep left right).run
      methods).PreservesInferOnly := by
  unfold finishLazyDeltaReductionStep
  refine bind_preservesInferOnly
    (quickDefEq_preservesInferOnly hmethods left right) ?_
  intro equal
  split <;> exact TcM.PreservesInferOnly.pure _

theorem lazyDeltaReductionStepWithLeftDelta_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((lazyDeltaReductionStepWithLeftDelta left right).run
      methods).PreservesInferOnly := by
  unfold lazyDeltaReductionStepWithLeftDelta
  refine bind_preservesInferOnly
    (deltaUnfoldOne_preservesInferOnly left) ?_
  intro unfoldedResult
  cases unfoldedResult with
  | none => exact TcM.PreservesInferOnly.pure (LazyDeltaStep.unknown, left, right)
  | some unfolded =>
      refine bind_preservesInferOnly (hcore unfolded) ?_
      intro reduced
      exact finishLazyDeltaReductionStep_preservesInferOnly hmethods reduced
        right

theorem lazyDeltaReductionStepWithRightDelta_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((lazyDeltaReductionStepWithRightDelta left right).run
      methods).PreservesInferOnly := by
  unfold lazyDeltaReductionStepWithRightDelta
  refine bind_preservesInferOnly
    (deltaUnfoldOne_preservesInferOnly right) ?_
  intro unfoldedResult
  cases unfoldedResult with
  | none => exact TcM.PreservesInferOnly.pure (LazyDeltaStep.unknown, left, right)
  | some unfolded =>
      refine bind_preservesInferOnly (hcore unfolded) ?_
      intro reduced
      exact finishLazyDeltaReductionStep_preservesInferOnly hmethods left
        reduced

theorem lazyDeltaReductionStepAfterSameHeadMiss_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((lazyDeltaReductionStepAfterSameHeadMiss left right).run
      methods).PreservesInferOnly := by
  unfold lazyDeltaReductionStepAfterSameHeadMiss
  refine bind_preservesInferOnly
    (deltaUnfoldOne_preservesInferOnly left) ?_
  intro leftUnfolded
  refine bind_preservesInferOnly
    (deltaUnfoldOne_preservesInferOnly right) ?_
  intro rightUnfolded
  cases leftUnfolded with
  | none =>
      cases rightUnfolded with
      | none => exact TcM.PreservesInferOnly.pure (LazyDeltaStep.unknown, left, right)
      | some rightBody =>
          refine bind_preservesInferOnly (hcore rightBody) ?_
          intro rightReduced
          exact finishLazyDeltaReductionStep_preservesInferOnly hmethods left
            rightReduced
  | some leftBody =>
      cases rightUnfolded with
      | none =>
          refine bind_preservesInferOnly (hcore leftBody) ?_
          intro leftReduced
          exact finishLazyDeltaReductionStep_preservesInferOnly hmethods
            leftReduced right
      | some rightBody =>
          refine bind_preservesInferOnly (hcore leftBody) ?_
          intro leftReduced
          refine bind_preservesInferOnly (hcore rightBody) ?_
          intro rightReduced
          exact finishLazyDeltaReductionStep_preservesInferOnly hmethods
            leftReduced rightReduced

theorem lazyDeltaReductionStepWithEqualRank_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) (leftId rightId : KId .anon) :
    ((lazyDeltaReductionStepWithEqualRank left right leftId rightId).run
      methods).PreservesInferOnly := by
  unfold lazyDeltaReductionStepWithEqualRank
  refine bind_preservesInferOnly (isRegular_preservesInferOnly leftId) ?_
  intro regular
  by_cases hguard : leftId.addr == rightId.addr && regular
  · simp only [hguard, if_true]
    refine bind_preservesInferOnly
      (trySameHeadSpine_preservesInferOnly hmethods left right) ?_
    intro result
    cases result with
    | none =>
        exact lazyDeltaReductionStepAfterSameHeadMiss_preservesInferOnly
          hmethods hcore left right
    | some answer =>
        cases answer with
        | true =>
            exact TcM.PreservesInferOnly.pure
              (LazyDeltaStep.equal, left, right)
        | false =>
            exact lazyDeltaReductionStepAfterSameHeadMiss_preservesInferOnly
              hmethods hcore left right
  · simp only [hguard, Bool.false_eq_true, if_false, pure_bind]
    exact lazyDeltaReductionStepAfterSameHeadMiss_preservesInferOnly hmethods
      hcore left right

theorem lazyDeltaReductionStepWithBothDelta_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (left right : KExpr .anon)
    (leftHead rightHead : Option (KId .anon)) :
    ((lazyDeltaReductionStepWithBothDelta left right leftHead rightHead).run
      methods).PreservesInferOnly := by
  unfold lazyDeltaReductionStepWithBothDelta
  refine bind_preservesInferOnly
    (defRankId_preservesInferOnly leftHead.get!) ?_
  intro leftRank
  refine bind_preservesInferOnly
    (defRankId_preservesInferOnly rightHead.get!) ?_
  intro rightRank
  simp only
  split
  · exact lazyDeltaReductionStepWithLeftDelta_preservesInferOnly hmethods
      hcore left right
  · split
    · exact lazyDeltaReductionStepWithRightDelta_preservesInferOnly hmethods
        hcore left right
    · exact lazyDeltaReductionStepWithEqualRank_preservesInferOnly hmethods
        hcore left right leftHead.get! rightHead.get!

theorem lazyDeltaReductionStepAfterActive_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (left right : KExpr .anon)
    (leftHead rightHead : Option (KId .anon))
    (leftDelta rightDelta : Bool) :
    ((lazyDeltaReductionStepAfterActive left right leftHead rightHead leftDelta
      rightDelta).run methods).PreservesInferOnly := by
  unfold lazyDeltaReductionStepAfterActive
  by_cases hleftOnly : leftDelta && !rightDelta
  · simp only [hleftOnly, if_true]
    refine bind_preservesInferOnly
      (tryUnfoldProjApp_preservesInferOnly hnoDelta right) ?_
    intro projectionResult
    cases projectionResult with
    | some reduced =>
        exact finishLazyDeltaReductionStep_preservesInferOnly hmethods left
          reduced
    | none =>
        exact lazyDeltaReductionStepWithLeftDelta_preservesInferOnly hmethods
          hcore left right
  · simp only [hleftOnly, Bool.false_eq_true, if_false]
    by_cases hrightOnly : !leftDelta && rightDelta
    · simp only [hrightOnly, if_true]
      refine bind_preservesInferOnly
        (tryUnfoldProjApp_preservesInferOnly hnoDelta left) ?_
      intro projectionResult
      cases projectionResult with
      | some reduced =>
          exact finishLazyDeltaReductionStep_preservesInferOnly hmethods
            reduced right
      | none =>
          exact lazyDeltaReductionStepWithRightDelta_preservesInferOnly
            hmethods hcore left right
    · simp only [hrightOnly, Bool.false_eq_true, if_false]
      exact lazyDeltaReductionStepWithBothDelta_preservesInferOnly hmethods
        hcore left right leftHead rightHead

theorem lazyDeltaReductionStepAfterClassification_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (left right : KExpr .anon)
    (leftHead rightHead : Option (KId .anon))
    (leftDelta rightDelta : Bool) :
    ((lazyDeltaReductionStepAfterClassification left right leftHead rightHead
      leftDelta rightDelta).run methods).PreservesInferOnly := by
  unfold lazyDeltaReductionStepAfterClassification
  split
  · exact TcM.PreservesInferOnly.pure
      (LazyDeltaStep.unknown, left, right)
  · simp only [pure_bind]
    exact lazyDeltaReductionStepAfterActive_preservesInferOnly hmethods hcore
      hnoDelta left right leftHead rightHead leftDelta rightDelta

theorem lazyDeltaReductionStep_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((lazyDeltaReductionStep left right).run
      methods).PreservesInferOnly := by
  unfold lazyDeltaReductionStep
  refine bind_preservesInferOnly
    (classifyDeltaHead_preservesInferOnly left) ?_
  intro leftDelta
  refine bind_preservesInferOnly
    (classifyDeltaHead_preservesInferOnly right) ?_
  intro rightDelta
  exact lazyDeltaReductionStepAfterClassification_preservesInferOnly hmethods
    hcore hnoDelta left right (headConstId left) (headConstId right) leftDelta
    rightDelta

theorem lazyDeltaProjReductionStep_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (structureId : KId .anon) (field : UInt64)
    (state : KExpr .anon × KExpr .anon) :
    (((fun current : KExpr .anon × KExpr .anon => do
      let (left, right) := current
      let (outcome, left, right) ← lazyDeltaReductionStep left right
      match outcome with
      | .equal => return BoundedStep.done true
      | .continue' => return BoundedStep.next (left, right)
      | .unknown =>
        let leftProjection ← tryProjReduce structureId field left
        let rightProjection ← tryProjReduce structureId field right
        match leftProjection, rightProjection with
        | some leftReduced, some rightReduced =>
            return BoundedStep.done (← isDefEqCall leftReduced rightReduced)
        | _, _ => return BoundedStep.done (← isDefEqCall left right)) state).run
      methods).PreservesInferOnly := by
  rcases state with ⟨left, right⟩
  refine bind_preservesInferOnly
    (lazyDeltaReductionStep_preservesInferOnly hmethods hcore hnoDelta left
      right) ?_
  intro result
  rcases result with ⟨outcome, leftReduced, rightReduced⟩
  cases outcome with
  | equal => exact TcM.PreservesInferOnly.pure (BoundedStep.done true)
  | continue' =>
      exact TcM.PreservesInferOnly.pure
        (BoundedStep.next (leftReduced, rightReduced))
  | unknown =>
      refine bind_preservesInferOnly
        (tryProjReduce_preservesInferOnly hmethods structureId field
          leftReduced) ?_
      intro leftProjection
      refine bind_preservesInferOnly
        (tryProjReduce_preservesInferOnly hmethods structureId field
          rightReduced) ?_
      intro rightProjection
      cases leftProjection with
      | none =>
          refine bind_preservesInferOnly
            (isDefEqCall_preservesInferOnly hmethods leftReduced
              rightReduced) ?_
          intro answer
          exact TcM.PreservesInferOnly.pure (BoundedStep.done answer)
      | some leftProjection =>
          cases rightProjection with
          | none =>
              refine bind_preservesInferOnly
                (isDefEqCall_preservesInferOnly hmethods leftReduced
                  rightReduced) ?_
              intro answer
              exact TcM.PreservesInferOnly.pure (BoundedStep.done answer)
          | some rightProjection =>
              refine bind_preservesInferOnly
                (isDefEqCall_preservesInferOnly hmethods leftProjection
                  rightProjection) ?_
              intro answer
              exact TcM.PreservesInferOnly.pure (BoundedStep.done answer)

theorem lazyDeltaProjReduction_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (structureId : KId .anon) (field : UInt64)
    (left right : KExpr .anon) :
  ((lazyDeltaProjReduction structureId field left right).run
      methods).PreservesInferOnly := by
  unfold lazyDeltaProjReduction
  simp only
  apply runBounded_preservesInferOnly
  intro state
  rcases state with ⟨currentLeft, currentRight⟩
  refine bind_preservesInferOnly
    (lazyDeltaReductionStep_preservesInferOnly hmethods hcore hnoDelta
      currentLeft currentRight) ?_
  intro result
  rcases result with ⟨outcome, reducedLeft, reducedRight⟩
  cases outcome with
  | equal => exact TcM.PreservesInferOnly.pure (BoundedStep.done true)
  | continue' =>
      exact TcM.PreservesInferOnly.pure
        (BoundedStep.next (reducedLeft, reducedRight))
  | unknown =>
      refine bind_preservesInferOnly
        (tryProjReduce_preservesInferOnly hmethods structureId field
          reducedLeft) ?_
      intro leftProjection
      refine bind_preservesInferOnly
        (tryProjReduce_preservesInferOnly hmethods structureId field
          reducedRight) ?_
      intro rightProjection
      cases leftProjection with
      | none =>
          refine bind_preservesInferOnly
            (isDefEqCall_preservesInferOnly hmethods reducedLeft
              reducedRight) ?_
          intro answer
          exact TcM.PreservesInferOnly.pure (BoundedStep.done answer)
      | some leftProjection =>
          cases rightProjection with
          | none =>
              refine bind_preservesInferOnly
                (isDefEqCall_preservesInferOnly hmethods reducedLeft
                  reducedRight) ?_
              intro answer
              exact TcM.PreservesInferOnly.pure (BoundedStep.done answer)
          | some rightProjection =>
              refine bind_preservesInferOnly
                (isDefEqCall_preservesInferOnly hmethods leftProjection
                  rightProjection) ?_
              intro answer
              exact TcM.PreservesInferOnly.pure (BoundedStep.done answer)

theorem tryStructuralCongruence_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (hcore : ∀ source,
      ((whnfCore source).run methods).PreservesInferOnly)
    (hnoDelta : ∀ source,
      ((whnfNoDelta source).run methods).PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryStructuralCongruence left right).run
      methods).PreservesInferOnly := by
  cases left with
  | prj structureId field value info =>
      cases right with
      | prj rightId rightField rightValue rightInfo =>
          simp only [tryStructuralCongruence]
          split
          · exact TcM.PreservesInferOnly.pure false
          · simp only [pure_bind]
            exact lazyDeltaProjReduction_preservesInferOnly hmethods hcore
              hnoDelta structureId field value rightValue
      | var | fvar | sort | const | app | lam | all | letE | nat | str =>
          exact TcM.PreservesInferOnly.pure false
  | var | fvar | sort | const | app | lam | all | letE | nat | str =>
      cases right <;> intro before <;> rfl

theorem tryDefEqApp_preservesInferOnly
    {methods : Methods .anon} (hmethods : methods.PreservesInferOnly)
    (left right : KExpr .anon) :
    ((tryDefEqApp left right).run methods).PreservesInferOnly := by
  cases left with
  | app leftFunction leftArgument leftInfo =>
      cases right with
      | app rightFunction rightArgument rightInfo =>
          rcases hleft :
              (leftFunction.app leftArgument leftInfo).collectSpine with
            ⟨leftHead, leftArguments⟩
          rcases hright :
              (rightFunction.app rightArgument rightInfo).collectSpine with
            ⟨rightHead, rightArguments⟩
          simp only [tryDefEqApp, hleft, hright, Bool.not_true,
            Bool.false_or, Bool.false_eq_true, if_false, pure_bind]
          split
          · exact TcM.PreservesInferOnly.pure false
          · refine bind_preservesInferOnly
              (isDefEqCall_preservesInferOnly hmethods leftHead rightHead) ?_
            intro headsEqual
            cases headsEqual with
            | false => exact TcM.PreservesInferOnly.pure false
            | true =>
                simp only [Bool.not_true, Bool.false_eq_true, if_false]
                exact allDefEqSpineArgs_preservesInferOnly hmethods
                  (leftArguments.zip rightArguments)
      | var | fvar | sort | const | lam | all | letE | prj | nat | str =>
          simp only [tryDefEqApp]
          exact TcM.PreservesInferOnly.pure false
  | var | fvar | sort | const | lam | all | letE | prj | nat | str =>
      cases right <;> simp only [tryDefEqApp] <;>
        exact TcM.PreservesInferOnly.pure false

end RecM

end Ix.Tc
