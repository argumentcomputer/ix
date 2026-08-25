import Ix.Tc.Verify.DefEq.EqualRankCache
import Ix.Tc.Verify.DefEq.ProjectionDeltaUnfolding

/-!
# Equal-rank projection-delta reduction

At equal reducibility rank the compact projection loop first looks up the
head hint and attempts raw same-head spine congruence, bounded for
non-Regular heads, then unfolds both operands and structurally normalizes
every successful unfold.  The rejection-only cache used by the main DefEq
iteration is intentionally absent here; this proof follows the actual
compact helper.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Complete two-sided unfold tail after the compact same-head attempt does
not prove equality. -/
theorem lazyDeltaReductionStepAfterSameHeadMiss_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : VExpr} {left right : KExpr .anon}
    (context : ProjectionDeltaReductionContext layer semantics trProj world
      support uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (lazyDeltaReductionStepAfterSameHeadMiss left right)
      (fun result _ => LazyDeltaReductionStepPost trProj world support uvars
        Delta leftSource rightSource result) := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  unfold lazyDeltaReductionStepAfterSameHeadMiss
  apply RecM.WF.bind (RecM.WF.withInv <|
    context.delta hpair.leftSupport hleft)
  intro leftResult afterLeft hleftResult
  rcases hleftResult with ⟨hILeft, hleftResult⟩
  apply RecM.WF.bind (RecM.WF.withInv <|
    context.delta hpair.rightSupport hright)
  intro rightResult afterRight hrightResult
  rcases hrightResult with ⟨hIRight, hrightResult⟩
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact RecM.WF.pure fun _ => hpair
      | some unfoldedRight =>
          rcases hrightResult with
            ⟨hunfoldedSupport, hunfoldedMeaning⟩
          have hunfoldedPost := WhnfPost.transMeaning
            context.finish.theory hDelta hpair.right hunfoldedMeaning
          obtain ⟨unfoldedV, hunfoldedTr, unfoldedEq⟩ := hunfoldedPost
          apply RecM.WF.bind (RecM.WF.withInv <|
            context.normalize hunfoldedSupport hunfoldedTr)
          intro reduced afterNormalize hreduced
          rcases hreduced with
            ⟨hINormalize, hreducedSupport, hreducedPost⟩
          have hrightReduced := WhnfPost.transMeaning
            context.finish.theory hDelta
            ⟨unfoldedV, hunfoldedTr, unfoldedEq⟩
            (WhnfPost.meaning hunfoldedTr hreducedPost)
          exact finishLazyDeltaReductionStep_wf context.finish
            ⟨hpair.leftSupport, hreducedSupport, hpair.left, hrightReduced⟩
  | some unfoldedLeft =>
      rcases hleftResult with ⟨hleftSupport, hleftMeaning⟩
      have hleftUnfolded := WhnfPost.transMeaning context.finish.theory
        hDelta hpair.left hleftMeaning
      obtain ⟨leftUnfoldedV, hleftUnfoldedTr, hleftUnfoldedEq⟩ :=
        hleftUnfolded
      cases rightResult with
      | none =>
          apply RecM.WF.bind (RecM.WF.withInv <|
            context.normalize hleftSupport hleftUnfoldedTr)
          intro reduced afterNormalize hreduced
          rcases hreduced with
            ⟨hINormalize, hreducedSupport, hreducedPost⟩
          have hleftReduced := WhnfPost.transMeaning context.finish.theory
            hDelta ⟨leftUnfoldedV, hleftUnfoldedTr, hleftUnfoldedEq⟩
            (WhnfPost.meaning hleftUnfoldedTr hreducedPost)
          exact finishLazyDeltaReductionStep_wf context.finish
            ⟨hreducedSupport, hpair.rightSupport, hleftReduced, hpair.right⟩
      | some unfoldedRight =>
          rcases hrightResult with ⟨hrightSupport, hrightMeaning⟩
          have hrightUnfolded := WhnfPost.transMeaning context.finish.theory
            hDelta hpair.right hrightMeaning
          obtain ⟨rightUnfoldedV, hrightUnfoldedTr, hrightUnfoldedEq⟩ :=
            hrightUnfolded
          apply RecM.WF.bind (RecM.WF.withInv <|
            context.normalize hleftSupport hleftUnfoldedTr)
          intro reducedLeft afterNormalizeLeft hreducedLeft
          rcases hreducedLeft with
            ⟨hINormalizeLeft, hreducedLeftSupport, hreducedLeftPost⟩
          have hleftReduced := WhnfPost.transMeaning context.finish.theory
            hDelta ⟨leftUnfoldedV, hleftUnfoldedTr, hleftUnfoldedEq⟩
            (WhnfPost.meaning hleftUnfoldedTr hreducedLeftPost)
          apply RecM.WF.bind (RecM.WF.withInv <|
            context.normalize hrightSupport hrightUnfoldedTr)
          intro reducedRight afterNormalizeRight hreducedRight
          rcases hreducedRight with
            ⟨hINormalizeRight, hreducedRightSupport, hreducedRightPost⟩
          have hrightReduced := WhnfPost.transMeaning context.finish.theory
            hDelta ⟨rightUnfoldedV, hrightUnfoldedTr, hrightUnfoldedEq⟩
            (WhnfPost.meaning hrightUnfoldedTr hreducedRightPost)
          exact finishLazyDeltaReductionStep_wf context.finish
            ⟨hreducedLeftSupport, hreducedRightSupport, hleftReduced,
              hrightReduced⟩

/-- Complete equal-rank compact branch, including hint lookup, every raw
same-head result, and the two-sided reduction tail. -/
theorem lazyDeltaReductionStepWithEqualRank_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : VExpr} {left right : KExpr .anon}
    {leftId rightId : KId .anon}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hsame : TrySameHeadSpine.WFAt layer semantics trProj world support
      uvars)
    (context : ProjectionDeltaReductionContext layer semantics trProj world
      support uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (lazyDeltaReductionStepWithEqualRank left right leftId rightId)
      (fun result _ => LazyDeltaReductionStepPost trProj world support uvars
        Delta leftSource rightSource result) := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  unfold lazyDeltaReductionStepWithEqualRank
  cases hguard : (leftId.addr == rightId.addr) with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact lazyDeltaReductionStepAfterSameHeadMiss_wf context hDelta hpair
  | true =>
      simp only [if_true]
      apply RecM.WF.bind (isRegular_wf hfault leftId)
      intro regular afterRegular _
      cases regular with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          apply RecM.WF.bind <|
            trySameHeadSpineSpeculative_wf hsame hpair.leftSupport
              hpair.rightSupport hleft hright
          intro result afterSame hresult
          cases result with
          | none =>
              exact lazyDeltaReductionStepAfterSameHeadMiss_wf context hDelta
                hpair
          | some answer =>
              cases answer with
              | false =>
                  exact lazyDeltaReductionStepAfterSameHeadMiss_wf context
                    hDelta hpair
              | true =>
                  exact RecM.WF.pure fun _ =>
                    hleftEq.trans world.venvWF hDelta <|
                      (hresult rfl).trans world.venvWF hDelta hrightEq.symm
      | true =>
          simp only [if_true]
          apply RecM.WF.bind <|
            hsame hpair.leftSupport hpair.rightSupport hleft hright
          intro result afterSame hresult
          cases result with
          | none =>
              exact lazyDeltaReductionStepAfterSameHeadMiss_wf context hDelta
                hpair
          | some answer =>
              cases answer with
              | false =>
                  exact lazyDeltaReductionStepAfterSameHeadMiss_wf context
                    hDelta hpair
              | true =>
                  exact RecM.WF.pure fun _ =>
                    hleftEq.trans world.venvWF hDelta <|
                      (hresult rfl).trans world.venvWF hDelta hrightEq.symm

end RecM

end Ix.Tc
