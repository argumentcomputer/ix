import Ix.Tc.Verify.DefEq.RankDispatch

/-!
# Equal-rank two-sided reduction

Once the guarded same-head attempt has not answered, equal-rank lazy delta
tries both unfolds before normalizing either result.  This module proves all
four hit/miss combinations in that exact order and feeds every productive
combination through the common finishing checks.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Contract for the equal-rank continuation after the same-head prefix. -/
def DefEqLazyDeltaAfterSameHeadMiss.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state leftSource rightSource left right},
    DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right) →
    RecM.WF layer semantics trProj world support uvars Delta state
      (defEqLazyDeltaStepAfterSameHeadMiss left right)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action)

/-- Close both equal-rank unfold probes, their four result combinations, and
the corresponding no-delta normalization calls. -/
theorem defEqLazyDeltaStepAfterSameHeadMiss_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : VExpr} {left right : KExpr .anon}
    (context : LazyDeltaReductionContext layer semantics trProj world support
      uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (defEqLazyDeltaStepAfterSameHeadMiss left right)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action) := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  unfold defEqLazyDeltaStepAfterSameHeadMiss
  apply RecM.WF.bind
    (RecM.WF.withInv <|
      context.delta hpair.leftSupport hleft)
  intro leftResult afterLeft hleftResult
  rcases hleftResult with ⟨hILeft, hleftResult⟩
  apply RecM.WF.bind
    (RecM.WF.withInv <|
      context.delta hpair.rightSupport hright)
  intro rightResult afterRight hrightResult
  rcases hrightResult with ⟨hIRight, hrightResult⟩
  cases leftResult with
  | none =>
      cases rightResult with
      | none =>
          exact RecM.WF.pure fun _ => hpair
      | some unfoldedRight =>
          rcases hrightResult with
            ⟨hunfoldedSupport, hunfoldedMeaning⟩
          have hunfoldedPost := WhnfPost.transMeaning context.theory hDelta
            hpair.right hunfoldedMeaning
          obtain ⟨unfoldedV, hunfoldedTr, hunfoldedEq⟩ := hunfoldedPost
          apply RecM.WF.bind
            (RecM.WF.withInv <|
              context.normalize hunfoldedSupport hunfoldedTr)
          intro reduced afterNormalize hreduced
          rcases hreduced with
            ⟨hINormalize, hreducedSupport, hreducedPost⟩
          have hrightReduced := WhnfPost.transMeaning context.theory hDelta
            ⟨unfoldedV, hunfoldedTr, hunfoldedEq⟩
            (WhnfPost.meaning hunfoldedTr hreducedPost)
          exact finishDefEqLazyDeltaStep_wf context.theory context.collision
            context.sorts context.structural
            ⟨hpair.leftSupport, hreducedSupport, hpair.left, hrightReduced⟩
  | some unfoldedLeft =>
      rcases hleftResult with ⟨hleftSupport, hleftMeaning⟩
      have hleftUnfolded := WhnfPost.transMeaning context.theory hDelta
        hpair.left hleftMeaning
      obtain ⟨leftUnfoldedV, hleftUnfoldedTr, hleftUnfoldedEq⟩ :=
        hleftUnfolded
      cases rightResult with
      | none =>
          apply RecM.WF.bind
            (RecM.WF.withInv <|
              context.normalize hleftSupport hleftUnfoldedTr)
          intro reduced afterNormalize hreduced
          rcases hreduced with
            ⟨hINormalize, hreducedSupport, hreducedPost⟩
          have hleftReduced := WhnfPost.transMeaning context.theory hDelta
            ⟨leftUnfoldedV, hleftUnfoldedTr, hleftUnfoldedEq⟩
            (WhnfPost.meaning hleftUnfoldedTr hreducedPost)
          exact finishDefEqLazyDeltaStep_wf context.theory context.collision
            context.sorts context.structural
            ⟨hreducedSupport, hpair.rightSupport, hleftReduced, hpair.right⟩
      | some unfoldedRight =>
          rcases hrightResult with ⟨hrightSupport, hrightMeaning⟩
          have hrightUnfolded := WhnfPost.transMeaning context.theory hDelta
            hpair.right hrightMeaning
          obtain ⟨rightUnfoldedV, hrightUnfoldedTr, hrightUnfoldedEq⟩ :=
            hrightUnfolded
          apply RecM.WF.bind
            (RecM.WF.withInv <|
              context.normalize hleftSupport hleftUnfoldedTr)
          intro reducedLeft afterNormalizeLeft hreducedLeft
          rcases hreducedLeft with
            ⟨hINormalizeLeft, hreducedLeftSupport, hreducedLeftPost⟩
          have hleftReduced := WhnfPost.transMeaning context.theory hDelta
            ⟨leftUnfoldedV, hleftUnfoldedTr, hleftUnfoldedEq⟩
            (WhnfPost.meaning hleftUnfoldedTr hreducedLeftPost)
          apply RecM.WF.bind
            (RecM.WF.withInv <|
              context.normalize hrightSupport hrightUnfoldedTr)
          intro reducedRight afterNormalizeRight hreducedRight
          rcases hreducedRight with
            ⟨hINormalizeRight, hreducedRightSupport, hreducedRightPost⟩
          have hrightReduced := WhnfPost.transMeaning context.theory hDelta
            ⟨rightUnfoldedV, hrightUnfoldedTr, hrightUnfoldedEq⟩
            (WhnfPost.meaning hrightUnfoldedTr hreducedRightPost)
          exact finishDefEqLazyDeltaStep_wf context.theory context.collision
            context.sorts context.structural
            ⟨hreducedLeftSupport, hreducedRightSupport, hleftReduced,
              hrightReduced⟩

namespace DefEqLazyDeltaAfterSameHeadMiss

/-- Package the concrete two-sided reducer as the post-same-head contract. -/
theorem ofReduction
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (context : LazyDeltaReductionContext layer semantics trProj world support
      uvars) :
    DefEqLazyDeltaAfterSameHeadMiss.WFAt layer semantics trProj world support
      uvars := by
  intro Delta state leftSource rightSource left right hpair
  intro methods hmethods hI
  exact (defEqLazyDeltaStepAfterSameHeadMiss_wf context hI.2.1.wf hpair)
    methods hmethods hI

end DefEqLazyDeltaAfterSameHeadMiss

end RecM

end Ix.Tc
