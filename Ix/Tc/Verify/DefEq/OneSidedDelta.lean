import Ix.Tc.Verify.DefEq.LoopFinish

/-!
# One-sided lazy-delta unfolding

Both a lone reducible head and an unequal-rank pair use the same operation:
unfold one operand, normalize that result without delta, and run the common
finishing checks.  This module gives those shared production helpers their
complete pair-invariant contracts.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Semantic resources shared by one- and two-sided lazy-delta reductions. -/
structure LazyDeltaReductionContext
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop where
  theory : WhnfTheory trProj world uvars
  collision : support.CollisionFree
  sorts : SortComponentResources support
  structural : QuickDefEqResources support
  delta : OptionalReduction.WFAt layer semantics trProj world support uvars
    deltaUnfoldOne
  normalize : DefEqReduction.WFAt layer semantics trProj world support uvars
    whnfNoDeltaForDefEq

/-- The left-only production helper preserves the lazy-delta action
contract, including the exact unfold-miss stopped result. -/
theorem defEqLazyDeltaStepWithLeftDelta_wf
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
      (defEqLazyDeltaStepWithLeftDelta left right)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action) := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  unfold defEqLazyDeltaStepWithLeftDelta
  apply RecM.WF.bind
    (RecM.WF.withInv <|
      context.delta hpair.leftSupport hleft)
  intro unfolded afterUnfold hunfolded
  rcases hunfolded with ⟨hIUnfold, hunfolded⟩
  cases unfolded with
  | none =>
      exact RecM.WF.pure fun _ => hpair
  | some unfoldedLeft =>
      rcases hunfolded with ⟨hunfoldedSupport, hunfoldedMeaning⟩
      have hunfoldedPost := WhnfPost.transMeaning context.theory hDelta
        hpair.left hunfoldedMeaning
      obtain ⟨unfoldedV, hunfoldedTr, hunfoldedEq⟩ := hunfoldedPost
      apply RecM.WF.bind
        (RecM.WF.withInv <|
          context.normalize hunfoldedSupport hunfoldedTr)
      intro reduced afterNormalize hreduced
      rcases hreduced with ⟨hINormalize, hreducedSupport, hreducedPost⟩
      have hleftReduced := WhnfPost.transMeaning context.theory hDelta
        ⟨unfoldedV, hunfoldedTr, hunfoldedEq⟩
        (WhnfPost.meaning hunfoldedTr hreducedPost)
      exact finishDefEqLazyDeltaStep_wf context.theory context.collision
        context.sorts context.structural
        ⟨hreducedSupport, hpair.rightSupport, hleftReduced, hpair.right⟩

/-- Symmetric proof for the right-only production helper. -/
theorem defEqLazyDeltaStepWithRightDelta_wf
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
      (defEqLazyDeltaStepWithRightDelta left right)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action) := by
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  unfold defEqLazyDeltaStepWithRightDelta
  apply RecM.WF.bind
    (RecM.WF.withInv <|
      context.delta hpair.rightSupport hright)
  intro unfolded afterUnfold hunfolded
  rcases hunfolded with ⟨hIUnfold, hunfolded⟩
  cases unfolded with
  | none =>
      exact RecM.WF.pure fun _ => hpair
  | some unfoldedRight =>
      rcases hunfolded with ⟨hunfoldedSupport, hunfoldedMeaning⟩
      have hunfoldedPost := WhnfPost.transMeaning context.theory hDelta
        hpair.right hunfoldedMeaning
      obtain ⟨unfoldedV, hunfoldedTr, hunfoldedEq⟩ := hunfoldedPost
      apply RecM.WF.bind
        (RecM.WF.withInv <|
          context.normalize hunfoldedSupport hunfoldedTr)
      intro reduced afterNormalize hreduced
      rcases hreduced with ⟨hINormalize, hreducedSupport, hreducedPost⟩
      have hrightReduced := WhnfPost.transMeaning context.theory hDelta
        ⟨unfoldedV, hunfoldedTr, hunfoldedEq⟩
        (WhnfPost.meaning hunfoldedTr hreducedPost)
      exact finishDefEqLazyDeltaStep_wf context.theory context.collision
        context.sorts context.structural
        ⟨hpair.leftSupport, hreducedSupport, hpair.left, hrightReduced⟩

end RecM

end Ix.Tc
