import Ix.Tc.Verify.DefEq.ProjectionDeltaFinish

/-!
# One-sided projection-delta unfolding

Unequal-rank and asymmetric projection-miss branches unfold one operand,
run the production structural normalizer, and enter the common productive
finish.  The two theorems here cover both directions, including unfold
misses and errors from either helper.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Reduction resources shared by the one- and two-sided compact projection
delta branches. -/
structure ProjectionDeltaReductionContext
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop where
  finish : ProjectionDeltaFinishResources trProj world support uvars
  delta : OptionalReduction.WFAt layer semantics trProj world support uvars
    deltaUnfoldOne
  normalize : DefEqReduction.WFAt layer semantics trProj world support uvars
    whnfCore

/-- The left-only compact delta helper preserves the original pair semantics
on its unfold miss and composes unfold plus structural normalization on a
hit. -/
theorem lazyDeltaReductionStepWithLeftDelta_wf
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
      (lazyDeltaReductionStepWithLeftDelta left right)
      (fun result _ => LazyDeltaReductionStepPost trProj world support uvars
        Delta leftSource rightSource result) := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  unfold lazyDeltaReductionStepWithLeftDelta
  apply RecM.WF.bind (RecM.WF.withInv <|
    context.delta hpair.leftSupport hleft)
  intro unfolded afterUnfold hunfolded
  rcases hunfolded with ⟨hIUnfold, hunfolded⟩
  cases unfolded with
  | none =>
      exact RecM.WF.pure fun _ => hpair
  | some unfoldedLeft =>
      rcases hunfolded with ⟨hunfoldedSupport, hunfoldedMeaning⟩
      have hunfoldedPost := WhnfPost.transMeaning context.finish.theory
        hDelta hpair.left hunfoldedMeaning
      obtain ⟨unfoldedV, hunfoldedTr, unfoldedEq⟩ := hunfoldedPost
      apply RecM.WF.bind (RecM.WF.withInv <|
        context.normalize hunfoldedSupport hunfoldedTr)
      intro reduced afterNormalize hreduced
      rcases hreduced with
        ⟨hINormalize, hreducedSupport, hreducedPost⟩
      have hleftReduced := WhnfPost.transMeaning context.finish.theory
        hDelta ⟨unfoldedV, hunfoldedTr, unfoldedEq⟩
        (WhnfPost.meaning hunfoldedTr hreducedPost)
      exact finishLazyDeltaReductionStep_wf context.finish
        ⟨hreducedSupport, hpair.rightSupport, hleftReduced, hpair.right⟩

/-- Symmetric right-only compact delta helper. -/
theorem lazyDeltaReductionStepWithRightDelta_wf
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
      (lazyDeltaReductionStepWithRightDelta left right)
      (fun result _ => LazyDeltaReductionStepPost trProj world support uvars
        Delta leftSource rightSource result) := by
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  unfold lazyDeltaReductionStepWithRightDelta
  apply RecM.WF.bind (RecM.WF.withInv <|
    context.delta hpair.rightSupport hright)
  intro unfolded afterUnfold hunfolded
  rcases hunfolded with ⟨hIUnfold, hunfolded⟩
  cases unfolded with
  | none =>
      exact RecM.WF.pure fun _ => hpair
  | some unfoldedRight =>
      rcases hunfolded with ⟨hunfoldedSupport, hunfoldedMeaning⟩
      have hunfoldedPost := WhnfPost.transMeaning context.finish.theory
        hDelta hpair.right hunfoldedMeaning
      obtain ⟨unfoldedV, hunfoldedTr, unfoldedEq⟩ := hunfoldedPost
      apply RecM.WF.bind (RecM.WF.withInv <|
        context.normalize hunfoldedSupport hunfoldedTr)
      intro reduced afterNormalize hreduced
      rcases hreduced with
        ⟨hINormalize, hreducedSupport, hreducedPost⟩
      have hrightReduced := WhnfPost.transMeaning context.finish.theory
        hDelta ⟨unfoldedV, hunfoldedTr, unfoldedEq⟩
        (WhnfPost.meaning hunfoldedTr hreducedPost)
      exact finishLazyDeltaReductionStep_wf context.finish
        ⟨hpair.leftSupport, hreducedSupport, hpair.left, hrightReduced⟩

end RecM

end Ix.Tc
