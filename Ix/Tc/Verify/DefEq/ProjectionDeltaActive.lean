import Ix.Tc.Verify.DefEq.ProjectionDeltaRank

/-!
# Active projection-delta branches

This module closes the compact delta step after at least one head has been
classified as reducible.  It covers both asymmetric projection probes and
all four flag combinations, then assembles the classifier prefix with rank,
unfold, normalization, and finishing proofs into the exact lower-step
contract used by the bounded projection driver.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Exhaustive active-flag proof for the compact projection-directed delta
step. -/
theorem lazyDeltaReductionStepAfterActive_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : VExpr} {left right : KExpr .anon}
    {leftHead rightHead : Option (KId .anon)}
    {leftDelta rightDelta : Bool}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hprojection : OptionalReduction.WFAt layer semantics trProj world
      support uvars tryUnfoldProjApp)
    (hsame : TrySameHeadSpine.WFAt layer semantics trProj world support
      uvars)
    (context : ProjectionDeltaReductionContext layer semantics trProj world
      support uvars)
    (hactive : (!leftDelta && !rightDelta) = false)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (lazyDeltaReductionStepAfterActive left right leftHead rightHead
        leftDelta rightDelta)
      (fun result _ => LazyDeltaReductionStepPost trProj world support uvars
        Delta leftSource rightSource result) := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  unfold lazyDeltaReductionStepAfterActive
  cases leftDelta <;> cases rightDelta
  case false.false =>
    simp at hactive
  case false.true =>
    simp only [Bool.false_and, Bool.false_eq_true, if_false,
      Bool.not_false, Bool.true_and, if_true]
    apply RecM.WF.bind (RecM.WF.withInv <|
      hprojection hpair.leftSupport hleft)
    intro reduced afterProjection hreduced
    rcases hreduced with ⟨hIProjection, hreduced⟩
    cases reduced with
    | none =>
        exact lazyDeltaReductionStepWithRightDelta_wf context hDelta hpair
    | some reducedLeft =>
        rcases hreduced with ⟨hreducedSupport, hreducedMeaning⟩
        have hleftReduced := WhnfPost.transMeaning context.finish.theory
          hDelta hpair.left hreducedMeaning
        exact finishLazyDeltaReductionStep_wf context.finish
          ⟨hreducedSupport, hpair.rightSupport, hleftReduced, hpair.right⟩
  case true.false =>
    simp only [Bool.not_false, Bool.true_and, if_true]
    apply RecM.WF.bind (RecM.WF.withInv <|
      hprojection hpair.rightSupport hright)
    intro reduced afterProjection hreduced
    rcases hreduced with ⟨hIProjection, hreduced⟩
    cases reduced with
    | none =>
        exact lazyDeltaReductionStepWithLeftDelta_wf context hDelta hpair
    | some reducedRight =>
        rcases hreduced with ⟨hreducedSupport, hreducedMeaning⟩
        have hrightReduced := WhnfPost.transMeaning context.finish.theory
          hDelta hpair.right hreducedMeaning
        exact finishLazyDeltaReductionStep_wf context.finish
          ⟨hpair.leftSupport, hreducedSupport, hpair.left, hrightReduced⟩
  case true.true =>
    simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
    exact lazyDeltaReductionStepWithBothDelta_wf hfault hsame context
      hDelta hpair

namespace LazyDeltaReductionAfterActive

/-- Package the concrete active branches under the installed no-acceleration
lazy-ingress contract. -/
theorem ofResources
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (ingress : AnonLazyIngressContext .noAccel semantics trProj world
      support)
    (hprojection : OptionalReduction.WFAt .noAccel semantics trProj world
      support uvars tryUnfoldProjApp)
    (hsame : TrySameHeadSpine.WFAt .noAccel semantics trProj world support
      uvars)
    (context : ProjectionDeltaReductionContext .noAccel semantics trProj
      world support uvars) :
    LazyDeltaReductionAfterActive.WFAt .noAccel semantics trProj world
      support uvars := by
  intro Delta state leftSource rightSource left right leftHead rightHead
    leftDelta rightDelta hactive hpair
  intro methods hmethods hI
  exact (lazyDeltaReductionStepAfterActive_wf ingress.preserves hprojection
    hsame context hactive hI.2.1.wf hpair) methods hmethods hI

end LazyDeltaReductionAfterActive

namespace LazyDeltaReductionStep

/-- Complete production contract for one compact projection-delta step. -/
theorem ofResources
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (ingress : AnonLazyIngressContext .noAccel semantics trProj world
      support)
    (hprojection : OptionalReduction.WFAt .noAccel semantics trProj world
      support uvars tryUnfoldProjApp)
    (hsame : TrySameHeadSpine.WFAt .noAccel semantics trProj world support
      uvars)
    (context : ProjectionDeltaReductionContext .noAccel semantics trProj
      world support uvars) :
    LazyDeltaReductionStep.WFAt .noAccel semantics trProj world support
      uvars :=
  LazyDeltaReductionStep.ofActive ingress
    (LazyDeltaReductionAfterActive.ofResources ingress hprojection hsame
      context)

end LazyDeltaReductionStep

end RecM

end Ix.Tc
