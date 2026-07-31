import Ix.Tc.Verify.DefEq.ProjectionDeltaEqualRank

/-!
# Projection-delta rank dispatch

When both compact-loop operands are delta-reducible, production reads their
reducibility ranks and selects a left-only, right-only, or equal-rank helper.
Rank values carry no semantic authority: every selected helper is proved
sound independently.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- A direct reducibility-rank lookup preserves the recursive invariant
through every declaration shape and lazy-ingress outcome. -/
theorem defRankId_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (id : KId .anon) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (defRankId id) (fun _ _ => True) := by
  simpa only [rankDeltaHead] using
    (rankDeltaHead_wf (state := state) hfault (some id))

/-- Exhaustive rank dispatch for the compact projection-delta step. -/
theorem lazyDeltaReductionStepWithBothDelta_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : VExpr} {left right : KExpr .anon}
    {leftHead rightHead : Option (KId .anon)}
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
      (lazyDeltaReductionStepWithBothDelta left right leftHead rightHead)
      (fun result _ => LazyDeltaReductionStepPost trProj world support uvars
        Delta leftSource rightSource result) := by
  unfold lazyDeltaReductionStepWithBothDelta
  apply RecM.WF.bind (defRankId_wf hfault leftHead.get!)
  intro leftRank afterLeftRank _
  apply RecM.WF.bind (defRankId_wf hfault rightHead.get!)
  intro rightRank afterRightRank _
  cases hcompare : compareRank leftRank rightRank with
  | lt =>
      simp
      exact lazyDeltaReductionStepWithRightDelta_wf context hDelta hpair
  | eq =>
      simp
      exact lazyDeltaReductionStepWithEqualRank_wf hfault hsame context
        hDelta hpair
  | gt =>
      simp
      exact lazyDeltaReductionStepWithLeftDelta_wf context hDelta hpair

end RecM

end Ix.Tc
