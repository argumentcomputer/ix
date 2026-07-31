import Ix.Tc.Verify.DefEq.EqualRankCache

/-!
# Equal-rank prefix assembly

This module assembles regular-hint lookup, the cached same-head attempt, and
the already-proved two-sided reduction continuation into the complete
equal-rank lazy-delta contract.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Complete equal-rank branch, including every skipped guard, cached miss,
positive same-head result, and the post-miss two-sided reducer. -/
theorem defEqLazyDeltaStepWithEqualRank_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : VExpr} {left right : KExpr .anon}
    {leftHead rightHead : Option (KId .anon)}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hcached : TrySameHeadSpineCached.WFAt layer semantics trProj world
      support uvars)
    (hafter : DefEqLazyDeltaAfterSameHeadMiss.WFAt layer semantics trProj
      world support uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (defEqLazyDeltaStepWithEqualRank left right leftHead rightHead)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action) := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  unfold defEqLazyDeltaStepWithEqualRank
  cases leftHead with
  | none => exact hafter hpair
  | some leftId =>
      cases rightHead with
      | none => exact hafter hpair
      | some rightId =>
          apply RecM.WF.bind (isRegular_wf hfault leftId)
          intro regular afterRegular _
          cases hguard : (leftId.addr == rightId.addr && regular) with
          | false =>
              simp only [Bool.false_eq_true, if_false]
              exact hafter hpair
          | true =>
              simp only [if_true]
              apply RecM.WF.bind <|
                hcached hpair.leftSupport hpair.rightSupport hleft hright
              intro result afterAttempt hresult
              cases result with
              | none => exact hafter hpair
              | some answer =>
                  exact RecM.WF.pure fun _ hanswer =>
                    hleftEq.trans world.venvWF hDelta <|
                      (hresult hanswer).trans world.venvWF hDelta
                        hrightEq.symm

namespace DefEqLazyDeltaEqualRank

/-- Package the complete generic equal-rank branch. -/
theorem ofPrefix
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hfault : ∀ {Delta}, TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hcached : TrySameHeadSpineCached.WFAt layer semantics trProj world
      support uvars)
    (hafter : DefEqLazyDeltaAfterSameHeadMiss.WFAt layer semantics trProj
      world support uvars) :
    DefEqLazyDeltaEqualRank.WFAt layer semantics trProj world support
      uvars := by
  intro Delta state leftSource rightSource left right leftHead rightHead hpair
  intro methods hmethods hI
  exact (defEqLazyDeltaStepWithEqualRank_wf hfault hcached hafter
    hI.2.1.wf hpair) methods hmethods hI

/-- Concrete no-acceleration/K2 construction of the equal-rank branch. -/
theorem ofKernelResources
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (model : KernelSuffixModel trProj world)
    (ingress : AnonLazyIngressContext .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support)
    (theory : WhnfTheory trProj world model.keys.uvars)
    (hcollision : support.CollisionFree)
    (hspines : SameHeadSpineResources support)
    (htrusted : TrustedReferences world support)
    (hafter : DefEqLazyDeltaAfterSameHeadMiss.WFAt .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars) :
    DefEqLazyDeltaEqualRank.WFAt .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars := by
  have hsame : TrySameHeadSpine.WFAt .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars :=
    TrySameHeadSpine.ofResources theory hcollision hspines
  have hcached : TrySameHeadSpineCached.WFAt .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars :=
    TrySameHeadSpineCached.ofResources
      (DefEqFailureCacheResources.ofKernelSuffixModel model htrusted) hsame
  intro Delta state leftSource rightSource left right leftHead rightHead hpair
  intro methods hmethods hI
  exact (defEqLazyDeltaStepWithEqualRank_wf ingress.preserves hcached hafter
    hI.2.1.wf hpair) methods hmethods hI

end DefEqLazyDeltaEqualRank

end RecM

end Ix.Tc
