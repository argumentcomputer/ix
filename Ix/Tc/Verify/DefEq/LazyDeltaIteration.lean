import Ix.Tc.Verify.DefEq.EqualRankPrefix
import Ix.Tc.Verify.DefEq.NatOffsetDecomposition

/-!
# Complete lazy-delta iteration assembly

The individual production branches are proved in focused modules.  This
module records their exact shared inputs and composes them, in execution
order, into the contract for one complete bounded lazy-delta iteration.

The remaining inputs are deliberately concrete contracts rather than
acceptance oracles: Nat-offset decomposition, the K1 reducers reused by
DefEq, and finite run-scoped resources for same-head comparison and cache
writes.
-/

namespace Ix.Tc

namespace RecM

/-- Run-scoped resources needed to assemble every branch of one production
lazy-delta iteration under the canonical K2 cache semantics. -/
structure LazyDeltaIterationResources
    {trProj : RawProjRel} {world : VerifyWorld} (support : RunSupport)
    (model : KernelSuffixModel trProj world) where
  ingress : AnonLazyIngressContext .noAccel
    (kernelCacheSemantics model.keys trProj) trProj world support
  theory : WhnfTheory trProj world model.keys.uvars
  collision : support.CollisionFree
  sameHeadSpines : SameHeadSpineResources support
  trustedReferences : TrustedReferences world support
  offsetCandidates : NatOffsetCandidateContext .noAccel
    (kernelCacheSemantics model.keys trProj) trProj world support
  natZero : NatZeroContext world
  natReduction : OptionalReduction.WFAt .noAccel
    (kernelCacheSemantics model.keys trProj) trProj world support
    model.keys.uvars tryReduceNat
  projectionWhnf : DefEqReduction.WFAt .noAccel
    (kernelCacheSemantics model.keys trProj) trProj world support
    model.keys.uvars whnfNoDelta
  deltaReduction : LazyDeltaReductionContext .noAccel
    (kernelCacheSemantics model.keys trProj) trProj world support
    model.keys.uvars

namespace DefEqLazyDeltaStep

/-- Compose every verified branch into the complete production one-step
contract.  In particular, the equal-rank failure cache is used only inside
its rejection-only shell; positive equality is supplied by the same-head
semantic proof. -/
theorem ofKernelResources
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (model : KernelSuffixModel trProj world)
    (resources : LazyDeltaIterationResources support model) :
    DefEqLazyDeltaStep.WFAt .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars := by
  have hsameHeadMiss : DefEqLazyDeltaAfterSameHeadMiss.WFAt .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars :=
    DefEqLazyDeltaAfterSameHeadMiss.ofReduction resources.deltaReduction
  have hequalRank : DefEqLazyDeltaEqualRank.WFAt .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars :=
    DefEqLazyDeltaEqualRank.ofKernelResources model resources.ingress
      resources.theory resources.collision resources.sameHeadSpines
      resources.trustedReferences hsameHeadMiss
  have hprojectionMiss : DefEqLazyDeltaAfterProjectionMiss.WFAt .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars :=
    DefEqLazyDeltaAfterProjectionMiss.ofRankDispatch resources.ingress
      resources.deltaReduction hequalRank
  have hprojection : OptionalReduction.WFAt .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars tryUnfoldProjApp :=
    tryUnfoldProjApp_wf resources.projectionWhnf
  have hclassified :
      DefEqLazyDeltaAfterDeltaClassification.WFAt .noAccel
        (kernelCacheSemantics model.keys trProj) trProj world support
        model.keys.uvars :=
    DefEqLazyDeltaAfterDeltaClassification.ofProjection resources.theory
      hprojection hprojectionMiss
  have haccelerators : DefEqLazyDeltaAfterAcceleratorMiss.WFAt .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars :=
    DefEqLazyDeltaAfterAcceleratorMiss.ofClassification resources.ingress
      hclassified
  have hnatMiss : DefEqLazyDeltaAfterNatMiss.WFAt .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars :=
    DefEqLazyDeltaAfterNatMiss.ofNoAccel resources.theory haccelerators
  have hoffsetMiss : DefEqLazyDeltaAfterOffsetMiss.WFAt .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars :=
    DefEqLazyDeltaAfterOffsetMiss.ofNat resources.theory
      resources.natReduction hnatMiss
  have hoffset : TryDefEqOffset.WFAt .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars :=
    TryDefEqOffset.ofContext resources.theory resources.natZero
      (TryDefEqOffsetAfterCandidates.ofContext resources.offsetCandidates)
  intro Delta state leftSource rightSource pair hpair
  intro methods hmethods hI
  exact (defEqLazyDeltaStep_wf hoffset hoffsetMiss hI.2.1.wf hpair)
    methods hmethods hI

end DefEqLazyDeltaStep

end RecM

end Ix.Tc
