import Ix.Tc.Verify.DefEq.ProjectionDeltaActive
import Ix.Tc.Verify.DefEq.ProjectionProbe

/-!
# Projection-directed delta closure

The branch proofs for the compact projection loop are deliberately split by
production control-flow seam.  This module is their resource-level assembly:
it constructs the one-step contract, the direct projection contract, and the
bounded loop from concrete lower reducers and finite support facts.

In particular, structural congruence no longer needs a free semantic contract
for `lazyDeltaProjReduction`.  The only projection-specific semantic boundary
left here is `DirectProjectionReflection`, indexed by the exact successful
execution of `tryProjReduce`.
-/

namespace Ix.Tc

namespace RecM

/-- Concrete inputs needed by the complete no-acceleration projection-delta
loop.  Every executable helper is named explicitly; no field assumes the
outer loop or its step is already sound. -/
structure ProjectionDeltaClosureResources
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) where
  theory : WhnfTheory trProj world uvars
  ingress : AnonLazyIngressContext .noAccel semantics trProj world support
  collision : support.CollisionFree
  sorts : SortComponentResources support
  quick : QuickDefEqResources support
  sameHeadSpines : SameHeadSpineResources support
  values : ProjectionValueResources support
  projectionWhnf : DefEqReduction.WFAt .noAccel semantics trProj world
    support uvars whnfNoDelta
  delta : OptionalReduction.WFAt .noAccel semantics trProj world support
    uvars deltaUnfoldOne
  core : DefEqReduction.WFAt .noAccel semantics trProj world support uvars
    whnfCore
  directProjection : DirectProjectionReductionResources semantics trProj
    world support

namespace ProjectionDeltaClosureResources

/-- The shared productive finish, projected from the complete resource
record. -/
def finish
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (resources : ProjectionDeltaClosureResources semantics trProj world
      support uvars) :
    ProjectionDeltaFinishResources trProj world support uvars where
  theory := resources.theory
  collision := resources.collision
  sorts := resources.sorts
  structural := resources.quick

/-- The unfold-and-normalize context shared by one- and two-sided branches. -/
def reduction
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (resources : ProjectionDeltaClosureResources semantics trProj world
      support uvars) :
    ProjectionDeltaReductionContext .noAccel semantics trProj world support
      uvars where
  finish := resources.finish
  delta := resources.delta
  normalize := resources.core

/-- Assemble every compact-step branch and the direct projection reducer into
the exact lower-resource record consumed by the bounded driver. -/
theorem loop
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (resources : ProjectionDeltaClosureResources semantics trProj world
      support uvars) :
    ProjectionDeltaLoopResources .noAccel semantics trProj world support
      uvars where
  values := resources.values
  step := LazyDeltaReductionStep.ofResources resources.ingress
    (tryUnfoldProjApp_wf resources.projectionWhnf)
    (TrySameHeadSpine.ofResources resources.theory resources.collision
      resources.sameHeadSpines)
    resources.reduction
  projection := TryProjReduce.ofDirectResources resources.directProjection

end ProjectionDeltaClosureResources

namespace LazyDeltaProjReduction

/-- Construct the bounded projection-directed comparison from concrete lower
resources, without assuming the outer helper's semantic contract. -/
theorem ofClosureResources
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (resources : ProjectionDeltaClosureResources semantics trProj world
      support uvars) :
    LazyDeltaProjReduction.WFAt .noAccel semantics trProj world support
      uvars :=
  LazyDeltaProjReduction.ofResources resources.theory resources.loop

end LazyDeltaProjReduction

namespace TryStructuralCongruence

/-- Structural congruence with its matching-projection branch discharged by
the concrete projection-delta closure. -/
theorem ofProjectionDeltaResources
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (resources : ProjectionDeltaClosureResources semantics trProj world
      support uvars)
    (structural : StructuralCongruenceResources support) :
    TryStructuralCongruence.WFAt .noAccel semantics trProj world support
      uvars :=
  TryStructuralCongruence.ofResources resources.theory resources.collision
    structural (LazyDeltaProjReduction.ofClosureResources resources)

end TryStructuralCongruence

end RecM

end Ix.Tc
