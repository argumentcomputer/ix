import Ix.Tc.Verify.DefEq.ProjectionDeltaClosure
import Ix.Tc.Verify.DefEq.StoppedContinuation

/-!
# Stopped-continuation closure

Once bounded lazy delta stops, the remaining DefEq control flow consumes a
structural probe, `whnfCore`, application-spine comparison, and final WHNF
comparison.  This module constructs that resource record with the structural
projection branch supplied by the concrete projection-delta closure.
-/

namespace Ix.Tc

namespace RecM

/-- Concrete lower resources for the no-acceleration stopped continuation.
The projection-delta record already owns the shared core, sort, and quick
comparison inputs, so they are not repeated here. -/
structure StoppedContinuationClosureResources
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) where
  projectionDelta : ProjectionDeltaClosureResources semantics trProj world
    support uvars
  structural : StructuralCongruenceResources support
  application : TryDefEqApp.WFAt .noAccel semantics trProj world support
    uvars
  finalWhnf : IsDefEqWhnf.WFAt .noAccel semantics trProj world support
    uvars

namespace StoppedContinuationClosureResources

/-- Assemble the exact helper record consumed by the production stopped
continuation. -/
def stopped
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (resources : StoppedContinuationClosureResources semantics trProj world
      support uvars) :
    StoppedContinuationResources .noAccel semantics trProj world support
      uvars where
  structural := TryStructuralCongruence.ofProjectionDeltaResources
    resources.projectionDelta resources.structural
  core := resources.projectionDelta.core
  sorts := resources.projectionDelta.sorts
  quick := resources.projectionDelta.quick
  application := resources.application
  finalWhnf := resources.finalWhnf

end StoppedContinuationClosureResources

namespace DefEqAfterLazyDeltaStopped

/-- Close the complete stopped continuation without assuming either
structural congruence or the bounded projection loop as a free contract. -/
theorem ofClosureResources
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (resources : StoppedContinuationClosureResources semantics trProj world
      support uvars) :
    DefEqAfterLazyDeltaStopped.WFAt .noAccel semantics trProj world support
      uvars :=
  DefEqAfterLazyDeltaStopped.ofResources resources.projectionDelta.theory
    resources.projectionDelta.collision resources.stopped

end DefEqAfterLazyDeltaStopped

end RecM

end Ix.Tc
