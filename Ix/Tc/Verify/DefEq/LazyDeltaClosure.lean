import Ix.Tc.Verify.DefEq.LazyDeltaIteration
import Ix.Tc.Verify.DefEq.StoppedContinuationClosure

/-!
# Complete lazy-delta tier assembly

The bounded driver needs one verified iteration and one verified continuation
for a stopped pair.  This module joins those independently proved executable
surfaces under the canonical K2 suffix/cache model.
-/

namespace Ix.Tc

namespace RecM

/-- Resources for the complete bounded lazy-delta tier.  Remaining semantic
work is visible inside the two component records rather than hidden behind a
contract for the outer driver. -/
structure LazyDeltaClosureResources
    {trProj : RawProjRel} {world : VerifyWorld} (support : RunSupport)
    (model : KernelSuffixModel trProj world) where
  iteration : LazyDeltaIterationResources support model
  stopped : StoppedContinuationClosureResources
    (kernelCacheSemantics model.keys trProj) trProj world support
    model.keys.uvars

namespace DefEqLazyDeltaContext

/-- Assemble the complete production lazy-delta context from the verified
iteration and stopped continuation. -/
theorem ofKernelResources
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world}
    (resources : LazyDeltaClosureResources support model) :
    DefEqLazyDeltaContext .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars where
  step := DefEqLazyDeltaStep.ofKernelResources model resources.iteration
  stopped := DefEqAfterLazyDeltaStopped.ofClosureResources resources.stopped

end DefEqLazyDeltaContext

namespace DefEqAfterProofIrrelevance

/-- Discharge the exact post-proof-irrelevance tail with the assembled
bounded lazy-delta reducer. -/
theorem ofKernelResources
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world}
    (resources : LazyDeltaClosureResources support model) :
    DefEqAfterProofIrrelevance.WF .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars :=
  DefEqAfterProofIrrelevance.ofLazyDelta resources.iteration.theory
    (DefEqLazyDeltaContext.ofKernelResources resources)

end DefEqAfterProofIrrelevance

end RecM

end Ix.Tc
