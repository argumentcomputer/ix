import Ix.Tc.Verify.InferDefEq.Closure
import Ix.Tc.Verify.Whnf.Closure

/-!
# Complete recursive method-table closure

The production table has four WHNF fields plus inference and definitional
equality.  Their proofs are developed independently, but they must share one
cache stack and one predecessor table before `methodsN` can be justified.
This module performs that final fixed-universe assembly.
-/

namespace Ix.Tc

/-- The semantic cache layers beneath K1's outer WHNF and delta layers. -/
def kernelCacheFallback (keys : WhnfContextKeys) (trProj : RawProjRel) :
    CacheSemantics :=
  inferCacheSemantics keys trProj <|
    defEqCacheSemantics keys trProj <|
      isPropCacheSemantics keys trProj <|
        isRecCacheSemantics CacheSemantics.blockErrorsOnly

/-- Expose the intentional decomposition used to combine the independently
proved WHNF and inference/DefEq closure records. -/
theorem kernelCacheSemantics_eq_k1
    (keys : WhnfContextKeys) (trProj : RawProjRel) :
    kernelCacheSemantics keys trProj =
      k1CacheSemantics keys trProj (kernelCacheFallback keys trProj) := rfl

/-- Concrete resources for all six fields of one unfolded production method
table at the universe count fixed by the joint suffix model. -/
structure RecursiveMethodClosureContext
    {alpha : Type} (initial : TcState .anon) (program : TcM .anon alpha)
    (requests : List WalkerRequest)
    {trProj : RawProjRel} {world : VerifyWorld} (support : RunSupport)
    (proposition : PropositionClassifierContext trProj world support)
    (eligible : KId .anon → Prop) where
  whnf : RecM.K1ClosureContext initial program requests proposition.model.keys
    (kernelCacheFallback proposition.model.keys trProj) trProj world support
  inferDefEq : InferDefEqClosureContext initial program requests support
    proposition eligible

namespace RecursiveMethodClosureContext

/-- Close one fixed-universe layer of the complete six-field method table. -/
theorem closedAt
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (context : RecursiveMethodClosureContext initial program requests support
      proposition eligible) :
    Methods.ClosedAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars := by
  rw [kernelCacheSemantics_eq_k1]
  exact Methods.ClosedAt.of_parts context.whnf.closedAt
    context.inferDefEq.closedAt

/-- Every finite production approximation selected by `runRec` satisfies all
six method contracts. -/
theorem methodsN
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (context : RecursiveMethodClosureContext initial program requests support
      proposition eligible) (n : Nat) :
    Methods.WFAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars (methodsN (m := .anon) n) :=
  Methods.methodsN_wfAt context.closedAt n

end RecursiveMethodClosureContext

end Ix.Tc
