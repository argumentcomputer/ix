import Ix.Tc.Verify.DefEq.Closure
import Ix.Tc.Verify.Infer.CacheSoundness

/-!
# Recursive inference and definitional-equality closure

Inference and definitional equality are the two non-WHNF fields of the
production method table.  This module proves their simultaneous fixed-
universe induction step: both fields may call a strictly smaller method table,
and neither proof assumes the next table is already sound.
-/

namespace Ix.Tc

/-- Concrete resources for the inference and DefEq fields of one production
method-table layer.  The shared proposition context fixes the suffix model,
cache semantics, and universe count for both fields. -/
structure InferDefEqClosureContext
    {alpha : Type} (initial : TcState .anon) (program : TcM .anon alpha)
    (requests : List WalkerRequest)
    {trProj : RawProjRel} {world : VerifyWorld} (support : RunSupport)
    (proposition : PropositionClassifierContext trProj world support)
    (eligible : KId .anon → Prop) where
  inference : UncachedInference.Context initial program requests
    (kernelCacheSemantics proposition.model.keys trProj) trProj world support
    proposition.model.keys.uvars
  defEq : RecM.DefEqClosureResources support proposition eligible

namespace InferDefEqClosureContext

/-- Assemble both non-WHNF fields for one unfolded production method table.
Recursive calls are justified exclusively by the supplied predecessor-table
contract. -/
theorem layer
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (context : InferDefEqClosureContext initial program requests support
      proposition eligible)
    (methods : Methods .anon)
    (hmethods : Methods.WFAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars methods) :
    Methods.InferDefEqLayerWFAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars methods where
  infer := context.inference.nextInfer_wf methods hmethods
  isDefEq := context.defEq.nextDefEq_wf methods hmethods

/-- Headline fixed-universe closure for the inference/DefEq pair. -/
theorem closedAt
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (context : InferDefEqClosureContext initial program requests support
      proposition eligible) :
    Methods.InferDefEqClosedAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world support
      proposition.model.keys.uvars := by
  intro methods hmethods
  exact context.layer methods hmethods

end InferDefEqClosureContext

end Ix.Tc
