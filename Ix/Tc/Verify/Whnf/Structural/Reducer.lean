import Ix.Tc.Verify.Whnf.Structural.VerifiedStep
import Ix.Tc.Verify.Whnf.Iota.OptionalReduction

/-!
# Construct the structural reducer

This slice connects the exhaustive local step to the bounded structural
driver and its real cache shell.  The context is indexed by the actual
universe count and local context used by `WhnfContextKeys`; it therefore
cannot replay a cache meaning proved at one universe count as though it held
at every other count.

`StructuralCoreContext.wf` produces the exact `StructuralReduction.WF`
consumed by the no-delta reducer.  In particular, its iota field is OptionalReduction's
state/semantic composition rather than a free `OptionalReduction.WF`
parameter.
-/

namespace Ix.Tc
namespace RecM

/-- Complete fixed-context input for the production structural reducer.

The remaining fields are owned by distinct parts of the verification model:
finite execution coverage, Theory, local-context safety, projection and
inductive admission, suffix-key interpretation, and collision-robust cache
provenance. -/
structure StructuralCoreContext {alpha : Type}
    (initial : TcState .anon) (program : TcM .anon alpha)
    (requests : List WalkerRequest) (keys : WhnfContextKeys)
    (fallback : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport)
    (Delta : KVLCtx) (flags : WhnfFlags) : Type where
  run : RunAssumptions initial program requests support
  letCensus : LetSubstRequestCensus requests support
  betaCensus : BetaRequestCensus requests support
  applicationCensus : ApplicationFinishRequestCensus requests support
  kCensus : KSynthCandidateRequestCensus requests
  iotaCensus : IotaRuleRequestCensus requests
  structEtaCensus : StructEtaFinishRequestCensus requests
  theory : WhnfTheory trProj world keys.uvars
  fvar : FVarZetaSafety .noAccel
    (whnfCacheSemantics keys trProj fallback) trProj world support
    keys.uvars Delta
  legacyVar : LegacyZetaRequestCensus .noAccel
    (whnfCacheSemantics keys trProj fallback) trProj world support
    keys.uvars Delta requests
  inputs : WhnfCoreInputSupport support
  telescopeInputs : ConstructorTelescopeInputSupport support
  constructorInputs : ConstructorTelescopeInputOracle trProj world support
  recursorInputs : StructEtaRecursorInputOracle trProj world support
  projectionHelper : ProjectionHelper.WF .noAccel
    (whnfCacheSemantics keys trProj fallback) trProj world support
  inductiveReduction : InductiveReductionOracle .noAccel
    (whnfCacheSemantics keys trProj fallback) trProj world support
  strings : ProjectionStringPlanContext trProj world support
  kSynthInputs :
    KSynthCandidateInputOracle trProj world support
  natOffsetCleanupInputs :
    NatOffsetCleanupInputOracle trProj world support
  iotaIngress : AnonLazyIngressContext .noAccel
    (whnfCacheSemantics keys trProj fallback) trProj world support
  iotaCallbacks : IotaCallbackFrameOracle
    (whnfCacheSemantics keys trProj fallback) trProj world support
  iotaSuccess : IotaSuccessOracle
    (whnfCacheSemantics keys trProj fallback) trProj world support
  keyRep : ∀ source, support source →
    WhnfKey.Represents keys trProj world source Delta
  cacheWrites : WhnfCoreCacheWriteOracle keys trProj fallback world support

namespace StructuralCoreContext

/-- The actual public `whnfCoreWithFlags` satisfies the structural-reduction
contract at the universe/context encoded by the cache model. -/
theorem wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {keys : WhnfContextKeys}
    {fallback : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {Delta : KVLCtx} {flags : WhnfFlags}
    (context : StructuralCoreContext initial program requests keys fallback
      trProj world support Delta flags) :
    StructuralReduction.WF .noAccel
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta flags := by
  intro source sourceV s hsourceSupport hsource
  have hiota : OptionalReduction.WF .noAccel
      (whnfCacheSemantics keys trProj fallback) trProj world support
      (fun source => tryIotaWithFlags source flags) :=
    tryIotaWithFlags_optional_wf_of_contexts context.run context.kCensus
      context.iotaCensus context.structEtaCensus context.strings
      context.inputs context.telescopeInputs context.constructorInputs
      context.recursorInputs context.kSynthInputs
      context.natOffsetCleanupInputs
      context.iotaIngress
      context.iotaCallbacks context.iotaSuccess flags
  have hstep :=
    whnfCoreWithFlagsStep_constructive_wf
      (uvars := keys.uvars) (Delta := Delta)
      context.run context.letCensus context.betaCensus
      context.applicationCensus context.theory context.fvar
      context.legacyVar context.inputs context.projectionHelper
      context.inductiveReduction hiota
  have hdriver :=
    whnfCoreWithFlags_wf context.theory
      (context.keyRep source hsourceSupport)
      (TransientNatWork.preserving
        (context.iotaIngress.preserves
          (uvars := keys.uvars) (Delta := Delta))
        source)
      hstep context.cacheWrites hsourceSupport (s := s) hsource
  exact RecM.WF.mono hdriver
    (fun _ _ hpost => ⟨hpost.1, hpost.2.meaning hsource⟩)
    (fun _ _ herror => herror)

end StructuralCoreContext
end RecM
end Ix.Tc
