import Ix.Tc.Verify.Whnf.Iota.Ingress

/-!
# Exhaustive iota optional-reduction contract

`Ingress` proves that every result or partial error of the production
`tryIotaWithFlags` dispatcher preserves the complete K1 state invariant.  This
slice separates the two remaining concerns:

* `IotaCallbackFrameOracle` retains the trusted-reference and
  recursion-cache authorities crossed by the dispatcher; predecessor-table
  callback contracts now come directly from `Methods.WF` at their exact
  translated inputs; and
* `IotaSuccessOracle` is the admission-owned semantic boundary for an observed
  successful reduction.

The latter deliberately contains no state-preservation field.  Successful,
absent, and error states are all discharged by `Ingress`; the inductive boundary
supplies only finite result support and Theory meaning.  Lazy declaration
ingress is supplied separately by `AnonLazyIngressContext`, which identifies
the actual installed `ingressAnonAddrShallow` hook.
-/

namespace Ix.Tc

/-- Remaining non-method authority used by `tryIotaWithFlags`.

The predecessor-table WHNF and inference frames are no longer fields here:
`Ingress` instantiates them directly from `Methods.WF` at the supported,
translated inputs selected by the production trace.  What remains is
catalog/reference closure and semantic provenance for recursion-cache
writes. -/
structure IotaCallbackFrameOracle (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) : Prop where
  trustedReferences : RecM.TrustedReferences world support
  isRecValid : ∀ {id : KId .anon}, world.trusted id →
    ∀ value,
      semantics.Valid (CacheAuthority.stable world) support
        (.isRec id.addr value)

/-- Semantic authority for one observed successful iota reduction.

This is the direct boundary required by the current application step.  Unlike
the historical `InductiveReductionOracle.iota` field, it does not depend on an
unrelated preceding head-WHNF equation.  Inductive admission must construct
this field from its registered checked recursor rules, including ordinary
iota, literal preprocessing, K synthesis, and struct eta. -/
structure IotaSuccessOracle (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) : Prop where
  accept : ∀ {uvars : Nat} {Delta : KVLCtx}
      {methods : Methods .anon} {source : KExpr .anon}
      {sourceV : Lean4Lean.VExpr} {flags : WhnfFlags}
      {s sf : TcState .anon} {result : KExpr .anon},
    Methods.WFAt .noAccel semantics trProj world support uvars methods →
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    WhnfStateInv .noAccel semantics trProj world support uvars Delta s →
    (RecM.tryIotaWithFlags source flags).run methods s =
      .ok (some result) sf →
    support result ∧
      WhnfMeaning trProj world uvars Delta source result

namespace RecM

/-- Complete `OptionalReduction.WF` for the production iota dispatcher.

All state claims, including partial errors, come from the exhaustive Ingress
proof.  The success oracle is consulted only after the actual run has returned
`some`; misses require no semantic authority. -/
theorem tryIotaWithFlags_optional_wf_of_contexts
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (kCensus : KSynthCandidateRequestCensus requests)
    (iotaCensus : IotaRuleRequestCensus requests)
    (finishCensus : StructEtaFinishRequestCensus requests)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld}
    (strings : ProjectionStringPlanContext trProj world support)
    (inputs : WhnfCoreInputSupport support)
    (telescopeInputs : ConstructorTelescopeInputSupport support)
    (constructorInputs :
      ConstructorTelescopeInputOracle trProj world support)
    (recursorInputs : StructEtaRecursorInputOracle trProj world support)
    (candidateInputs : KSynthCandidateInputOracle trProj world support)
    (cleanupInputs : NatOffsetCleanupInputOracle trProj world support)
    (ingress : AnonLazyIngressContext .noAccel semantics trProj world support)
    (callbacks : IotaCallbackFrameOracle semantics trProj world support)
    (success : IotaSuccessOracle semantics trProj world support)
    (flags : WhnfFlags) :
    OptionalReduction.WF .noAccel semantics trProj world support
      (fun source => tryIotaWithFlags source flags) := by
  intro uvars Delta source sourceV s hsourceSupport hsource
  intro methods hmethods hI
  have hstate :=
    tryIotaWithFlags_state_wf_of_contexts (uvars := uvars) (Delta := Delta)
      hrun kCensus iotaCensus finishCensus strings inputs telescopeInputs
      constructorInputs recursorInputs candidateInputs cleanupInputs
      hmethods (fun {_} => ingress.preserves)
      callbacks.trustedReferences
      (fun id htrusted =>
        IsRecCacheWriteOracle.of_trusted htrusted
          (callbacks.isRecValid htrusted))
      source hsourceSupport hsource flags s
  have hpost := hstate hI
  match hrunIota :
      (tryIotaWithFlags source flags).run methods s with
  | .error err sf =>
      rw [hrunIota] at hpost
      exact ⟨hpost.1, trivial⟩
  | .ok none sf =>
      rw [hrunIota] at hpost
      exact ⟨hpost.1, trivial⟩
  | .ok (some result) sf =>
      rw [hrunIota] at hpost
      exact ⟨hpost.1,
        success.accept hmethods hsourceSupport hsource hI hrunIota⟩

end RecM
end Ix.Tc
