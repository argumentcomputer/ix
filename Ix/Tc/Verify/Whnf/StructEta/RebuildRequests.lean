import Ix.Tc.Verify.Whnf.Iota.ApplicationRequests

/-!
# Finite request closure for the struct-eta rebuild tail

Classifier exhausts the struct-eta control flow and RebuildTail proves its successful H3
tail from finite walker/rebuild requests.  This slice packages those exact
requests at every possible selected tail, constructs
`StructEtaFinishPreserves`, and therefore replaces NatOffset's whole
`StructEtaIotaPreserves` premise with a contract indexed by the one selected
recursor and spine.  The inference probes are derived from `Methods.WF`; only
the helper-scan and recursion-cache authorities remain.
-/

namespace Ix.Tc
namespace RecM

/-- The exact finite requests for one successful struct-eta H3 tail. -/
structure StructEtaFinishRequests (requests : List WalkerRequest)
    (recUs : Array (KUniv .anon)) (spine : Array (KExpr .anon))
    (recr : IotaInfo .anon) (rule : RecRule .anon) (indId : KId .anon)
    (major : KExpr .anon) where
  instantiate : WalkerRequest.instUniv rule.rhs recUs ∈ requests
  build : ∀ {rhs},
    KExpr.instantiateUnivParamsSpec rule.rhs recUs = .ok rhs →
    Σ final,
      StructEtaBuildRequests requests indId major rhs rule.fields
        (spine.extract 0
          (min (recr.params + recr.motives + recr.minors) spine.size))
        (spine.extract (recr.majorIdx + 1) spine.size) final

/-- Run-wide census indexed by production's exact selected recursor rule,
inductive, major, and argument slices. -/
structure StructEtaFinishRequestCensus (requests : List WalkerRequest) where
  plan : ∀ (recUs : Array (KUniv .anon))
      (spine : Array (KExpr .anon)) (recr : IotaInfo .anon)
      (rule : RecRule .anon) (indId : KId .anon)
      (major : KExpr .anon),
    StructEtaFinishRequests requests recUs spine recr rule indId major

namespace StructEtaFinishPreserves

/-- Construct Classifier's final-tail contract from the exact finite run census. -/
theorem of_requests
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : StructEtaFinishRequestCensus requests)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon} :
    StructEtaFinishPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
      methods := by
  intro recUs spine recr rule indId major majorSortW s
  let plan := census.plan recUs spine recr rule indId major
  exact finishStructEtaAfterSort_wf_of_requests hrun
    (hrun.coverage.instUniv plan.instantiate) plan.build

end StructEtaFinishPreserves

namespace StructEtaIotaPreserves

/-- NatOffset's selected struct-eta boundary constructed from Classifier's precise
helper/cache authorities, exact major translation, and RebuildTail's finite
final-tail census. -/
theorem of_components
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (finishCensus : StructEtaFinishRequestCensus requests)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ConstructorTelescopeInputSupport support)
    (hctorInputs : ConstructorTelescopeInputOracle trProj world support)
    (hrecInputs : StructEtaRecursorInputOracle trProj world support)
    (hfault : ∀ {current : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv layer semantics trProj world support uvars current))
    (hreferences : TrustedReferences world support)
    (hwrites : ∀ id, world.trusted id →
      IsRecCacheWriteOracle semantics world support methods id)
    {majorV : Lean4Lean.VExpr}
    (hmajorSupport : support spine[recr.majorIdx]!)
    (hmajorTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      spine[recr.majorIdx]! majorV) :
    SelectedStructEtaIotaPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta)
      methods recId recr recUs spine := by
  intro s
  exact tryStructEtaIota_wf hmethods hinputs hctorInputs hrecInputs hfault
    hreferences hwrites hmajorSupport hmajorTr
    (StructEtaFinishPreserves.of_requests hrun finishCensus)

end StructEtaIotaPreserves

/-- The complete post-major state path with both NatOffset whole-tail premises
replaced by finite requests and the remaining exact callback/cache
authorities. -/
theorem tryIotaAfterMajorWhnf_state_wf_of_contexts
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (iotaCensus : IotaRuleRequestCensus requests)
    (finishCensus : StructEtaFinishRequestCensus requests)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld}
    (strings : ProjectionStringPlanContext trProj world support)
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt .noAccel semantics trProj world support uvars methods)
    (hinputs : ConstructorTelescopeInputSupport support)
    (hctorInputs : ConstructorTelescopeInputOracle trProj world support)
    (hrecInputs : StructEtaRecursorInputOracle trProj world support)
    (hfault : ∀ {current : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv .noAccel semantics trProj world support uvars current))
    (hreferences : TrustedReferences world support)
    (hwrites : ∀ id, world.trusted id →
      IsRecCacheWriteOracle semantics world support methods id)
    {flags : WhnfFlags} {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {majorV : Lean4Lean.VExpr}
    (hmajorSupport : support spine[recr.majorIdx]!)
    (hmajorTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      spine[recr.majorIdx]! majorV)
    {majorWhnf0 : KExpr .anon} {s : TcState .anon} :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((tryIotaAfterMajorWhnf flags recId recr recUs spine majorWhnf0).run
        methods)
      (fun _ _ => True) := by
  exact tryIotaAfterMajorWhnf_state_wf strings hmethods
    (hfault (current := Delta))
    (TryApplyIotaCtorPreserves.of_requests hrun iotaCensus)
    (StructEtaIotaPreserves.of_components hrun finishCensus hmethods hinputs
      hctorInputs hrecInputs hfault hreferences hwrites hmajorSupport hmajorTr)

end RecM
end Ix.Tc
