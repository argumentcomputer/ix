import Ix.Tc.Verify.Whnf.Iota.SynthesisRequests

/-!
# Actual iota ingress state closure

RebuildRequests closes every post-major branch and SynthesisRequests closes the positive K-synthesis
prefix.  This slice composes those results through production's real
`tryIotaWithFlags` dispatcher: spine classification, lazy recursor lookup,
iota-info and major-index guards, optional K synthesis, the first Nat-offset
cleanup, and the policy-selected major callback.

The struct-eta inference probes and both major-normalization callbacks are
instantiated at their exact translated inputs.  Generated expressions,
catalog reads, and both ordinary and struct-eta iota tails are discharged
from finite run censuses; the remaining callback premises are confined to
bounded helper scans over open declaration telescopes.
-/

namespace Ix.Tc
namespace RecM

/-- Exhaustive state closure of the actual iota reducer. -/
theorem tryIotaWithFlags_state_wf_of_contexts
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
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
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt .noAccel semantics trProj world support uvars methods)
    (hfault : ∀ {current : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv .noAccel semantics trProj world support uvars current))
    (hreferences : TrustedReferences world support)
    (hwrites : ∀ id, world.trusted id →
      IsRecCacheWriteOracle semantics world support methods id)
    (e : KExpr .anon) {sourceV : Lean4Lean.VExpr}
    (hsourceSupport : support e)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta e sourceV)
    (flags : WhnfFlags) (s : TcState .anon) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((tryIotaWithFlags e flags).run methods)
      (fun _ _ => True) := by
  let I :=
    WhnfStateInv .noAccel semantics trProj world support uvars Delta
  have hpost : ∀ (recId : KId .anon) (recr : IotaInfo .anon)
      (recUs : Array (KUniv .anon)) (spine : Array (KExpr .anon))
      (major : KExpr .anon) {majorV : Lean4Lean.VExpr}
      (after : TcState .anon),
      support major →
      TrKExprS world.venv uvars world.nameOf trProj Delta major majorV →
      support spine[recr.majorIdx]! →
      ∀ {spineMajorV : Lean4Lean.VExpr},
      TrKExprS world.venv uvars world.nameOf trProj Delta
        spine[recr.majorIdx]! spineMajorV →
      TcM.WF I after
        ((do
          let major := (← cleanupNatOffsetMajor major).getD major
          let majorWhnf0 ←
            if flags.cheapRec then whnfCoreFlagsRec major flags
            else whnfRec major
          tryIotaAfterMajorWhnf flags recId recr recUs spine majorWhnf0).run
        methods)
        (fun _ _ => True) := by
    intro recId recr recUs spine major majorV after hmajorSupport hmajorTr
      hspineMajorSupport spineMajorV hspineMajorTr
    rw [ReaderT.run_bind]
    apply TcM.WF.bind
      (cleanupNatOffsetMajor_input_wf cleanupInputs hmajorSupport hmajorTr after)
    intro cleaned afterCleanup hcleaned
    let cleanedMajor := cleaned.getD major
    obtain ⟨cleanedMajorV, hcleanedSupport, hcleanedTr⟩ :
        ∃ cleanedMajorV,
          support cleanedMajor ∧
            TrKExprS world.venv uvars world.nameOf trProj Delta
              cleanedMajor cleanedMajorV := by
      cases cleaned with
      | none =>
          exact ⟨majorV, hmajorSupport, hmajorTr⟩
      | some result =>
          simpa only [cleanedMajor, Option.getD_some, OptionalGeneratedInput]
            using hcleaned
    cases hcheap : flags.cheapRec with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        rw [ReaderT.run_bind]
        apply TcM.WF.bind
          ((whnfRec_wf (s := afterCleanup) hcleanedSupport hcleanedTr)
            methods hmethods)
        intro majorWhnf0 afterWhnf _
        exact tryIotaAfterMajorWhnf_state_wf_of_contexts
          hrun iotaCensus finishCensus strings hmethods telescopeInputs
          constructorInputs recursorInputs hfault hreferences hwrites
          hspineMajorSupport hspineMajorTr
    | true =>
        simp only [if_true]
        rw [ReaderT.run_bind]
        apply TcM.WF.bind
          ((whnfCoreFlagsRec_wf (s := afterCleanup)
            hcleanedSupport hcleanedTr) methods hmethods)
        intro majorWhnf0 afterWhnf _
        exact tryIotaAfterMajorWhnf_state_wf_of_contexts
          hrun iotaCensus finishCensus strings hmethods telescopeInputs
          constructorInputs recursorInputs hfault hreferences hwrites
          hspineMajorSupport hspineMajorTr
  unfold tryIotaWithFlags
  rcases hspine : e.collectSpine with ⟨head, spine⟩
  cases head with
  | const recId recUs info =>
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.WF.bind
        (TcM.tryGetConst_wf (hfault (current := Delta)) recId s)
      intro foundRecursor afterLookup _
      cases foundRecursor with
      | none =>
          exact TcM.WF.pure (fun _ => trivial)
      | some recursor =>
          cases hinfo : recursor.iotaInfo? with
          | none =>
              simp only [hinfo]
              exact TcM.WF.pure (fun _ => trivial)
          | some recr =>
              simp only [hinfo, pure_bind]
              by_cases hmajor : spine.size ≤ recr.majorIdx
              · simp only [hmajor, if_pos]
                exact TcM.WF.pure (fun _ => trivial)
              · simp only [hmajor]
                let major := spine[recr.majorIdx]!
                have hmajorLt : recr.majorIdx < spine.size := by
                  omega
                have hmajorGet :
                    spine[recr.majorIdx]? =
                      some spine[recr.majorIdx]! := by
                  rw [getElem?_pos spine recr.majorIdx hmajorLt,
                    getElem!_pos spine recr.majorIdx hmajorLt]
                have hmajorMem :
                    spine[recr.majorIdx]! ∈ spine.toList :=
                  Array.mem_toList_iff.mpr
                    (Array.mem_of_getElem? hmajorGet)
                have hmajorSupport : support major :=
                  inputs.spineArg hsourceSupport hspine hmajorMem
                have hspineTr :=
                  trAppSpine_of_collectSpine hsource hspine
                obtain ⟨majorV, _, _, hmajorTr⟩ :=
                  hspineTr.argument hmajorMem
                cases hk : recr.k with
                | false =>
                    simp only [Bool.false_eq_true, if_false]
                    exact hpost recId recr recUs spine major afterLookup
                      hmajorSupport hmajorTr hmajorSupport hmajorTr
                | true =>
                    simp only [if_true, if_false]
                    rw [ReaderT.run_bind]
                    apply TcM.WF.bind
                      (synthCtorWhenK_state_wf_of_inputs hrun kCensus
                        hmethods telescopeInputs recursorInputs hfault
                        hreferences candidateInputs hmajorSupport hmajorTr
                        recId recr recUs afterLookup)
                    intro synthesized afterKSynth hsynthesized
                    cases synthesized with
                    | definitiveReject =>
                        exact TcM.WF.pure (fun _ => trivial)
                    | inconclusive =>
                        exact hpost recId recr recUs spine major afterKSynth
                          hmajorSupport hmajorTr hmajorSupport hmajorTr
                    | synthesized synthesized =>
                        obtain ⟨hsynthesizedSupport, synthesizedV,
                          hsynthesizedTr⟩ := hsynthesized
                        exact hpost recId recr recUs spine synthesized
                          afterKSynth hsynthesizedSupport hsynthesizedTr
                          hmajorSupport hmajorTr
  | _ =>
      exact TcM.WF.pure (fun _ => trivial)

end RecM
end Ix.Tc
