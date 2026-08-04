import Ix.Tc.Verify.Infer.CacheSoundness
import Ix.Tc.Verify.RecursiveMethods.ScopedCallDomains

/-!
# Run-scoped call-domain inference

This is the finite-suffix-state counterpart of `RecursiveMethods.Inference`.
The production cache shell is proved directly over `ScopedWhnfStateInv`:
key construction advances the suffix scope through its memo update, while
interning and cache insertion use the exact digest-neutral state frame.

No theorem in this module converts a `ScopedKernelSuffixModel` to the legacy
globally quantified `KernelSuffixModel`.
-/

namespace Ix.Tc

namespace TcM

/-- Direct interning preserves a run-scoped suffix model because its exact
state frame changes only the intern table.  The successful result and frame
remain exposed for syntax-specific leaf proofs. -/
theorem intern_scoped_wf
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport} {Delta : KVLCtx}
    {e : KExpr .anon} {s : TcState .anon}
    (hcollision : support.CollisionFree) (hsupport : support e) :
    TcM.WF (ScopedWhnfStateInv model layer semantics support Delta) s
      (TcM.intern e)
      (fun result after => result = e ∧ InternUpdateFrame s after) := by
  intro hI
  obtain ⟨after, hrun, hbase, hframe⟩ :=
    TcM.intern_whnf_eval hcollision hsupport hI.1
  rw [hrun]
  exact ⟨⟨hbase, model.preservesFrame hI.2
    (ContextDigestFrame.ofInternUpdateFrame hframe)⟩, rfl, hframe⟩

end TcM

/-- Per-layer inference resources whose uncached body preserves the finite
suffix-state domain as well as the ordinary checker invariant. -/
structure ScopedInferenceCallDomainContext
    {trProj : RawProjRel} {world : VerifyWorld} (scope : RunSupport)
    (model : ScopedKernelSuffixModel trProj world)
    (current predecessor : Methods.CallDomain) : Type where
  collisionFree : scope.CollisionFree
  currentWithin : current.Within scope
  theory : WhnfTheory trProj world model.keys.uvars
  references : RecM.TrustedReferences world scope
  uncached : ∀ {Delta : KVLCtx} {s : TcState .anon} {inferOnly : Bool}
      {source : KExpr .anon} {sourceV : Lean4Lean.VExpr},
    current.infer source →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
      sourceV →
    RecM.ScopedWFOn model .noAccel
      (kernelCacheSemantics model.keys trProj) scope predecessor Delta s
      (RecM.inferUncached RecM.inferCall inferOnly source)
      (fun result _ => scope result ∧
        InferPost trProj world model.keys.uvars Delta sourceV result)

namespace ScopedInferenceCallDomainContext

private theorem cacheReferences
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {current predecessor : Methods.CallDomain}
    (context : ScopedInferenceCallDomainContext scope model current
      predecessor)
    {kind : ExprCacheKind} {key : Address × Address}
    {ty : KExpr .anon} (hty : scope ty) :
    (CacheEntry.expr kind key ty).ReferencesAuthorized
      (CacheAuthority.stable world) scope := by
  intro id href
  apply Or.inl
  rcases href with href | href
  · obtain ⟨source, hsource, _, hreference⟩ := href
    exact context.references hsource hreference
  · exact context.references hty href

/-- A validated inference-cache insertion changes no suffix-digest input
field, so it preserves both halves of the scoped invariant. -/
private theorem cacheWriteFull_scopedWFOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {predecessor : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {key : Address × Address} {ty : KExpr .anon}
    (hnew : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) scope (.expr .infer key ty)) :
    RecM.ScopedWFOn model .noAccel
      (kernelCacheSemantics model.keys trProj) scope predecessor Delta s
      (RecM.cacheInferResult false key ty) (fun _ _ => True) := by
  intro methods _ hI
  rw [RecM.cacheInferResult_full_run]
  refine ⟨⟨RecM.InferCacheUpdate.full_whnfStateInv hI.1 hnew,
    model.preservesFrame hI.2 ?_⟩, trivial⟩
  constructor <;> rfl

/-- An infer-only cache insertion has the same digest-neutral state frame. -/
private theorem cacheWriteInferOnly_scopedWFOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {predecessor : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {key : Address × Address} {ty : KExpr .anon}
    (hnew : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) scope (.expr .inferOnly key ty)) :
    RecM.ScopedWFOn model .noAccel
      (kernelCacheSemantics model.keys trProj) scope predecessor Delta s
      (RecM.cacheInferResult true key ty) (fun _ _ => True) := by
  intro methods _ hI
  rw [RecM.cacheInferResult_inferOnly_run]
  refine ⟨⟨RecM.InferCacheUpdate.inferOnly_whnfStateInv hI.1 hnew,
    model.preservesFrame hI.2 ?_⟩, trivial⟩
  constructor <;> rfl

/-- Execute one admitted uncached source and install its result without ever
leaving the model's finite suffix-state domain. -/
private theorem missTail_scopedWFOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {current predecessor : Methods.CallDomain}
    (context : ScopedInferenceCallDomainContext scope model current
      predecessor)
    {Delta : KVLCtx} {before s : TcState .anon} {inferOnly : Bool}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    {key : Address × Address}
    (hmatch : model.keys.Matches trProj world before Delta source key)
    (hcall : current.infer source)
    (hsource : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta
      source sourceV) :
    RecM.ScopedWFOn model .noAccel
      (kernelCacheSemantics model.keys trProj) scope predecessor Delta s
      (do
        let ty ← RecM.inferUncached RecM.inferCall inferOnly source
        RecM.cacheInferResult inferOnly key ty
        pure ty)
      (fun result _ => scope result ∧
        InferPost trProj world model.keys.uvars Delta sourceV result) := by
  have hsourceSupport := context.currentWithin.infer hcall
  cases inferOnly with
  | false =>
      apply RecM.ScopedWFOn.bind
        (RecM.ScopedWFOn.withInv (context.uncached hcall hsource))
      intro ty afterBody hbody
      rcases hbody with ⟨_, hty, hpost⟩
      have hprovenance := model.transports.inferProvenance
        context.collisionFree .infer hsourceSupport hty hmatch
        (InferMeaning.of_post hsource hpost)
        (context.cacheReferences hty)
      apply RecM.ScopedWFOn.bind
        (Q1 := fun _ _ => True)
        (cacheWriteFull_scopedWFOn (predecessor := predecessor) hprovenance)
      intro _ afterWrite _
      exact RecM.ScopedWFOn.pure fun _ => ⟨hty, hpost⟩
  | true =>
      apply RecM.ScopedWFOn.bind
        (RecM.ScopedWFOn.withInv (context.uncached hcall hsource))
      intro ty afterBody hbody
      rcases hbody with ⟨_, hty, hpost⟩
      have hprovenance := model.transports.inferProvenance
        context.collisionFree .inferOnly hsourceSupport hty hmatch
        (InferMeaning.of_post hsource hpost)
        (context.cacheReferences hty)
      apply RecM.ScopedWFOn.bind
        (Q1 := fun _ _ => True)
        (cacheWriteInferOnly_scopedWFOn (predecessor := predecessor)
          hprovenance)
      intro _ afterWrite _
      exact RecM.ScopedWFOn.pure fun _ => ⟨hty, hpost⟩

/-- Production `inferWith` over one admitted source, with scope preserved on
key errors, cache hits, uncached errors, and both cache-write partitions. -/
theorem inferWith_scopedWFOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {current predecessor : Methods.CallDomain}
    (context : ScopedInferenceCallDomainContext scope model current
      predecessor)
    {Delta : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hcall : current.infer source)
    (hsource : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta
      source sourceV) :
    RecM.ScopedWFOn model .noAccel
      (kernelCacheSemantics model.keys trProj) scope predecessor Delta s
      (RecM.inferWith RecM.inferCall source)
      (fun result _ => scope result ∧
        InferPost trProj world model.keys.uvars Delta sourceV result) := by
  have hsourceSupport := context.currentWithin.infer hcall
  unfold RecM.inferWith
  apply RecM.ScopedWFOn.bind
    (Q1 := fun observed after => observed = s ∧ after = s)
    (RecM.ScopedWFOn.get fun _ => ⟨rfl, rfl⟩)
  intro observed after hread
  rcases hread with ⟨hObserved, hAfter⟩
  subst observed
  subst after
  apply RecM.ScopedWFOn.bind
    (Q1 := fun key _ =>
      model.keys.Matches trProj world s Delta source key)
  · apply RecM.ScopedWFOn.liftTcM
    exact TcM.WF.mono (TcM.inferKey_scoped_model_matches_wf model)
      (fun _ _ h => h.1) (fun _ _ h => h)
  · intro key afterKey hmatch
    apply RecM.ScopedWFOn.bind
      (Q1 := fun currentState after =>
        currentState = afterKey ∧ after = afterKey)
      (RecM.ScopedWFOn.get fun _ => ⟨rfl, rfl⟩)
    intro currentState afterRead hread
    rcases hread with ⟨hCurrent, hAfterRead⟩
    subst currentState
    subst afterRead
    let fullFound := afterKey.env.inferCache[key]?
    cases hfullFound : fullFound with
    | some cached =>
        have hhit : afterKey.env.inferCache[key]? = some cached := by
          simpa [fullFound] using hfullFound
        simp only [hhit]
        exact RecM.ScopedWFOn.pure fun hI => by
          have hprovenance := hI.1.1.caches.hit (.infer hhit)
          have hmeaning := hprovenance.kernelInferMeaningOfMatches
            .infer hsourceSupport hmatch
          exact ⟨hprovenance.supported.2,
            hmeaning.post context.theory hI.1.2.1.wf hsource⟩
    | none =>
        have hfullMiss : afterKey.env.inferCache[key]? = none := by
          simpa [fullFound] using hfullFound
        simp only [hfullMiss]
        cases hpolicy : s.inferOnly with
        | false =>
            simp only [Bool.false_eq_true, if_false]
            exact context.missTail_scopedWFOn hmatch hcall hsource
        | true =>
            simp only [pure_bind, if_true]
            apply RecM.ScopedWFOn.bind
              (Q1 := fun currentState after =>
                currentState = afterKey ∧ after = afterKey)
              (RecM.ScopedWFOn.get fun _ => ⟨rfl, rfl⟩)
            intro currentState afterInferOnlyRead hread
            rcases hread with ⟨hCurrent, hAfterRead⟩
            subst currentState
            subst afterInferOnlyRead
            let inferOnlyFound := afterKey.env.inferOnlyCache[key]?
            cases hinferOnlyFound : inferOnlyFound with
            | some cached =>
                have hhit : afterKey.env.inferOnlyCache[key]? = some cached :=
                  by simpa [inferOnlyFound] using hinferOnlyFound
                simp only [hhit]
                exact RecM.ScopedWFOn.pure fun hI => by
                  have hprovenance := hI.1.1.caches.hit (.inferOnly hhit)
                  have hmeaning := hprovenance.kernelInferMeaningOfMatches
                    .inferOnly hsourceSupport hmatch
                  exact ⟨hprovenance.supported.2,
                    hmeaning.post context.theory hI.1.2.1.wf hsource⟩
            | none =>
                have hmiss : afterKey.env.inferOnlyCache[key]? = none := by
                  simpa [inferOnlyFound] using hinferOnlyFound
                simp only [hmiss]
                exact context.missTail_scopedWFOn hmatch hcall hsource

/-- The inference field of one unfolded method-table layer, now directly
proved over the run-scoped suffix model. -/
theorem nextInfer_scopedWFAtOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : ScopedKernelSuffixModel trProj world}
    {current predecessor : Methods.CallDomain}
    (context : ScopedInferenceCallDomainContext scope model current
      predecessor)
    (predecessorMethods : Methods .anon)
    (predecessorWF : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) scope predecessor
      predecessorMethods) :
    ∀ {Delta : KVLCtx} {s : TcState .anon}
        {source : KExpr .anon} {sourceV : Lean4Lean.VExpr},
      current.infer source →
      TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
        sourceV →
      TcM.WF
        (ScopedWhnfStateInv model .noAccel
          (kernelCacheSemantics model.keys trProj) scope Delta) s
        ((Methods.next predecessorMethods).infer source)
        (fun result _ => scope result ∧
          InferPost trProj world model.keys.uvars Delta sourceV result) := by
  intro Delta s source sourceV hcall hsource
  simpa [Methods.next, RecM.infer] using
    (context.inferWith_scopedWFOn hcall hsource) predecessorMethods
      predecessorWF

end ScopedInferenceCallDomainContext

end Ix.Tc
