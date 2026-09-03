import Ix.Tc.Verify.Infer.CacheSoundness
import Ix.Tc.Verify.RecursiveMethods.CallDomains

/-!
# Call-domain inference layer

This is the first production layer migrated from the legacy same-support
closure.  Cache behavior still uses one finite `RunSupport`, but uncached
dispatch is required only for sources admitted by the current inference call
domain.  Recursive callbacks inside that dispatch are proved against the
strictly smaller table's domain.

The cache shell is intentionally reproduced at this more precise interface
rather than recovered from `UncachedInference.Context`: that older context
contains the all-support `SyntaxInferenceResources` field whose sort clause is
provably uninhabitable for any finite support containing a sort.
-/

namespace Ix.Tc

/-- Per-layer resources for production inference.  `current` guards only the
outer calls proved at this layer; `predecessor` governs recursive back-edges
made by `inferUncached`. -/
structure InferenceCallDomainContext
    {trProj : RawProjRel} {world : VerifyWorld} (scope : RunSupport)
    (model : KernelSuffixModel trProj world)
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
    RecM.WFOn .noAccel (kernelCacheSemantics model.keys trProj) trProj world
      scope model.keys.uvars predecessor Delta s
      (RecM.inferUncached RecM.inferCall inferOnly source)
      (fun result _ => scope result ∧
        InferPost trProj world model.keys.uvars Delta sourceV result)

namespace InferenceCallDomainContext

private theorem cacheReferences
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : KernelSuffixModel trProj world}
    {current predecessor : Methods.CallDomain}
    (context : InferenceCallDomainContext scope model current predecessor)
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

private theorem cacheWriteFull_wfOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : KernelSuffixModel trProj world}
    {predecessor : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {key : Address × Address} {ty : KExpr .anon}
    (hnew : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) scope (.expr .infer key ty)) :
    RecM.WFOn .noAccel (kernelCacheSemantics model.keys trProj) trProj world
      scope model.keys.uvars predecessor Delta s
      (RecM.cacheInferResult false key ty) (fun _ _ => True) := by
  apply RecM.WFOn.ofWF_of_methodIndependent
  · intro methods
    funext state
    rfl
  · exact RecM.cacheInferResult_full_wf hnew

private theorem cacheWriteInferOnly_wfOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : KernelSuffixModel trProj world}
    {predecessor : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {key : Address × Address} {ty : KExpr .anon}
    (hnew : CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) scope (.expr .inferOnly key ty)) :
    RecM.WFOn .noAccel (kernelCacheSemantics model.keys trProj) trProj world
      scope model.keys.uvars predecessor Delta s
      (RecM.cacheInferResult true key ty) (fun _ _ => True) := by
  apply RecM.WFOn.ofWF_of_methodIndependent
  · intro methods
    funext state
    rfl
  · exact RecM.cacheInferResult_inferOnly_wf hnew

/-- Execute one admitted uncached source and install its result in the cache
partition selected at entry. -/
private theorem missTail_wfOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : KernelSuffixModel trProj world}
    {current predecessor : Methods.CallDomain}
    (context : InferenceCallDomainContext scope model current predecessor)
    {Delta : KVLCtx} {before s : TcState .anon} {inferOnly : Bool}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    {key : Address × Address}
    (hmatch : model.keys.Matches trProj world before Delta source key)
    (hcall : current.infer source)
    (hsource : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta
      source sourceV) :
    RecM.WFOn .noAccel (kernelCacheSemantics model.keys trProj) trProj world
      scope model.keys.uvars predecessor Delta s
      (do
        let ty ← RecM.inferUncached RecM.inferCall inferOnly source
        RecM.cacheInferResult inferOnly key ty
        pure ty)
      (fun result _ => scope result ∧
        InferPost trProj world model.keys.uvars Delta sourceV result) := by
  have hsourceSupport := context.currentWithin.infer hcall
  cases inferOnly with
  | false =>
      apply RecM.WFOn.bind
        (RecM.WFOn.withInv (context.uncached hcall hsource))
      intro ty afterBody hbody
      rcases hbody with ⟨_, hty, hpost⟩
      have hprovenance := model.inferProvenance
        context.collisionFree .infer hsourceSupport hty hmatch
        (InferMeaning.of_post hsource hpost)
        (context.cacheReferences hty)
      apply RecM.WFOn.bind
        (Q1 := fun _ _ => True)
        (cacheWriteFull_wfOn (predecessor := predecessor) hprovenance)
      intro _ afterWrite _
      exact RecM.WFOn.pure fun _ => ⟨hty, hpost⟩
  | true =>
      apply RecM.WFOn.bind
        (RecM.WFOn.withInv (context.uncached hcall hsource))
      intro ty afterBody hbody
      rcases hbody with ⟨_, hty, hpost⟩
      have hprovenance := model.inferProvenance
        context.collisionFree .inferOnly hsourceSupport hty hmatch
        (InferMeaning.of_post hsource hpost)
        (context.cacheReferences hty)
      apply RecM.WFOn.bind
        (Q1 := fun _ _ => True)
        (cacheWriteInferOnly_wfOn (predecessor := predecessor) hprovenance)
      intro _ afterWrite _
      exact RecM.WFOn.pure fun _ => ⟨hty, hpost⟩

/-- Production `inferWith` over one admitted source.  Cache hits use the
shared finite cache semantics; only a genuine miss consumes the guarded
uncached proof. -/
theorem inferWith_wfOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : KernelSuffixModel trProj world}
    {current predecessor : Methods.CallDomain}
    (context : InferenceCallDomainContext scope model current predecessor)
    {Delta : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hcall : current.infer source)
    (hsource : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta
      source sourceV) :
    RecM.WFOn .noAccel (kernelCacheSemantics model.keys trProj) trProj world
      scope model.keys.uvars predecessor Delta s
      (RecM.inferWith RecM.inferCall source)
      (fun result _ => scope result ∧
        InferPost trProj world model.keys.uvars Delta sourceV result) := by
  have hsourceSupport := context.currentWithin.infer hcall
  unfold RecM.inferWith
  apply RecM.WFOn.bind
    (Q1 := fun observed after => observed = s ∧ after = s)
    (RecM.WFOn.get fun _ => ⟨rfl, rfl⟩)
  intro observed after hread
  rcases hread with ⟨hObserved, hAfter⟩
  subst observed
  subst after
  apply RecM.WFOn.bind
    (Q1 := fun key _ =>
      model.keys.Matches trProj world s Delta source key)
  · apply RecM.WFOn.liftTcM
    exact TcM.WF.mono (TcM.inferKey_model_matches_wf model)
      (fun _ _ h => h.1) (fun _ _ h => h)
  · intro key afterKey hmatch
    apply RecM.WFOn.bind
      (Q1 := fun currentState after =>
        currentState = afterKey ∧ after = afterKey)
      (RecM.WFOn.get fun _ => ⟨rfl, rfl⟩)
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
        exact RecM.WFOn.pure fun hI => by
          have hprovenance := hI.1.caches.hit (.infer hhit)
          have hmeaning := hprovenance.kernelInferMeaningOfMatches
            .infer hsourceSupport hmatch hsource.contextScoped
          exact ⟨hprovenance.supported.2,
            hmeaning.post context.theory hI.2.1.wf hsource⟩
    | none =>
        have hfullMiss : afterKey.env.inferCache[key]? = none := by
          simpa [fullFound] using hfullFound
        simp only [hfullMiss]
        cases hpolicy : s.inferOnly with
        | false =>
            simp only [Bool.false_eq_true, if_false]
            exact context.missTail_wfOn hmatch hcall hsource
        | true =>
            simp only [pure_bind, if_true]
            apply RecM.WFOn.bind
              (Q1 := fun currentState after =>
                currentState = afterKey ∧ after = afterKey)
              (RecM.WFOn.get fun _ => ⟨rfl, rfl⟩)
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
                exact RecM.WFOn.pure fun hI => by
                  have hprovenance := hI.1.caches.hit (.inferOnly hhit)
                  have hmeaning := hprovenance.kernelInferMeaningOfMatches
                    .inferOnly hsourceSupport hmatch hsource.contextScoped
                  exact ⟨hprovenance.supported.2,
                    hmeaning.post context.theory hI.2.1.wf hsource⟩
            | none =>
                have hmiss : afterKey.env.inferOnlyCache[key]? = none := by
                  simpa [inferOnlyFound] using hinferOnlyFound
                simp only [hmiss]
                exact context.missTail_wfOn hmatch hcall hsource

/-- The exact inference field of `Methods.next predecessorMethods`. -/
theorem nextInfer_wfAtOn
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {model : KernelSuffixModel trProj world}
    {current predecessor : Methods.CallDomain}
    (context : InferenceCallDomainContext scope model current predecessor)
    (predecessorMethods : Methods .anon)
    (predecessorWF : Methods.WFAtOn .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world scope
      model.keys.uvars predecessor predecessorMethods) :
    ∀ {Delta : KVLCtx} {s : TcState .anon}
        {source : KExpr .anon} {sourceV : Lean4Lean.VExpr},
      current.infer source →
      TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
        sourceV →
      TcM.WF
        (WhnfStateInv .noAccel (kernelCacheSemantics model.keys trProj)
          trProj world scope model.keys.uvars Delta) s
        ((Methods.next predecessorMethods).infer source)
        (fun result _ => scope result ∧
          InferPost trProj world model.keys.uvars Delta sourceV result) := by
  intro Delta s source sourceV hcall hsource
  simpa [Methods.next, RecM.infer] using
    (context.inferWith_wfOn hcall hsource) predecessorMethods predecessorWF

end InferenceCallDomainContext

end Ix.Tc
