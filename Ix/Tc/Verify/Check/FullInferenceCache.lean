import Ix.Tc.Verify.Check.FullInferenceDispatcher
import Ix.Tc.Verify.Infer.CacheSoundness

/-!
# Full-inference cache shell

The K3 uncached dispatcher establishes a typed source translation from
`PreTrKExprS`.  This module closes the production `inferWith` cache shell
around that result.  Full-cache hits are reconciled with the current raw
translation; misses construct ordinary collision-robust K2 provenance before
writing the validated cache partition.
-/

namespace Ix.Tc

namespace FullUncachedInference.Context

/-- Every direct constant root of a new full-inference cache entry is
authorized by the finite run support. -/
private theorem cacheReferences
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world} {methods : Methods .anon}
    (context : FullUncachedInference.Context initial program requests
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars methods)
    {kind : ExprCacheKind} {key : Address × Address} {ty : KExpr .anon}
    (hty : support ty) :
    (CacheEntry.expr kind key ty).ReferencesAuthorized
      (CacheAuthority.stable world) support := by
  intro id href
  apply Or.inl
  rcases href with hsource | hresult
  · obtain ⟨source, hsourceSupport, _, hsourceRef⟩ := hsource
    exact context.base.references hsourceSupport hsourceRef
  · exact context.base.references hty hresult

/-- Execute a full-mode cache miss and install its result only after the
typed source translation has supplied ordinary K2 inference provenance.
Both the uncached body and the cache write preserve full mode on errors. -/
private theorem missTail_full_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world} {methods : Methods .anon}
    (context : FullUncachedInference.Context initial program requests
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars methods)
    {Delta : KVLCtx} {before s : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    {key : Address × Address}
    (hmatch : model.keys.Matches trProj world before Delta source key)
    (hsourceSupport : support source)
    (hsource : PreTrKExprS world.venv model.keys.uvars world.nameOf trProj
      Delta source sourceV)
    (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars Delta) s
      ((do
        let ty ← RecM.inferUncached RecM.inferCall false source
        RecM.cacheInferResult false key ty
        pure ty).run methods)
      (fun result after => after.inferOnly = false ∧
        FullInferPost trProj world support model.keys.uvars Delta source
          sourceV result)
      (fun _ after => after.inferOnly = false) := by
  simp only [ReaderT.run_bind]
  apply TcM.WF.bind
    (TcM.WF.withInv <|
      RecM.inferUncached_full_wf context hsourceSupport hsource hpolicy)
  intro ty afterBody hbody
  rcases hbody with
    ⟨hI, hpolicyBody, htySupport, hsourceTr, hpost⟩
  have hprovenance := model.inferProvenance
    context.base.projection.run.collisionFree .infer hsourceSupport
    htySupport hmatch (InferMeaning.of_post hsourceTr hpost)
    (context.cacheReferences htySupport)
  apply TcM.WF.bind
    (TcM.WF.mono
      (TcM.PreservesInferOnly.strengthenWFValue
        ((RecM.cacheInferResult_full_wf hprovenance)
          methods context.methodSemantics)
        (RecM.cacheInferResult_preservesInferOnly false key ty methods)
        hpolicyBody)
      (fun _ _ post => post) (fun _ _ post => post.1))
  intro _ afterWrite hwrite
  exact TcM.WF.pure fun _ =>
    ⟨hwrite.1, htySupport, hsourceTr, hpost⟩

end FullUncachedInference.Context

namespace RecM

/-- Complete production `inferWith` in full mode from untyped structural
ingress.  A hit upgrades the current raw translation from cache provenance;
a miss runs the exhaustive K3 dispatcher and writes validated provenance. -/
theorem inferWith_full_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world} {methods : Methods .anon}
    (context : FullUncachedInference.Context initial program requests
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars methods)
    {Delta : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsourceSupport : support source)
    (hsource : PreTrKExprS world.venv model.keys.uvars world.nameOf trProj
      Delta source sourceV)
    (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars Delta) s
      ((inferWith inferCall source).run methods)
      (fun result after => after.inferOnly = false ∧
        FullInferPost trProj world support model.keys.uvars Delta source
          sourceV result)
      (fun _ after => after.inferOnly = false) := by
  unfold inferWith
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply TcM.WF.bind
    (Q₁ := fun observed after =>
      observed = s ∧ after = s ∧ after.inferOnly = false)
    (TcM.WF.get fun _ => ⟨rfl, rfl, hpolicy⟩)
  intro observed after hread
  rcases hread with ⟨rfl, rfl, hpolicyRead⟩
  apply TcM.WF.bind
    (TcM.WF.mono
      (TcM.PreservesInferOnly.strengthenWFValue
        (TcM.inferKey_model_matches_wf model)
        (TcM.PreservesInferOnly.inferKey source) hpolicyRead)
      (fun _ _ post => post) (fun _ _ post => post.1))
  intro key afterKey hkey
  rcases hkey with ⟨hpolicyKey, hmatch, hframe⟩
  apply TcM.WF.bind
    (Q₁ := fun current after =>
      current = afterKey ∧ after = afterKey ∧ after.inferOnly = false)
    (TcM.WF.get fun _ => ⟨rfl, rfl, hpolicyKey⟩)
  intro current afterRead hread
  rcases hread with ⟨rfl, rfl, hpolicyAfterRead⟩
  let fullFound := afterRead.env.inferCache[key]?
  cases hfullFound : fullFound with
  | some cached =>
      have hhit : afterRead.env.inferCache[key]? = some cached := by
        simpa [fullFound] using hfullFound
      simp only [hhit]
      exact TcM.WF.pure fun hI => by
        have hprovenance := hI.1.caches.hit (.infer hhit)
        have hmeaning := hprovenance.kernelInferMeaningOfMatches
          .infer hsourceSupport hmatch
        obtain ⟨typedV, htyped, hcachedPost⟩ := hmeaning
        have hsourceTyped : TrKExprS world.venv model.keys.uvars
            world.nameOf trProj Delta source sourceV :=
          hsource.upgradeOfTyped world.venvWF
            context.base.projection.theory.literalWF
            context.base.projection.theory.projections
            (KVLCtx.IsDefEq.refl world.venvWF hI.2.1.wf) htyped
        exact ⟨hpolicyAfterRead, hprovenance.supported.2, hsourceTyped,
          InferMeaning.post context.base.projection.theory hI.2.1.wf
            hsourceTyped ⟨typedV, htyped, hcachedPost⟩⟩
  | none =>
      have hfullMiss : afterRead.env.inferCache[key]? = none := by
        simpa [fullFound] using hfullFound
      simp only [hfullMiss, hpolicy, Bool.false_eq_true, if_false]
      exact context.missTail_full_wf hmatch hsourceSupport hsource
        hpolicyAfterRead

/-- `RecM.infer` is definitionally the full cache shell above. -/
theorem infer_full_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world} {methods : Methods .anon}
    (context : FullUncachedInference.Context initial program requests
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars methods)
    {Delta : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsourceSupport : support source)
    (hsource : PreTrKExprS world.venv model.keys.uvars world.nameOf trProj
      Delta source sourceV)
    (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars Delta) s
      ((infer source).run methods)
      (fun result after => after.inferOnly = false ∧
        FullInferPost trProj world support model.keys.uvars Delta source
          sourceV result)
      (fun _ after => after.inferOnly = false) := by
  simpa [infer] using
    (inferWith_full_wf context hsourceSupport hsource hpolicy)

end RecM

end Ix.Tc
