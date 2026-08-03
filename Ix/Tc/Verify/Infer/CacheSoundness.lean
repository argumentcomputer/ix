import Ix.Tc.Verify.Infer.Dispatcher

/-!
# Inference cache soundness

This module closes the production `inferWith` shell around the exhaustive
uncached dispatcher.  Cache hits are accepted only through canonical K2
provenance.  Cache misses build new provenance from the exact key execution,
finite expression collision freedom, suffix transport, and the concrete
uncached typing result before mutating either cache partition.
-/

namespace Ix.Tc

namespace TcM

/-- A joint K2 suffix model turns the actual inference-key execution into the
same operational match used to validate both hits and writes. -/
theorem inferKey_model_matches_wf
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixModel trProj world)
    {Delta : KVLCtx} {source : KExpr .anon} {s : TcState .anon} :
    TcM.WF
      (WhnfStateInv layer (kernelCacheSemantics model.keys trProj) trProj
        world support model.keys.uvars Delta) s
      (TcM.inferKey source)
      (fun key s' =>
        model.keys.Matches trProj world s Delta source key /\
          ContextKeyFrame s s') := by
  simpa using
    (TcM.whnfKey_matches_wf
      (layer := layer) (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (keys := model.keys) (Δ := Delta) (source := source) (s := s)
      (fun _ _ hctx hrun => model.represents hctx hrun))

end TcM

namespace UncachedInference.Context

/-- Every direct constant root of a newly inferred cache entry is trusted:
source witnesses and the concrete result both lie in the finite run support. -/
private theorem cacheReferences
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world}
    (context : UncachedInference.Context initial program requests
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars)
    {kind : ExprCacheKind} {key : Address × Address} {ty : KExpr .anon}
    (hty : support ty) :
    (CacheEntry.expr kind key ty).ReferencesAuthorized
      (CacheAuthority.stable world) support := by
  intro id href
  apply Or.inl
  rcases href with hsource | hresult
  · obtain ⟨source, hsourceSupport, _, hsourceRef⟩ := hsource
    exact context.references hsourceSupport hsourceRef
  · exact context.references hty hresult

/-- Execute one uncached result and install it in exactly the partition
selected at `inferWith` entry.  The write occurs only after collision-robust
semantic provenance has been constructed. -/
private theorem missTail_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world}
    (context : UncachedInference.Context initial program requests
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars)
    {Delta : KVLCtx} {before s : TcState .anon} {inferOnly : Bool}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    {key : Address × Address}
    (hmatch : model.keys.Matches trProj world before Delta source key)
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta
      source sourceV) :
    RecM.WF .noAccel (kernelCacheSemantics model.keys trProj) trProj world
      support model.keys.uvars Delta s
      (do
        let ty ← RecM.inferUncached RecM.inferCall inferOnly source
        RecM.cacheInferResult inferOnly key ty
        pure ty)
      (fun result _ => support result /\
        InferPost trProj world model.keys.uvars Delta sourceV result) := by
  cases inferOnly with
  | false =>
      apply RecM.WF.bind
        (RecM.WF.withInv <|
          RecM.inferUncached_wf context hsourceSupport hsource)
      intro ty afterBody hbody
      rcases hbody with ⟨_, hty, hpost⟩
      have hprovenance := model.inferProvenance
        context.projection.run.collisionFree .infer hsourceSupport hty hmatch
        (InferMeaning.of_post hsource hpost)
        (context.cacheReferences hty)
      apply RecM.WF.bind
        (RecM.cacheInferResult_full_wf hprovenance)
      intro _ afterWrite _
      exact RecM.WF.pure fun _ => ⟨hty, hpost⟩
  | true =>
      apply RecM.WF.bind
        (RecM.WF.withInv <|
          RecM.inferUncached_wf context hsourceSupport hsource)
      intro ty afterBody hbody
      rcases hbody with ⟨_, hty, hpost⟩
      have hprovenance := model.inferProvenance
        context.projection.run.collisionFree .inferOnly hsourceSupport hty
        hmatch (InferMeaning.of_post hsource hpost)
        (context.cacheReferences hty)
      apply RecM.WF.bind
        (RecM.cacheInferResult_inferOnly_wf hprovenance)
      intro _ afterWrite _
      exact RecM.WF.pure fun _ => ⟨hty, hpost⟩

end UncachedInference.Context

namespace RecM

/-- Complete production inference entry point: key errors preserve the
invariant, full-cache hits are accepted in either policy, infer-only hits are
accepted only under the captured infer-only policy, and both miss paths write
only provenance-certified results to their respective partitions. -/
theorem inferWith_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world}
    (context : UncachedInference.Context initial program requests
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars)
    {Delta : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta
      source sourceV) :
    RecM.WF .noAccel (kernelCacheSemantics model.keys trProj) trProj world
      support model.keys.uvars Delta s (inferWith inferCall source)
      (fun result _ => support result /\
        InferPost trProj world model.keys.uvars Delta sourceV result) := by
  unfold inferWith
  apply RecM.WF.bind
    (Q₁ := fun observed after => observed = s /\ after = s)
    (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
  intro observed after hread
  rcases hread with ⟨hObserved, hAfter⟩
  subst observed
  subst after
  apply RecM.WF.bind
    (Q₁ := fun key _ =>
      model.keys.Matches trProj world s Delta source key)
  · apply RecM.WF.liftTcM
    exact TcM.WF.mono (TcM.inferKey_model_matches_wf model)
      (fun _ _ h => h.1) (fun _ _ h => h)
  · intro key afterKey hmatch
    apply RecM.WF.bind
      (Q₁ := fun current after => current = afterKey /\ after = afterKey)
      (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
    intro current afterRead hread
    rcases hread with ⟨hCurrent, hAfterRead⟩
    subst current
    subst afterRead
    let fullFound := afterKey.env.inferCache[key]?
    cases hfullFound : fullFound with
    | some cached =>
        have hhit : afterKey.env.inferCache[key]? = some cached := by
          simpa [fullFound] using hfullFound
        simp only [hhit]
        exact RecM.WF.pure fun hI => by
          have hprovenance := hI.1.caches.hit (.infer hhit)
          have hmeaning := hprovenance.kernelInferMeaningOfMatches
            .infer hsourceSupport hmatch
          exact ⟨hprovenance.supported.2,
            hmeaning.post context.projection.theory hI.2.1.wf hsource⟩
    | none =>
        have hfullMiss : afterKey.env.inferCache[key]? = none := by
          simpa [fullFound] using hfullFound
        simp only [hfullMiss]
        cases hpolicy : s.inferOnly with
        | false =>
            simp only [Bool.false_eq_true, if_false]
            exact context.missTail_wf hmatch hsourceSupport hsource
        | true =>
            simp only [pure_bind, if_true]
            apply RecM.WF.bind
              (Q₁ := fun current after =>
                current = afterKey /\ after = afterKey)
              (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
            intro current afterInferOnlyRead hread
            rcases hread with ⟨hCurrent, hAfterRead⟩
            subst current
            subst afterInferOnlyRead
            let inferOnlyFound := afterKey.env.inferOnlyCache[key]?
            cases hinferOnlyFound : inferOnlyFound with
            | some cached =>
                have hhit : afterKey.env.inferOnlyCache[key]? = some cached := by
                  simpa [inferOnlyFound] using hinferOnlyFound
                simp only [hhit]
                exact RecM.WF.pure fun hI => by
                  have hprovenance := hI.1.caches.hit (.inferOnly hhit)
                  have hmeaning := hprovenance.kernelInferMeaningOfMatches
                    .inferOnly hsourceSupport hmatch
                  exact ⟨hprovenance.supported.2,
                    hmeaning.post context.projection.theory hI.2.1.wf hsource⟩
            | none =>
                have hmiss : afterKey.env.inferOnlyCache[key]? = none := by
                  simpa [inferOnlyFound] using hinferOnlyFound
                simp only [hmiss]
                exact context.missTail_wf hmatch hsourceSupport hsource

/-- Public inference inherits the complete `inferWith` cache contract; its
recursive edges remain tied exclusively through the caller's smaller method
table. -/
theorem infer_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world}
    (context : UncachedInference.Context initial program requests
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars)
    {Delta : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta
      source sourceV) :
    RecM.WF .noAccel (kernelCacheSemantics model.keys trProj) trProj world
      support model.keys.uvars Delta s (infer source)
      (fun result _ => support result /\
        InferPost trProj world model.keys.uvars Delta sourceV result) := by
  simpa [infer] using
    (RecM.inferWith_wf context hsourceSupport hsource)

end RecM

namespace UncachedInference.Context

/-- The inference field of one unfolded production method-table layer.  The
proof consumes only the semantic contract of the smaller table supplied by
the knot induction hypothesis. -/
theorem nextInfer_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world}
    (context : UncachedInference.Context initial program requests
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars)
    (methods : Methods .anon)
    (hmethods : Methods.WFAt .noAccel
      (kernelCacheSemantics model.keys trProj) trProj world support
      model.keys.uvars methods) :
    forall {Delta : KVLCtx} {s : TcState .anon} {source : KExpr .anon}
        {sourceV : Lean4Lean.VExpr},
      support source ->
      TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
        sourceV ->
      TcM.WF
        (WhnfStateInv .noAccel (kernelCacheSemantics model.keys trProj)
          trProj world support model.keys.uvars Delta) s
        ((RecM.infer source).run methods)
        (fun result _ => support result /\
          InferPost trProj world model.keys.uvars Delta sourceV result) := by
  intro Delta s source sourceV hsourceSupport hsource
  exact (RecM.infer_wf context hsourceSupport hsource) methods hmethods

end UncachedInference.Context

end Ix.Tc
