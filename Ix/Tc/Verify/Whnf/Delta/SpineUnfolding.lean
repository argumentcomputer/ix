import Ix.Tc.Verify.Whnf.Delta.CacheExecution

/-!
# Trusted spine-aware delta unfolding

CacheExecution verifies the cached body selected for one exact constant head.  The
first production delta helper accepts an arbitrary application, peels its
head, unfolds that head, and rebuilds every argument.  This module connects
the operational catalog hit to a declaration-specific certificate and uses
the typed spine to prove that rebuilding preserves the complete source
meaning.
-/

namespace Ix.Tc

/-- Run-scoped trusted resolution and resource bounds for every supported
reducible constant head that delta unfolding may reach.

The immutable catalog equation is repeated deliberately: it ties the
certificate to the exact concrete entry observed by `tryGetConst`.  Resource
bounds are indexed by the actual universe array at the supported head, rather
than asserted for every possible instantiation of the declaration. -/
structure TrustedDeltaCensus (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) : Prop where
  resolve : ∀ {id : KId .anon} {us : Array (KUniv .anon)}
      {info : ExprInfo .anon} {concrete : KConst .anon}
      {kind : Ix.DefKind} {lvls : UInt64} {body : KExpr .anon},
    support (.const id us info) →
    DeltaBodyShape kind lvls body concrete →
    world.catalog id = some concrete →
    kind ≠ .opaq →
    ∃ ci : Lean4Lean.VDefVal,
      TrustedDeltaBody trProj world id concrete ci kind lvls body ∧
        DeltaInstantiationResources us body

namespace WhnfMeaning

/-- Re-index a concrete reduction meaning by a caller-retained structural
translation of its source.  Structural uniqueness supplies the bridge; no
syntactic equality between Theory representatives is assumed. -/
theorem toPost
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    {Delta : KVLCtx} (hDelta : KVLCtx.WF world.venv uvars Delta)
    {source result : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (h : WhnfMeaning trProj world uvars Delta source result) :
    WhnfPost trProj world uvars Delta sourceV result := by
  apply WhnfPost.transMeaning theory hDelta
    (WhnfPost.refl hsource
      (hsource.wf world.venvWF.ordered theory.literalWF
        theory.projections.wf hDelta))
  exact h

end WhnfMeaning

namespace RecM

/-- Strengthen a checker Hoare triple with the exact successful or erroneous
execution equation. -/
private theorem delta_wf_with_run_eq
    {I : TcState .anon → Prop} {s : TcState .anon} {x : TcM .anon α}
    {Q : α → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (hx : TcM.WF I s x Q E) :
    TcM.WF I s x
      (fun value after => Q value after ∧ x s = .ok value after)
      (fun err after => E err after ∧ x s = .error err after) := by
  intro hI
  have hpost := hx hI
  cases hrun : x s with
  | ok value after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.2, rfl⟩
  | error err after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.2, rfl⟩

/-- Delta's application loop is exactly the shared, certified suffix
finisher. -/
private theorem deltaFinish_eq (base : KExpr m)
    (args : Array (KExpr m)) :
    (forIn args base fun arg result => do
      let result ← TcM.intern (KExpr.mkApp result arg)
      pure (.yield result) : RecM m (KExpr m)) =
    finishAppResult base args 0 := by
  rw [finishAppResult_eq_foldlM]
  simp [Array.forIn_yield_eq_foldlM]

/-- Complete state, support, and semantic closure for the spine-aware
production delta helper.

Every successful definition/theorem branch is resolved through
`TrustedDeltaCensus`; warm and cold body paths use CacheExecution; and the exact typed
application suffix is rebuilt through `FinishAppRequests`.  Misses and
partial errors retain the invariant through the ordinary `RecM.WF` bind
rules. -/
theorem tryDeltaUnfold_trusted_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld}
    (operational : DeltaUnfoldRequestCensus requests world support)
    (trustedCensus : TrustedDeltaCensus trProj world support)
    (theory : StableWhnfTheory trProj world keys.uvars)
    {Delta : KVLCtx}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel
        (whnfCacheSemantics keys trProj
          (unfoldCacheSemantics keys.uvars trProj fallback))
        trProj world support keys.uvars Delta))
    (hreferences : TrustedReferences world support)
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    {s : TcState .anon}
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta
      source sourceV) :
    RecM.WF .noAccel
      (whnfCacheSemantics keys trProj
        (unfoldCacheSemantics keys.uvars trProj fallback))
      trProj world support keys.uvars Delta s
      (tryDeltaUnfold source)
      (fun result _ => match result with
        | none => True
        | some reduced =>
            support reduced ∧
              WhnfMeaning trProj world keys.uvars Delta source reduced) := by
  unfold tryDeltaUnfold
  generalize hspine : source.collectSpine = spine
  rcases spine with ⟨head, args⟩
  cases head with
  | const id us headInfo =>
      have htyped := trAppSpine_of_collectSpine hsource hspine
      obtain ⟨headV, hheadTr, hsuffix⟩ := htyped.toSuffix
      simp only [pure_bind]
      apply RecM.WF.bind <| RecM.WF.withInv <| RecM.WF.liftTcM <|
        TcM.WF.mono
          (delta_wf_with_run_eq (TcM.tryGetConst_wf hfault id s))
          (fun _ _ hpost => hpost.2)
          (fun _ _ _ => trivial)
      intro entry afterLookup hlookup
      rcases hlookup with ⟨hILookup, hlookupRun⟩
      cases entry with
      | none =>
          exact RecM.WF.pure fun _ => trivial
      | some entry =>
          cases entry with
          | defn name levelParams kind safety hints lvls ty body leanAll block =>
              cases kind with
              | opaq =>
                  exact RecM.WF.pure fun _ => trivial
              | defn | thm =>
                  have hloaded :=
                    TcM.tryGetConst_success_loaded hlookupRun
                  have hcatalog :=
                    hILookup.1.core.loaded hloaded
                  obtain ⟨hheadSupport, hrequest, hfinish⟩ :=
                    operational.reduce hsourceSupport hspine rfl hcatalog
                  obtain ⟨ci, htrusted, hresources⟩ :=
                    trustedCensus.resolve hheadSupport .defn hcatalog
                      (by simp)
                  apply RecM.WF.bind <|
                    unfoldConstValue_trusted_wf hrun theory hreferences
                      htrusted hresources hheadSupport hrequest hheadTr
                  intro base afterUnfold hbase
                  obtain ⟨hbaseSupport, hbaseMeaning⟩ := hbase
                  obtain ⟨final, plan⟩ := hfinish hbaseSupport
                  have plan' : FinishAppRequests requests
                      (args.extract 0 args.size).toList base final := by
                    simpa using plan
                  rw [deltaFinish_eq base args]
                  apply RecM.WF.bind
                    (plan'.finishAppResult_wf hrun hbaseSupport)
                  intro actual afterFinish hactual
                  rcases hactual with ⟨hactualEq, hfinalSupport⟩
                  subst actual
                  apply RecM.WF.pure
                  intro hI
                  have hheadPost :=
                    hbaseMeaning.toPost theory.current hI.2.1.wf hheadTr
                  exact ⟨hfinalSupport,
                    WhnfMeaning.appHeadRebuild hI.2.1.wf hsource hsuffix
                      hheadPost plan'⟩
          | recr | axio | quot | indc | ctor =>
              exact RecM.WF.pure fun _ => trivial
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      exact RecM.WF.pure fun _ => trivial

end RecM

end Ix.Tc
