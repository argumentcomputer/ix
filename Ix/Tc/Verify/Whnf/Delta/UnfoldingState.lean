import Ix.Tc.Verify.Whnf.Driver.PublicReducers

/-!
# Delta unfolding state and support closure

Successful delta unfolding has three independent obligations:

* lazy constant lookup must preserve the fixed-world invariant;
* a cache miss must run a request-covered universe-instantiation walk and
  install a certified `unfoldCache` entry;
* rebuilding the original application spine must use a finite sequence of
  request-covered intern operations.

This module proves those operational obligations for the production
`deltaUnfoldOne`.  The final Theory equation remains an admission-owned
reflection field: a loaded definition-shaped catalog entry is not by itself
evidence that its body is the trusted definition installed in `VerifyWorld`.
-/

namespace Ix.Tc

/-- Collision-robust provenance for the universe-instantiated definition body
cached under the concrete constant-head address. -/
structure UnfoldCacheWriteOracle (semantics : CacheSemantics)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  write : ∀ {head result : KExpr .anon},
    support head →
    support result →
    CacheProvenance semantics (CacheAuthority.stable world) support
      (.unfold head.addr result)

/-- Finite operational plan for every reducible definition lookup reachable
from the run support.  The suffix field is quantified over any supported
unfold-cache result, so a warm hit cannot bypass the request census. -/
structure DeltaUnfoldRequestCensus
    (requests : List WalkerRequest) (world : VerifyWorld)
    (support : RunSupport) : Prop where
  reduce : ∀ {source head : KExpr .anon}
      {args : Array (KExpr .anon)} {id : KId .anon}
      {us : Array (KUniv .anon)} {headInfo : ExprInfo .anon}
      {name : Mode.anon.F Name} {levelParams : Mode.anon.F (Array Name)}
      {kind : Ix.DefKind} {safety : Ix.DefinitionSafety}
      {hints : Lean.ReducibilityHints} {lvls : UInt64}
      {ty val : KExpr .anon}
      {leanAll : Mode.anon.F (Array (KId .anon))}
      {block : KId .anon},
    support source →
    source.collectSpine = (head, args) →
    head = .const id us headInfo →
    world.catalog id =
      some (.defn name levelParams kind safety hints lvls ty val leanAll
        block) →
    support head ∧
      WalkerRequest.instUniv val us ∈ requests ∧
      ∀ {base}, support base →
        ∃ final, RecM.FinishAppRequests requests args.toList base final

/-- Semantic authority for an observed successful delta unfold.  Operational
state preservation and generated-result support are proved below; this field
asserts only the definition equation selected by the exact production run. -/
structure DeltaUnfoldReflection (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) : Prop where
  success : ∀ {uvars : Nat} {Delta : KVLCtx}
      {methods : Methods .anon} {source result : KExpr .anon}
      {sourceV : Lean4Lean.VExpr} {s sf : TcState .anon},
    Methods.WFAt .noAccel semantics trProj world support uvars methods →
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    WhnfStateInv .noAccel semantics trProj world support uvars Delta s →
    (RecM.deltaUnfoldOne source).run methods s = .ok (some result) sf →
    WhnfMeaning trProj world uvars Delta source result

namespace RecM

/-- Strengthen a checker Hoare triple with the concrete equation selected by
its actual success or error outcome. -/
private theorem wf_with_run_eq
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

/-- Delta rebuilding traverses the complete collected spine, which is the
zero-consumed specialization of the shared application finisher. -/
private theorem deltaDefinitionFinish_eq (base : KExpr m)
    (args : Array (KExpr m)) :
    (forIn args base fun arg result => do
      let result ← TcM.intern (KExpr.mkApp result arg)
      pure (.yield result) : RecM m (KExpr m)) =
    finishAppResult base args 0 := by
  rw [finishAppResult_eq_foldlM]
  simp [Array.forIn_yield_eq_foldlM]

/-- Installing a certified unfold entry changes no logical checker state and
preserves the complete WHNF invariant. -/
theorem unfoldCacheInsert_whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {key : Address} {result : KExpr .anon}
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.unfold key result)) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      {s with env := {s.env with
        unfoldCache := s.env.unfoldCache.insert key result}} := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · exact {
      core := hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
      internSupport := by simpa using hkernel.internSupport
      caches := hkernel.caches.insertUnfold hnew }
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

/-- The production `unfoldConstValue` preserves state and returns a supported
body on both warm hits and request-covered misses. -/
theorem unfoldConstValue_inv_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Delta : KVLCtx}
    (writes : UnfoldCacheWriteOracle semantics world support)
    {head val : KExpr .anon} {us : Array (KUniv .anon)}
    (hheadSupport : support head)
    (hrequest : WalkerRequest.instUniv val us ∈ requests)
    {s : TcState .anon} :
    RecM.WF layer semantics trProj world support uvars Delta s
      (unfoldConstValue head val us)
      (fun result _ => support result) := by
  unfold unfoldConstValue
  apply RecM.WF.bind
    (Q₁ := fun observed after => observed = after)
    (RecM.WF.get fun _ => rfl)
  intro observed after hread
  subst observed
  cases hcache : after.env.unfoldCache[head.addr]? with
  | some cached =>
      simp only
      exact RecM.WF.pure fun hI =>
        (hI.1.caches.hit (.unfold hcache)).supported.2
  | none =>
      simp only
      apply RecM.WF.bind <| RecM.WF.liftTcM <|
        TcM.instantiateUnivParams_whnf_wf hrun.collisionFree
          (hrun.coverage.instUniv hrequest)
      intro result afterInst hresult
      obtain ⟨_, hresultSupport⟩ := hresult
      apply RecM.WF.bind
        (Q₁ := fun _ next =>
          next =
            {afterInst with env := {afterInst.env with
              unfoldCache :=
                afterInst.env.unfoldCache.insert head.addr result}})
      · apply RecM.WF.modify
        · intro hI
          exact unfoldCacheInsert_whnfStateInv hI
            (writes.write hheadSupport hresultSupport)
        · intro _
          rfl
      · intro _ next hnext
        subst next
        exact RecM.WF.pure fun _ => hresultSupport

/-- State and finite-support closure for the first, spine-aware delta helper. -/
theorem tryDeltaUnfold_inv_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    {world : VerifyWorld}
    (hrun : RunAssumptions initial program requests support)
    (census : DeltaUnfoldRequestCensus requests world support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {uvars : Nat} {Delta : KVLCtx}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    (writes : UnfoldCacheWriteOracle semantics world support)
    {source : KExpr .anon} {s : TcState .anon}
    (hsourceSupport : support source) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryDeltaUnfold source)
      (fun result _ => match result with
        | none => True
        | some reduced => support reduced) := by
  unfold tryDeltaUnfold
  generalize hspine : source.collectSpine = spine
  rcases spine with ⟨head, args⟩
  cases head with
  | const id us headInfo =>
      simp only [pure_bind]
      apply RecM.WF.bind <| RecM.WF.withInv <| RecM.WF.liftTcM <|
        TcM.WF.mono
          (wf_with_run_eq (TcM.tryGetConst_wf hfault id s))
          (fun _ _ hpost => hpost.2)
          (fun _ _ _ => trivial)
      intro entry afterLookup hlookup
      rcases hlookup with ⟨hILookup, hlookupRun⟩
      cases entry with
      | none =>
          exact RecM.WF.pure fun _ => trivial
      | some entry =>
          cases entry with
          | defn name levelParams kind safety hints lvls ty val leanAll block =>
              cases kind with
              | opaq =>
                  exact RecM.WF.pure fun _ => trivial
              | defn | thm =>
                  have hloaded :=
                    TcM.tryGetConst_success_loaded hlookupRun
                  have hcatalog :=
                    hILookup.1.core.loaded hloaded
                  obtain ⟨hheadSupport, hrequest, hfinish⟩ :=
                    census.reduce hsourceSupport hspine rfl hcatalog
                  apply RecM.WF.bind <|
                    unfoldConstValue_inv_wf hrun writes hheadSupport hrequest
                  intro base afterUnfold hbaseSupport
                  obtain ⟨final, plan⟩ := hfinish hbaseSupport
                  have plan' : FinishAppRequests requests
                      (args.extract 0 args.size).toList base final := by
                    simpa using plan
                  rw [deltaDefinitionFinish_eq base args]
                  apply RecM.WF.bind
                    (plan'.finishAppResult_wf hrun hbaseSupport)
                  intro actual afterFinish hactual
                  rcases hactual with ⟨hactualEq, hfinalSupport⟩
                  subst actual
                  exact RecM.WF.pure fun _ => hfinalSupport
          | recr | axio | quot | indc | ctor =>
              exact RecM.WF.pure fun _ => trivial
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      exact RecM.WF.pure fun _ => trivial

/-- Complete operational closure of `deltaUnfoldOne`, including its bare-
constant fallback after a spine-aware miss. -/
theorem deltaUnfoldOne_inv_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    {world : VerifyWorld}
    (hrun : RunAssumptions initial program requests support)
    (census : DeltaUnfoldRequestCensus requests world support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {uvars : Nat} {Delta : KVLCtx}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    (writes : UnfoldCacheWriteOracle semantics world support)
    {source : KExpr .anon} {s : TcState .anon}
    (hsourceSupport : support source) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (deltaUnfoldOne source)
      (fun result _ => match result with
        | none => True
        | some reduced => support reduced) := by
  unfold deltaUnfoldOne
  apply RecM.WF.bind <|
    tryDeltaUnfold_inv_wf hrun census hfault writes hsourceSupport
  intro first afterFirst hfirst
  cases first with
  | some result =>
      simp only
      exact RecM.WF.pure fun _ => hfirst
  | none =>
      simp only [pure_bind]
      cases source with
      | const id us info =>
          apply RecM.WF.bind <| RecM.WF.withInv <| RecM.WF.liftTcM <|
            TcM.WF.mono
              (wf_with_run_eq
                (TcM.tryGetConst_wf hfault id afterFirst))
              (fun _ _ hpost => hpost.2)
              (fun _ _ _ => trivial)
          intro entry afterLookup hlookup
          rcases hlookup with ⟨hILookup, hlookupRun⟩
          cases entry with
          | none =>
              exact RecM.WF.pure fun _ => trivial
          | some entry =>
              cases entry with
              | defn name levelParams kind safety hints lvls ty val leanAll
                  block =>
                  cases kind with
                  | opaq =>
                      exact RecM.WF.pure fun _ => trivial
                  | defn | thm =>
                      have hloaded :=
                        TcM.tryGetConst_success_loaded hlookupRun
                      have hcatalog :=
                        hILookup.1.core.loaded hloaded
                      obtain ⟨hheadSupport, hrequest, _⟩ :=
                        census.reduce hsourceSupport rfl rfl hcatalog
                      apply RecM.WF.bind <|
                        unfoldConstValue_inv_wf hrun writes hheadSupport
                          hrequest
                      intro result afterUnfold hresultSupport
                      exact RecM.WF.pure fun _ => hresultSupport
              | recr | axio | quot | indc | ctor =>
                  exact RecM.WF.pure fun _ => trivial
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          exact RecM.WF.pure fun _ => trivial

/-- Complete optional-reducer contract: operational state and support facts
come from the finite plan; only an observed successful hit consults semantic
definition reflection. -/
theorem deltaUnfoldOne_optional_wf_of_contexts
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    {world : VerifyWorld}
    (hrun : RunAssumptions initial program requests support)
    (census : DeltaUnfoldRequestCensus requests world support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    (hfault : ∀ {uvars : Nat} {Delta : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    (writes : UnfoldCacheWriteOracle semantics world support)
    (reflection : DeltaUnfoldReflection semantics trProj world support) :
    OptionalReduction.WF .noAccel semantics trProj world support
      deltaUnfoldOne := by
  intro uvars Delta source sourceV s hsourceSupport hsource
  have hstate :=
    deltaUnfoldOne_inv_wf hrun census
      (hfault (uvars := uvars) (Delta := Delta)) writes
      (s := s) hsourceSupport
  intro methods hmethods hI
  have hpost := hstate methods hmethods hI
  match hrunDelta : (deltaUnfoldOne source).run methods s with
  | .error err sf =>
      rw [hrunDelta] at hpost
      exact ⟨hpost.1, trivial⟩
  | .ok none sf =>
      rw [hrunDelta] at hpost
      exact ⟨hpost.1, trivial⟩
  | .ok (some result) sf =>
      rw [hrunDelta] at hpost
      exact ⟨hpost.1, hpost.2,
        reflection.success hmethods hsourceSupport hsource hI hrunDelta⟩

end RecM
end Ix.Tc
