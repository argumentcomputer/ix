import Ix.Tc.Verify.Whnf.NoDelta.StringPrimitive

/-!
# Projection-definition no-delta field

`tryReduceProjectionDefinition` recognizes a loaded reducible definition whose
body is exactly a lambda telescope ending in a projection.  A hit constructs
the projection node and then rebuilds every application after the wrapper's
arity.

This slice keeps those two generated-node obligations finite and explicit.
The initial projection and every intermediate suffix application must be in
the run support; support for only the final expression is not enough to make
the intern-table collision argument sound.
-/

namespace Ix.Tc

/-- Finite request plan for a recognized projection-wrapper definition.

The indices are the exact values returned by `collectSpine` and
`projectionDefinitionInfo`, so the plan covers production's initial `prj`
intern and precisely the suffix beginning at `arity`. -/
structure ProjectionDefinitionRequestCensus
    (requests : List WalkerRequest) (support : RunSupport) : Prop where
  reduce : ∀ {source head : KExpr .anon}
      {args : Array (KExpr .anon)} {id : KId .anon}
      {us : Array (KUniv .anon)} {headInfo : ExprInfo .anon}
      {val : KExpr .anon} {arity : Nat} {structId : KId .anon}
      {field : UInt64} {structArgIdx : Nat},
    support source →
    source.collectSpine = (head, args) →
    head = .const id us headInfo →
    projectionDefinitionInfo val =
      some (arity, structId, field, structArgIdx) →
    ¬ args.size < arity →
    let base := KExpr.mkPrj structId field args[structArgIdx]!
    support base ∧
      ∃ final, RecM.FinishAppRequests requests
        (args.extract arity args.size).toList base final

/-- Semantic authority for an observed successful projection-wrapper
rewrite.  It owns no state or support claim: ProjectionDefinition proves those from the actual
lazy lookup and finite intern plan.  A later admission refinement constructs
this boundary from the loaded definition translation and projection rule. -/
structure ProjectionDefinitionReflection (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) : Prop where
  success : ∀ {uvars : Nat} {Delta : KVLCtx}
      {methods : Methods .anon} {source result : KExpr .anon}
      {sourceV : Lean4Lean.VExpr} {s sf : TcState .anon},
    Methods.WFAt .noAccel semantics trProj world support uvars methods →
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    WhnfStateInv .noAccel semantics trProj world support uvars Delta s →
    (RecM.tryReduceProjectionDefinition source).run methods s =
      .ok (some result) sf →
    WhnfMeaning trProj world uvars Delta source result

namespace RecM

set_option maxHeartbeats 800000

/-- The suffix loop embedded in the projection-definition helper is exactly
the shared production application finisher. -/
theorem projectionDefinitionFinish_eq (base : KExpr m)
    (args : Array (KExpr m)) (arity : Nat) :
    (forIn (args.extract arity args.size) base fun arg result => do
      let result ← TcM.intern (KExpr.mkApp result arg)
      pure (.yield result) : RecM m (KExpr m)) =
      finishAppResult base args arity := by
  rw [finishAppResult_eq_foldlM]
  simp [Array.forIn_yield_eq_foldlM]

/-- Execute a finite suffix plan as a `RecM.WF` contract. -/
theorem FinishAppRequests.finishAppResult_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {uvars : Nat} {Delta : KVLCtx}
    {args : Array (KExpr .anon)} {consumed : Nat}
    {base final : KExpr .anon} {s : TcState .anon}
    (plan : FinishAppRequests requests
      (args.extract consumed args.size).toList base final)
    (hbase : support base) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (finishAppResult base args consumed)
      (fun actual _ => actual = final ∧ support actual) := by
  intro methods hmethods hI
  obtain ⟨sf, hrunFinish, hIf, _⟩ := plan.eval hrun hI
  rw [hrunFinish]
  exact ⟨hIf, rfl, plan.support hrun hbase⟩

/-- State and generated-result closure of the production projection-wrapper
helper, including lazy-ingress errors and every intern in the suffix fold. -/
theorem tryReduceProjectionDefinition_inv_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : ProjectionDefinitionRequestCensus requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {uvars : Nat} {Delta : KVLCtx}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    {source : KExpr .anon} {s : TcState .anon}
    (hsourceSupport : support source) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryReduceProjectionDefinition source)
      (fun result _ => match result with
        | none => True
        | some reduced => support reduced) := by
  unfold tryReduceProjectionDefinition
  generalize hspine : source.collectSpine = spine
  rcases spine with ⟨head, args⟩
  cases head with
  | const id us headInfo =>
      simp only [pure_bind]
      apply RecM.WF.bind <| RecM.WF.withInv <| RecM.WF.liftTcM <|
        TcM.tryGetConst_wf hfault id s
      intro entry afterLookup hlookup
      rcases hlookup with ⟨hILookup, _⟩
      cases entry with
      | none =>
          simp only
          exact RecM.WF.pure fun _ => trivial
      | some entry =>
          cases entry with
          | defn name levelParams kind safety hints lvls ty val leanAll block =>
              cases kind with
              | defn =>
                  simp only
                  cases hinfo : projectionDefinitionInfo val with
                  | none =>
                      simp only
                      exact RecM.WF.pure fun _ => trivial
                  | some info =>
                      rcases info with
                        ⟨arity, structId, field, structArgIdx⟩
                      simp only
                      by_cases hsmall : args.size < arity
                      · simp only [hsmall, if_pos]
                        exact RecM.WF.pure fun _ => trivial
                      · simp only [hsmall, if_false]
                        let base : KExpr .anon :=
                          KExpr.mkPrj structId field args[structArgIdx]!
                        obtain ⟨hbase, final, plan⟩ :=
                          census.reduce hsourceSupport hspine rfl hinfo
                            hsmall
                        apply RecM.WF.bind <| RecM.WF.liftTcM <|
                          TcM.intern_whnf_wf hrun.collisionFree hbase
                        intro actualBase afterBase hactualBase
                        have hactualBaseEq : actualBase = base :=
                          hactualBase.1
                        subst actualBase
                        rw [projectionDefinitionFinish_eq]
                        apply RecM.WF.bind
                          (plan.finishAppResult_wf hrun hbase)
                        intro actualFinal afterFinal hactualFinal
                        rcases hactualFinal with
                          ⟨hactualFinalEq, hfinalSupport⟩
                        subst actualFinal
                        exact RecM.WF.pure fun _ => hfinalSupport
              | opaq | thm =>
                  simp only
                  exact RecM.WF.pure fun _ => trivial
          | recr | axio | quot | indc | ctor =>
              simp only
              exact RecM.WF.pure fun _ => trivial
  | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
      simp only
      exact RecM.WF.pure fun _ => trivial

/-- Complete optional-reducer field: all operational state and support facts
come from the finite plan; only a successful hit consults semantic
reflection. -/
theorem tryReduceProjectionDefinition_optional_wf_of_contexts
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (census : ProjectionDefinitionRequestCensus requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld}
    (hfault : ∀ {uvars : Nat} {Delta : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    (reflection : ProjectionDefinitionReflection semantics trProj world
      support) :
    OptionalReduction.WF .noAccel semantics trProj world support
      tryReduceProjectionDefinition := by
  intro uvars Delta source sourceV s hsourceSupport hsource
  have hstate :=
    tryReduceProjectionDefinition_inv_wf hrun census
      (hfault (uvars := uvars) (Delta := Delta))
      (semantics := semantics) (trProj := trProj) (world := world)
      (s := s) hsourceSupport
  intro methods hmethods hI
  have hpost := hstate methods hmethods hI
  match hrunProjection :
      (tryReduceProjectionDefinition source).run methods s with
  | .error err sf =>
      rw [hrunProjection] at hpost
      exact ⟨hpost.1, trivial⟩
  | .ok none sf =>
      rw [hrunProjection] at hpost
      exact ⟨hpost.1, trivial⟩
  | .ok (some result) sf =>
      rw [hrunProjection] at hpost
      exact ⟨hpost.1, hpost.2,
        reflection.success hmethods hsourceSupport hsource hI
          hrunProjection⟩

end RecM
end Ix.Tc
