import Ix.Tc.Verify.Infer.FunctionTypes
import Ix.Tc.Verify.Whnf.Beta.LambdaInstantiation

/-!
# Application inference

Application inference is the first dispatcher branch that composes all three
recursive services: inference of the function and (in full mode) argument,
direct WHNF exposure of the inferred function type, and DefEq validation of
the argument type.  The final dependent codomain is produced by the verified
single-substitution walker.

The run support is finite and deliberately not constructor-closed.  The
application census below therefore records both source-component descent and
the exact family of substitution requests reachable after a supported
codomain has been exposed.
-/

namespace Ix.Tc

/-- Finite-support obligations for supported applications that reach the
uncached inference dispatcher.  Quantifying the final clause over supported
codomains is still finite, and avoids pretending that every possible WHNF
result belongs to the run. -/
def ApplicationInferCensus (support : RunSupport)
    (requests : List WalkerRequest) : Prop :=
  forall {f a : KExpr .anon} {info : ExprInfo .anon},
    support (.app f a info) ->
      support f /\ support a /\
        forall {cod}, support cod ->
          WalkerRequest.subst cod a 0 ∈ requests

namespace TcM

/-- `isEagerReduce` observes the application spine and primitive table but
does not mutate the checker state. -/
theorem isEagerReduce_wf {I : TcState .anon -> Prop}
    (e : KExpr .anon) (s : TcState .anon) :
    TcM.WF I s (TcM.isEagerReduce e) (fun _ after => after = s) := by
  intro hI
  rcases hspine : e.collectSpine with ⟨head, args⟩
  cases hsize : args.size != 2 <;>
    cases head <;>
    simp [TcM.isEagerReduce, hspine, hsize, hI]
  change I s /\ s = s
  exact ⟨hI, rfl⟩

end TcM

namespace RecM

/-- Updating the eager-reduction marker changes only operational
bookkeeping.  In particular, an error returned by the following DefEq call
may retain the marker without invalidating the semantic state invariant. -/
theorem setEagerReduce_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon} (value : Bool) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (modify fun state => { state with eagerReduce := value })
      (fun _ _ => True) :=
  RecM.WF.modify
    (fun hI => hI.of_semantic_fields_eq rfl rfl rfl rfl rfl rfl rfl rfl)
    (fun _ => trivial)

/-- Theory meaning of the substitution returned by application inference.
Translation uniqueness reconciles the recursively inferred function type
with the Pi already present in the source application's structural typing.
Pi injectivity then aligns the exposed domain and codomain. -/
private theorem applicationResult
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Delta : KVLCtx}
    (theory : WhnfTheory trProj world uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    {a cod : KExpr .anon}
    {fV aV A B fTyV domV codV : Lean4Lean.VExpr}
    (hfun : world.venv.HasType uvars Delta.toCtx fV (.forallE A B))
    (harg : world.venv.HasType uvars Delta.toCtx aV A)
    (hargTr : TrKExprS world.venv uvars world.nameOf trProj Delta a aV)
    (hfTy : world.venv.HasType uvars Delta.toCtx fV fTyV)
    (hview : world.venv.IsDefEqU uvars Delta.toCtx fTyV
      (.forallE domV codV))
    (hcodTr : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam domV) :: Delta) cod codV)
    (hbounds : WalkerRequest.Bounds (.subst cod a 0)) :
    InferPost trProj world uvars Delta (.app fV aV)
      (KExpr.substSpec cod a 0) := by
  have hfTyEq : world.venv.IsDefEqU uvars Delta.toCtx fTyV
      (.forallE A B) :=
    hfTy.uniqU world.venvWF hDelta hfun
  have hforallEq : world.venv.IsDefEqU uvars Delta.toCtx
      (.forallE A B) (.forallE domV codV) :=
    hfTyEq.symm.trans world.venvWF hDelta hview
  have hdomainEq : world.venv.IsDefEqU uvars Delta.toCtx A domV :=
    let ⟨level, hEq⟩ :=
      (hforallEq.forallE_inv world.venvWF hDelta.toCtx).1
    ⟨.sort level, hEq⟩
  have hcodEq : world.venv.IsDefEqU uvars (A :: Delta.toCtx) B codV :=
    let ⟨level, hEq⟩ :=
      (hforallEq.forallE_inv world.venvWF hDelta.toCtx).2
    ⟨.sort level, hEq⟩
  have hargAtDom : world.venv.HasType uvars Delta.toCtx aV domV :=
    harg.defeqU_r world.venvWF hDelta hdomainEq
  have hresultTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.substSpec cod a 0) (codV.inst aV) :=
    TrKExprS.instN_lbr world.venvWF.ordered theory.projections.weakN
      theory.projections.instN hbounds.2.1 hargTr hargAtDom hcodTr
        (.zero : KVLCtx.KInstN Delta aV domV 0 0
          ((none, .vlam domV) :: Delta) Delta)
        rfl hbounds.2.2.2.2
  have hcodInstEq : world.venv.IsDefEqU uvars Delta.toCtx
      (B.inst aV) (codV.inst aV) :=
    hcodEq.instN world.venvWF.ordered .zero harg
  refine ⟨codV.inst aV, ?_, ?_⟩
  · exact hresultTr.trKExpr world.venvWF.ordered theory.literalWF
      theory.projections.wf hDelta
  · exact (Lean4Lean.VEnv.HasType.app hfun harg).defeqU_r
      world.venvWF hDelta hcodInstEq

/-- Execute the final substitution and package its support and Theory
meaning.  This helper is shared by full and infer-only application paths. -/
private theorem finishApplication_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {uvars : Nat} {Delta : KVLCtx}
    {s : TcState .anon}
    (theory : WhnfTheory trProj world uvars)
    {a cod : KExpr .anon}
    {fV aV A B fTyV domV codV : Lean4Lean.VExpr}
    (hfun : world.venv.HasType uvars Delta.toCtx fV (.forallE A B))
    (harg : world.venv.HasType uvars Delta.toCtx aV A)
    (hargTr : TrKExprS world.venv uvars world.nameOf trProj Delta a aV)
    (hfTy : world.venv.HasType uvars Delta.toCtx fV fTyV)
    (hview : world.venv.IsDefEqU uvars Delta.toCtx fTyV
      (.forallE domV codV))
    (hcodTr : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam domV) :: Delta) cod codV)
    (hmem : WalkerRequest.subst cod a 0 ∈ requests) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (liftM (TcM.runIntern (subst cod a 0)))
      (fun result _ => support result /\
        InferPost trProj world uvars Delta (.app fV aV) result) := by
  apply RecM.WF.mono
    (RecM.WF.withInv <| RecM.WF.liftTcM <|
      hrun.subst_whnf_wf hmem)
  · intro result final hresult
    rcases hresult with ⟨hIfinal, rfl, _⟩
    have hresultSupport : support (KExpr.substSpec cod a 0) :=
      hrun.coverage.subst hmem _ (KExpr.SubstReach.spec a cod 0)
    exact ⟨hresultSupport,
      applicationResult theory hIfinal.2.1.wf hfun harg hargTr hfTy
        hview hcodTr (hrun.requestBounds hmem)⟩
  · intro _ _ _
    trivial

/-- The complete application branch of the uncached syntax dispatcher.
Full mode validates the inferred argument type, including the production
eager-reduction marker protocol.  Infer-only mode skips those callbacks but
returns the same substitution-backed semantic type. -/
theorem inferUncached_app_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {uvars : Nat} {Delta : KVLCtx}
    {s : TcState .anon} {inferOnly : Bool}
    {f a : KExpr .anon} {info : ExprInfo .anon}
    {sourceV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hcomponents : ForallComponentSupport support)
    (hcensus : ApplicationInferCensus support requests)
    (hsourceSupport : support (.app f a info))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.app f a info) sourceV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (inferUncached inferCall inferOnly (.app f a info))
      (fun ty _ => support ty /\
        InferPost trProj world uvars Delta sourceV ty) := by
  cases hsource with
  | app hfun harg hfunTr hargTr =>
      rename_i fV aV A B
      obtain ⟨hfunSupport, hargSupport, hsubst⟩ :=
        hcensus hsourceSupport
      cases inferOnly with
      | false =>
          unfold inferUncached
          simp only [Bool.not_false, if_true]
          apply RecM.WF.bind
            (RecM.WF.withInv <| RecM.inferCall_wf hfunSupport hfunTr)
          intro fTy afterFun hfunPost
          rcases hfunPost with
            ⟨_, hfTySupport, fTyV, hfTyTr, hfTy⟩
          apply RecM.WF.bind
            (RecM.WF.withInv <|
              RecM.ensureForallDirect_wf hwhnf hcomponents hfTySupport
                hfTyTr)
          intro exposed afterForall hforallPost
          rcases exposed with ⟨dom, cod⟩
          rcases hforallPost with
            ⟨_, domV, codV, hdomSupport, hcodSupport, _, _, hdomTr,
              hcodTr, hview⟩
          apply RecM.WF.bind
            (RecM.WF.withInv <| RecM.inferCall_wf hargSupport hargTr)
          intro aTy afterArg hargPost
          rcases hargPost with
            ⟨_, haTySupport, aTyV, haTyTr, _⟩
          obtain ⟨aTyCoreV, haTyCoreTr, _⟩ := haTyTr
          apply RecM.WF.bind
            (RecM.WF.withInv <| RecM.WF.liftTcM <|
              TcM.isEagerReduce_wf a afterArg)
          intro eager afterEager heager
          rcases heager with ⟨_, rfl⟩
          cases eager with
          | false =>
              simp only [Bool.false_eq_true, if_false]
              apply RecM.WF.bind
                (RecM.isDefEqCall_wf haTySupport hdomSupport
                  haTyCoreTr hdomTr)
              intro equal afterEq _
              cases equal with
              | false =>
                  simp only [Bool.not_false, if_true, pure_bind]
                  apply RecM.WF.bind
                    (Q₁ := fun read state => read = state)
                    (RecM.WF.get fun _ => rfl)
                  intro read state _
                  apply RecM.WF.bind
                    (Q₁ := fun _ _ => False)
                    (RecM.WF.throw fun _ => trivial)
                  intro _ _ impossible
                  exact impossible.elim
              | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, if_false]
                  exact finishApplication_wf hrun theory hfun harg hargTr
                    hfTy hview hcodTr (hsubst hcodSupport)
          | true =>
              simp only [if_true]
              apply RecM.WF.bind (RecM.setEagerReduce_wf true)
              intro _ afterSet _
              apply RecM.WF.bind
                (RecM.isDefEqCall_wf haTySupport hdomSupport
                  haTyCoreTr hdomTr)
              intro equal afterEq _
              apply RecM.WF.bind (RecM.setEagerReduce_wf false)
              intro _ afterReset _
              cases equal with
              | false =>
                  simp only [Bool.not_false, if_true, pure_bind]
                  apply RecM.WF.bind
                    (Q₁ := fun read state => read = state)
                    (RecM.WF.get fun _ => rfl)
                  intro read state _
                  apply RecM.WF.bind
                    (Q₁ := fun _ _ => False)
                    (RecM.WF.throw fun _ => trivial)
                  intro _ _ impossible
                  exact impossible.elim
              | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, if_false]
                  exact finishApplication_wf hrun theory hfun harg hargTr
                    hfTy hview hcodTr (hsubst hcodSupport)
      | true =>
          unfold inferUncached
          simp only [Bool.not_true, Bool.false_eq_true, if_false]
          apply RecM.WF.bind
            (RecM.WF.withInv <| RecM.inferCall_wf hfunSupport hfunTr)
          intro fTy afterFun hfunPost
          rcases hfunPost with
            ⟨_, hfTySupport, fTyV, hfTyTr, hfTy⟩
          apply RecM.WF.bind
            (RecM.WF.withInv <|
              RecM.ensureForallDirect_wf hwhnf hcomponents hfTySupport
                hfTyTr)
          intro exposed afterForall hforallPost
          rcases exposed with ⟨dom, cod⟩
          rcases hforallPost with
            ⟨_, domV, codV, _, hcodSupport, _, _, _, hcodTr, hview⟩
          exact finishApplication_wf hrun theory hfun harg hargTr hfTy
            hview hcodTr (hsubst hcodSupport)

end RecM

end Ix.Tc
