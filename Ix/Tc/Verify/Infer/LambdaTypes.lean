import Ix.Tc.Verify.Infer.CheapBeta
import Ix.Tc.Verify.Infer.BinderClosing
import Ix.Tc.Verify.Infer.SortTypes
import Ix.Tc.Verify.Whnf.Iota.ArgumentExecution

/-!
# Lambda inference

This module verifies the production lambda branch: optional domain-sort
validation, fresh-fvar binder opening, recursive body inference, cheap beta,
singleton abstraction, anonymous Pi reconstruction, and scoped cleanup.
-/

namespace Ix.Tc

/-- Finite closure for the anonymous Pi nodes produced from supported body
types.  The body argument ranges only over the finite run support. -/
def LambdaResultSupport (support : RunSupport) (ty : KExpr .anon) : Prop :=
  ∀ {body : KExpr .anon}, support body →
    support (KExpr.mkAll RecM.anonN RecM.anonBi ty body)

namespace RecM

/-- Infer and close the type of an already-open lambda body.  The checker
invariant remains in the tagged fvar context until `withLctxScope` returns,
while the semantic result is stated in the original de Bruijn context. -/
private theorem inferLambdaTail_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {fv : FVarId} {deps : List FVarId}
    {ty bodyOpen : KExpr .anon} {tyV bodyV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hcheap : CheapBetaResources support)
    (habstract : SingletonAbstractionResources support)
    (hresults : LambdaResultSupport support ty)
    (hcollision : support.CollisionFree)
    (htyType : world.venv.IsType uvars Delta.toCtx tyV)
    (htyTr : TrKExprS world.venv uvars world.nameOf trProj Delta ty tyV)
    (hbodySupport : support bodyOpen)
    (hbodyTr : TrKExprS world.venv uvars world.nameOf trProj
      ((some (fv, deps), .vlam tyV) :: Delta) bodyOpen bodyV) :
    RecM.WF .noAccel semantics trProj world support uvars
      ((some (fv, deps), .vlam tyV) :: Delta) s
      (do
        let bodyTy ← inferCall bodyOpen
        let bodyTy ← TcM.runIntern (cheapBetaReduce bodyTy)
        let abstracted ← TcM.runIntern (abstractFVars bodyTy #[fv])
        TcM.intern (.mkAll anonN anonBi ty abstracted))
      (fun result _ => support result ∧
        InferPost trProj world uvars Delta (.lam tyV bodyV) result) := by
  apply RecM.WF.bind
    (RecM.WF.withInv <| RecM.inferCall_wf hbodySupport hbodyTr)
  intro bodyTy afterBody hbodyPost
  rcases hbodyPost with
    ⟨hIBody, hbodyTySupport, bodyTyV, hbodyTyTr, hbodyTy⟩
  obtain ⟨bodyTyCoreV, hbodyTyCoreTr, hbodyTyEq⟩ := hbodyTyTr
  have hcheapMeaning := KExpr.cheapBetaReduceResult_meaning theory
    hIBody.2.1.wf hbodyTyCoreTr (hcheap.bounds hbodyTySupport)
  apply RecM.WF.bind
    (RecM.WF.withInv <| RecM.WF.liftTcM <|
      hcheap.whnf_wf hcollision hbodyTySupport)
  intro reduced afterCheap hcheapPost
  rcases hcheapPost with
    ⟨hICheap, rfl, hreducedSupport, _⟩
  have hreducedQ := WhnfMeaning.resultQuot theory hICheap.2.1.wf
    (⟨bodyTyCoreV, hbodyTyCoreTr, hbodyTyEq⟩ :
      TrKExpr world.venv uvars world.nameOf trProj
        ((some (fv, deps), .vlam tyV) :: Delta) bodyTy bodyTyV)
    hcheapMeaning
  obtain ⟨reducedV, hreducedTr, hreducedEq⟩ := hreducedQ
  apply RecM.WF.bind
    (RecM.WF.withInv <| RecM.WF.liftTcM <|
      habstract.close_whnf_wf hcollision hreducedSupport hreducedTr)
  intro abstracted afterAbstract habstractPost
  rcases habstractPost with
    ⟨hIAbstract, rfl, habstractedSupport, _, habstractedTr⟩
  have hresultSupport := hresults habstractedSupport
  apply RecM.WF.mono
    (RecM.WF.withInv <| RecM.WF.liftTcM <|
      TcM.intern_whnf_wf hcollision hresultSupport)
  · intro result final hresult
    rcases hresult with ⟨hIFinal, rfl, _⟩
    have hDelta : KVLCtx.WF world.venv uvars Delta :=
      hIFinal.2.1.wf.1
    have hbodyTyType : world.venv.IsType uvars
        (tyV :: Delta.toCtx) bodyTyV := by
      simpa [KVLCtx.toCtx] using
        hbodyTy.isType world.venvWF.ordered hIFinal.2.1.wf.toCtx
    have htyQ := htyTr.trKExpr world.venvWF.ordered
      theory.literalWF theory.projections.wf hDelta
    have habstractedQ : TrKExpr world.venv uvars world.nameOf trProj
        ((none, .vlam tyV) :: Delta)
        (KExpr.abstractFVarsResult
          (KExpr.cheapBetaReduceResult bodyTy) #[fv]) bodyTyV :=
      ⟨reducedV, habstractedTr, hreducedEq⟩
    have hresultTr : TrKExpr world.venv uvars world.nameOf trProj Delta
        (KExpr.mkAll anonN anonBi ty
          (KExpr.abstractFVarsResult
            (KExpr.cheapBetaReduceResult bodyTy) #[fv]))
        (.forallE tyV bodyTyV) :=
      TrKExpr.all world.venvWF theory.literalWF theory.projections
        hDelta htyType hbodyTyType htyQ habstractedQ
    obtain ⟨u, htySort⟩ := htyType
    have hbodyTy' : world.venv.HasType uvars
        (tyV :: Delta.toCtx) bodyV bodyTyV := by
      simpa [KVLCtx.toCtx] using hbodyTy
    exact ⟨hresultSupport, .forallE tyV bodyTyV, hresultTr,
      Lean4Lean.VEnv.HasType.lam htySort hbodyTy'⟩
  · intro _ _ _
    trivial

/-- Scope the shared lambda tail through the production binder-opening
helper.  Factoring this once avoids elaborating the large callback contract
independently in the full and infer-only dispatcher paths. -/
private theorem inferLambdaScoped_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body : KExpr .anon} {tyV bodyV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hcheap : CheapBetaResources support)
    (habstract : SingletonAbstractionResources support)
    (hresults : LambdaResultSupport support ty)
    (hcollision : support.CollisionFree)
    (htyType : world.venv.IsType uvars Delta.toCtx tyV)
    (htyTr : TrKExprS world.venv uvars world.nameOf trProj Delta ty tyV)
    (hbodyTr : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam tyV) :: Delta) body bodyV)
    (hbinder : BinderOpeningResources support name body) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (withLctxScope do
        let (bodyOpen, fv) ← TcM.openBinder name bi ty body
        let bodyTy ← inferCall bodyOpen
        let bodyTy ← TcM.runIntern (cheapBetaReduce bodyTy)
        let abstracted ← TcM.runIntern (abstractFVars bodyTy #[fv])
        TcM.intern (.mkAll anonN anonBi ty abstracted))
      (fun result _ => support result ∧
        InferPost trProj world uvars Delta (.lam tyV bodyV) result) := by
  apply RecM.withLctxScope_openBinder_wf
    (layer := .noAccel) (semantics := semantics) (trProj := trProj)
    (world := world) (uvars := uvars) (Delta := Delta) (s := s)
    (bi := bi)
    (k := fun bodyOpen fv => do
      let bodyTy ← inferCall bodyOpen
      let bodyTy ← TcM.runIntern (cheapBetaReduce bodyTy)
      let abstracted ← TcM.runIntern (abstractFVars bodyTy #[fv])
      TcM.intern (.mkAll anonN anonBi ty abstracted))
    (Qinner := fun result _ => support result ∧
      InferPost trProj world uvars Delta (.lam tyV bodyV) result)
    (Qouter := fun result _ => support result ∧
      InferPost trProj world uvars Delta (.lam tyV bodyV) result)
    htyTr htyType hbodyTr hcollision hbinder
  · intro bodyOpen fv after hfv hbodyEq hbodyOpenSupport hbodyOpenTr
    subst fv
    exact inferLambdaTail_wf
      (semantics := semantics) (trProj := trProj) (world := world)
      (support := support) (uvars := uvars) (Delta := Delta)
      (s := after) (fv := ⟨s.env.nextFVarId⟩) (deps := Delta.fvars)
      (ty := ty) (tyV := tyV) (bodyV := bodyV)
      theory hcheap habstract hresults hcollision htyType htyTr
      hbodyOpenSupport hbodyOpenTr
  · intro result after hresult
    exact hresult

/- Complete production lambda branch.  Full mode validates the domain as a
type; infer-only mode skips that validation.  Both paths use the same
fresh-fvar opening, semantic closing, and anonymous Pi result. -/
theorem inferUncached_lam_wf
    {alpha : Type} {initial : TcState .anon}
    {program : TcM .anon alpha} {requests : List WalkerRequest}
    {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {uvars : Nat} {Delta : KVLCtx}
    {s : TcState .anon} {inferOnly : Bool}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body : KExpr .anon} {info : ExprInfo .anon}
    {sourceV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hsorts : SortComponentResources support)
    (hcheap : CheapBetaResources support)
    (habstract : SingletonAbstractionResources support)
    (hresults : LambdaResultSupport support ty)
    (htySupport : support ty)
    (hbinder : BinderOpeningResources support name body)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.lam name bi ty body info) sourceV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (inferUncached inferCall inferOnly (.lam name bi ty body info))
      (fun result _ => support result ∧
        InferPost trProj world uvars Delta sourceV result) := by
  cases hsource with
  | lam htyType htyTr hbodyTr =>
      rename_i tyV bodyV
      cases inferOnly with
      | false =>
          unfold inferUncached
          simp only [Bool.not_false, if_true]
          apply RecM.WF.bind
            (RecM.WF.withInv <| RecM.inferCall_wf htySupport htyTr)
          intro tyTy afterTy htyPost
          rcases htyPost with
            ⟨_, htyTySupport, tyTyV, htyTyTr, _⟩
          apply RecM.WF.bind
            (RecM.WF.withInv <|
              RecM.ensureSortDirect_wf hwhnf hsorts htyTySupport htyTyTr)
          intro _ afterSort hsortPost
          rcases hsortPost with ⟨hISort, _⟩
          exact inferLambdaScoped_wf
            (semantics := semantics) (trProj := trProj) (world := world)
            (support := support) (uvars := uvars) (Delta := Delta)
            (s := afterSort) theory hcheap habstract hresults
            hrun.collisionFree htyType htyTr hbodyTr hbinder
      | true =>
          unfold inferUncached
          simp only [Bool.not_true]
          exact inferLambdaScoped_wf
            (semantics := semantics) (trProj := trProj) (world := world)
            (support := support) (uvars := uvars) (Delta := Delta)
            (s := s) theory hcheap habstract hresults hrun.collisionFree
            htyType htyTr hbodyTr hbinder

end RecM

end Ix.Tc
