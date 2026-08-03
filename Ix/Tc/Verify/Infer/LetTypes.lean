import Ix.Tc.Verify.Infer.LetScopes
import Ix.Tc.Verify.Infer.BinderClosing
import Ix.Tc.Verify.Infer.Substitution
import Ix.Tc.Verify.Infer.CheapBeta
import Ix.Tc.Verify.Infer.SortTypes
import Ix.Tc.Verify.Whnf.Iota.ArgumentExecution

/-!
# Let inference

This module verifies domain/value validation, let-fvar opening, recursive
body inference, singleton abstraction, eager value substitution, cheap beta,
and scoped cleanup for the production `letE` branch.
-/

namespace Ix.Tc

namespace RecM

/-- Infer the type of an opened let body and eliminate the temporary let
binder from that type before returning to the outer context. -/
private theorem inferLetTail_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {fv : FVarId} {deps : List FVarId}
    {val bodyOpen : KExpr .anon}
    {tyV valV bodyV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (habstract : SingletonAbstractionResources support)
    (hsubst : SubstitutionResources support)
    (hcheap : CheapBetaResources support)
    (hcollision : support.CollisionFree)
    (hvalSupport : support val)
    (hvalTr : TrKExprS world.venv uvars world.nameOf trProj Delta val valV)
    (hbodySupport : support bodyOpen)
    (hbodyTr : TrKExprS world.venv uvars world.nameOf trProj
      ((some (fv, deps), .vlet tyV valV) :: Delta) bodyOpen bodyV) :
    RecM.WF .noAccel semantics trProj world support uvars
      ((some (fv, deps), .vlet tyV valV) :: Delta) s
      (do
        let bodyTy ← inferCall bodyOpen
        let abstracted ← TcM.runIntern (abstractFVars bodyTy #[fv])
        let result ← TcM.runIntern (subst abstracted val 0)
        TcM.runIntern (cheapBetaReduce result))
      (fun result _ => support result ∧
        InferPost trProj world uvars Delta bodyV result) := by
  apply RecM.WF.bind
    (RecM.WF.withInv <| RecM.inferCall_wf hbodySupport hbodyTr)
  intro bodyTy afterBody hbodyPost
  rcases hbodyPost with
    ⟨hIBody, hbodyTySupport, bodyTyV, hbodyTyTr, hbodyTy⟩
  obtain ⟨bodyTyCoreV, hbodyTyCoreTr, hbodyTyEq⟩ := hbodyTyTr
  apply RecM.WF.bind
    (RecM.WF.withInv <| RecM.WF.liftTcM <|
      habstract.close_whnf_wf hcollision hbodyTySupport hbodyTyCoreTr)
  intro abstracted afterAbstract habstractPost
  rcases habstractPost with
    ⟨hIAbstract, rfl, habstractedSupport, _, habstractedTr⟩
  have hsubstBounds := hsubst.bounds (depth := 0)
    habstractedSupport hvalSupport
  obtain ⟨_, hvalCon, _, _, hsubstBig⟩ := hsubstBounds
  have hsubstTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.substSpec
        (KExpr.abstractFVarsResult bodyTy #[fv]) val 0) bodyTyCoreV :=
    TrKExprS.inst_let_lbr world.venvWF.ordered
      theory.projections.weakN hvalCon habstractedTr hvalTr (by
        simpa using hsubstBig)
  apply RecM.WF.bind
    (RecM.WF.withInv <| RecM.WF.liftTcM <|
      hsubst.whnf_wf hcollision habstractedSupport hvalSupport)
  intro substituted afterSubst hsubstPost
  rcases hsubstPost with ⟨hISubst, rfl, hsubstitutedSupport, _⟩
  have hsubstitutedQ : TrKExpr world.venv uvars world.nameOf trProj Delta
      (KExpr.substSpec
        (KExpr.abstractFVarsResult bodyTy #[fv]) val 0) bodyTyV :=
    ⟨bodyTyCoreV, hsubstTr, hbodyTyEq⟩
  have hcheapMeaning := KExpr.cheapBetaReduceResult_meaning theory
    hISubst.2.1.wf.1 hsubstTr (hcheap.bounds hsubstitutedSupport)
  apply RecM.WF.mono
    (RecM.WF.withInv <| RecM.WF.liftTcM <|
      hcheap.whnf_wf hcollision hsubstitutedSupport)
  · intro result final hresult
    rcases hresult with ⟨hIFinal, rfl, hresultSupport, _⟩
    have hresultQ := WhnfMeaning.resultQuot theory hIFinal.2.1.wf.1
      hsubstitutedQ hcheapMeaning
    have hbodyTy' : world.venv.HasType uvars Delta.toCtx bodyV bodyTyV := by
      simpa [KVLCtx.toCtx] using hbodyTy
    exact ⟨hresultSupport, bodyTyV, hresultQ, hbodyTy'⟩
  · intro _ _ _
    trivial

/-- Scope the shared let tail through the production `openLet` helper. -/
private theorem inferLetScoped_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {name : Mode.anon.F Name}
    {ty val body : KExpr .anon} {tyV valV bodyV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (habstract : SingletonAbstractionResources support)
    (hsubst : SubstitutionResources support)
    (hcheap : CheapBetaResources support)
    (hcollision : support.CollisionFree)
    (hvalSupport : support val)
    (htyTr : TrKExprS world.venv uvars world.nameOf trProj Delta ty tyV)
    (hvalTr : TrKExprS world.venv uvars world.nameOf trProj Delta val valV)
    (hvalType : world.venv.HasType uvars Delta.toCtx valV tyV)
    (hbodyTr : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlet tyV valV) :: Delta) body bodyV)
    (hbinder : BinderOpeningResources support name body) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (withLctxScope do
        let (bodyOpen, fv) ← TcM.openLet name ty val body
        let bodyTy ← inferCall bodyOpen
        let abstracted ← TcM.runIntern (abstractFVars bodyTy #[fv])
        let result ← TcM.runIntern (subst abstracted val 0)
        TcM.runIntern (cheapBetaReduce result))
      (fun result _ => support result ∧
        InferPost trProj world uvars Delta bodyV result) := by
  apply RecM.withLctxScope_openLet_wf
    (layer := .noAccel) (semantics := semantics) (trProj := trProj)
    (world := world) (uvars := uvars) (Delta := Delta) (s := s)
    (k := fun bodyOpen fv => do
      let bodyTy ← inferCall bodyOpen
      let abstracted ← TcM.runIntern (abstractFVars bodyTy #[fv])
      let result ← TcM.runIntern (subst abstracted val 0)
      TcM.runIntern (cheapBetaReduce result))
    (Qinner := fun result _ => support result ∧
      InferPost trProj world uvars Delta bodyV result)
    (Qouter := fun result _ => support result ∧
      InferPost trProj world uvars Delta bodyV result)
    htyTr hvalTr hvalType hbodyTr hcollision hbinder
  · intro bodyOpen fv after hfv hbodyEq hbodyOpenSupport hbodyOpenTr
    subst fv
    exact inferLetTail_wf
      (semantics := semantics) (trProj := trProj) (world := world)
      (support := support) (uvars := uvars) (Delta := Delta)
      (s := after) (fv := ⟨s.env.nextFVarId⟩) (deps := Delta.fvars)
      (val := val) (tyV := tyV) (valV := valV)
      (bodyV := bodyV) theory habstract hsubst hcheap hcollision
      hvalSupport hvalTr hbodyOpenSupport hbodyOpenTr
  · intro result after hresult
    exact hresult

/- Complete production let branch. -/
theorem inferUncached_let_wf
    {alpha : Type} {initial : TcState .anon}
    {program : TcM .anon alpha} {requests : List WalkerRequest}
    {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {uvars : Nat} {Delta : KVLCtx}
    {s : TcState .anon} {inferOnly : Bool}
    {name : Mode.anon.F Name}
    {ty val body : KExpr .anon} {nondep : Bool} {info : ExprInfo .anon}
    {sourceV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hsorts : SortComponentResources support)
    (habstract : SingletonAbstractionResources support)
    (hsubst : SubstitutionResources support)
    (hcheap : CheapBetaResources support)
    (htySupport : support ty)
    (hvalSupport : support val)
    (hbinder : BinderOpeningResources support name body)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.letE name ty val body nondep info) sourceV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (inferUncached inferCall inferOnly
        (.letE name ty val body nondep info))
      (fun result _ => support result ∧
        InferPost trProj world uvars Delta sourceV result) := by
  cases hsource with
  | letE hvalType htyTr hvalTr hbodyTr =>
      rename_i tyV valV
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
          apply RecM.WF.bind
            (RecM.WF.withInv <| RecM.inferCall_wf hvalSupport hvalTr)
          intro valTy afterVal hvalPost
          rcases hvalPost with
            ⟨_, hvalTySupport, valTyV, hvalTyTr, _⟩
          obtain ⟨valTyCoreV, hvalTyCoreTr, _⟩ := hvalTyTr
          apply RecM.WF.bind
            (RecM.isDefEqCall_wf hvalTySupport htySupport
              hvalTyCoreTr htyTr)
          intro equal afterEq hequal
          cases equal with
          | false =>
              simp only [Bool.not_false, if_true]
              apply RecM.WF.bind
                (Q₁ := fun _ _ => False)
                (RecM.WF.throw fun _ => trivial)
              intro _ _ impossible
              exact impossible.elim
          | true =>
              simp only [Bool.not_true]
              exact inferLetScoped_wf
                (semantics := semantics) (trProj := trProj) (world := world)
                (support := support) (uvars := uvars) (Delta := Delta)
                (s := afterEq) theory habstract hsubst hcheap
                hrun.collisionFree hvalSupport htyTr hvalTr hvalType
                hbodyTr hbinder
      | true =>
          unfold inferUncached
          simp only [Bool.not_true]
          exact inferLetScoped_wf
            (semantics := semantics) (trProj := trProj) (world := world)
            (support := support) (uvars := uvars) (Delta := Delta)
            (s := s) theory habstract hsubst hcheap hrun.collisionFree
            hvalSupport htyTr hvalTr hvalType hbodyTr hbinder

end RecM

end Ix.Tc
