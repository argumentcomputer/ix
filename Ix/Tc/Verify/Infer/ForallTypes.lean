import Ix.Tc.Verify.Infer.SortTypes
import Ix.Tc.Verify.Infer.BinderScopes

/-!
# Forall inference

This module verifies the production `forall` inference branch.  It composes
recursive domain/body inference, direct sort exposure, operational binder
opening and cleanup, the simplifying universe `imax` constructor, and final
expression interning.
-/

namespace Ix.Tc

/-- Finite result closure for `forall` inference.  The premise ranges only
over the finite universe support of the run, rather than over all levels. -/
def ForallResultSupport (support : RunSupport) : Prop :=
  ∀ {u1 u2 : KUniv .anon}, support.univ u1 → support.univ u2 →
    support (KExpr.mkSort (KUniv.mkIMax u1 u2))

namespace RecM

/-- Once the binder is open, infer its body type, expose its sort, and
construct the result sort.  The semantic postcondition is already stated in
the outer context; only the state invariant remains under the tagged fvar
until `withLctxScope` closes it. -/
private theorem inferForallTail_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {fv : FVarId} {deps : List FVarId}
    {tyV bodyV input1 : Lean4Lean.VExpr} {bodyOpen : KExpr .anon}
    {u1 : KUniv .anon}
    (theory : WhnfTheory trProj world uvars)
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hresources : SortComponentResources support)
    (hresults : ForallResultSupport support)
    (hcollision : support.CollisionFree)
    (htySort : world.venv.HasType uvars Delta.toCtx tyV
      (.sort u1.toVLevel))
    (hu1 : SortView world support uvars Delta input1 u1)
    (hbodySupport : support bodyOpen)
    (hbodyTr : TrKExprS world.venv uvars world.nameOf trProj
      ((some (fv, deps), .vlam tyV) :: Delta) bodyOpen bodyV) :
    RecM.WF .noAccel semantics trProj world support uvars
      ((some (fv, deps), .vlam tyV) :: Delta) s
      (do
        let bodyTy ← inferCall bodyOpen
        let u2 ← ensureSortDirect bodyTy
        TcM.intern (.mkSort (.mkIMax u1 u2)))
      (fun result _ => support result ∧
        InferPost trProj world uvars Delta (.forallE tyV bodyV) result) := by
  apply RecM.WF.bind
    (RecM.WF.withInv <| RecM.inferCall_wf hbodySupport hbodyTr)
  intro bodyTy afterBody hbodyPost
  rcases hbodyPost with
    ⟨_, hbodyTySupport, bodyTyV, hbodyTyTr, hbodyTy⟩
  apply RecM.WF.bind
    (RecM.WF.withInv <|
      RecM.ensureSortDirect_wf hwhnf hresources hbodyTySupport hbodyTyTr)
  intro u2 afterSort hu2Post
  rcases hu2Post with ⟨hISort, hu2⟩
  have hresultSupport := hresults hu1.rootSupport hu2.rootSupport
  apply RecM.WF.mono
    (RecM.WF.withInv <| RecM.WF.liftTcM <|
      TcM.intern_whnf_wf hcollision hresultSupport)
  · intro result final hresult
    rcases hresult with ⟨hIfinal, rfl, _⟩
    refine ⟨hresultSupport,
      .sort (KUniv.mkIMax u1 u2).toVLevel, ?_, ?_⟩
    · exact (TrKExprS.sort
          (KUniv.toVLevel_mkIMax_wf hu1.levelWF hu2.levelWF)).trKExpr
        world.venvWF.ordered theory.literalWF theory.projections.wf
        hIfinal.2.1.wf.1
    · have hbodySort : world.venv.HasType uvars
          (tyV :: Delta.toCtx) bodyV (.sort u2.toVLevel) := by
        simpa [KVLCtx.toCtx] using
          hbodyTy.defeqU_r world.venvWF hIfinal.2.1.wf hu2.inputEq
      have hforall : world.venv.HasType uvars Delta.toCtx
          (.forallE tyV bodyV) (.sort (.imax u1.toVLevel u2.toVLevel)) :=
        Lean4Lean.VEnv.HasType.forallE htySort (by simpa using hbodySort)
      have hlevelEq := hu1.mkIMax_equiv hcollision hu2
      have hsortEq : world.venv.IsDefEqU uvars Delta.toCtx
          (.sort (.imax u1.toVLevel u2.toVLevel))
          (.sort (KUniv.mkIMax u1 u2).toVLevel) := by
        refine ⟨_, .sortDF ?_ ?_ ?_⟩
        · exact ⟨hu1.levelWF, hu2.levelWF⟩
        · exact KUniv.toVLevel_mkIMax_wf hu1.levelWF hu2.levelWF
        · exact hlevelEq.symm
      exact hforall.defeqU_r world.venvWF hIfinal.2.1.wf.1 hsortEq
  · intro _ _ _
    trivial

/-- Complete production `forall` branch.  All continuation errors are
cleaned back to the outer local context, while a successful result realizes
the Theory forall typing rule at the smart-constructor `imax`. -/
theorem inferUncached_all_wf
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
    (hresources : SortComponentResources support)
    (hresults : ForallResultSupport support)
    (htySupport : support ty)
    (hbinder : BinderOpeningResources support name body)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.all name bi ty body info) sourceV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (inferUncached inferCall inferOnly (.all name bi ty body info))
      (fun result _ => support result ∧
        InferPost trProj world uvars Delta sourceV result) := by
  cases hsource with
  | all htyType hbodyType htyTr hbodyTr =>
      rename_i tyV bodyV
      unfold inferUncached
      apply RecM.WF.bind
        (RecM.WF.withInv <| RecM.inferCall_wf htySupport htyTr)
      intro tyTy afterTy htyPost
      rcases htyPost with
        ⟨_, htyTySupport, tyTyV, htyTyTr, htyTy⟩
      apply RecM.WF.bind
        (RecM.WF.withInv <|
          RecM.ensureSortDirect_wf hwhnf hresources htyTySupport htyTyTr)
      intro u1 afterSort hu1Post
      rcases hu1Post with ⟨hISort, hu1⟩
      have htySort : world.venv.HasType uvars Delta.toCtx
          tyV (.sort u1.toVLevel) :=
        htyTy.defeqU_r world.venvWF hISort.2.1.wf.toCtx hu1.inputEq
      apply RecM.withLctxScope_openBinder_wf
        (layer := .noAccel) (semantics := semantics) (trProj := trProj)
        (world := world) (uvars := uvars) (Delta := Delta)
        (s := afterSort) (bi := bi)
        (k := fun bodyOpen _ => do
          let bodyTy ← inferCall bodyOpen
          let u2 ← ensureSortDirect bodyTy
          TcM.intern (.mkSort (.mkIMax u1 u2)))
        (Qinner := fun result _ => support result ∧
          InferPost trProj world uvars Delta (.forallE tyV bodyV) result)
        (Qouter := fun result _ => support result ∧
          InferPost trProj world uvars Delta (.forallE tyV bodyV) result)
        htyTr htyType hbodyTr hrun.collisionFree hbinder
      · intro bodyOpen fv after hfv hbodyEq hbodyOpenSupport hbodyOpenTr
        exact inferForallTail_wf theory hwhnf hresources hresults
          hrun.collisionFree htySort hu1 hbodyOpenSupport hbodyOpenTr
      · intro result after hresult
        exact hresult

end RecM

end Ix.Tc
