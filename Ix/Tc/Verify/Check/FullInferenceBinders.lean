import Ix.Tc.Verify.Check.BinderRoundTrip
import Ix.Tc.Verify.Check.FullInferenceApplications
import Ix.Tc.Verify.Infer.ForallTypes
import Ix.Tc.Verify.Infer.LambdaTypes
import Ix.Tc.Verify.Infer.LetTypes

/-!
# Full inference for binding forms

K2's lambda and forall proofs assume the complete source translation is
already typed.  These K3 branches instead start from `PreTrKExprS`, validate
the domain, infer the freshly opened body, and close its newly established
typed translation back to the original de Bruijn syntax.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Full-inference lambda tail after the source binder has been opened. -/
private theorem inferLambdaFullTail_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {fv : FVarId} {name : Mode.anon.F Name}
    {bi : Mode.anon.F Lean.BinderInfo}
    {ty body bodyOpen : KExpr .anon} {info : ExprInfo .anon}
    {tyV bodyV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (callbacks : FullInferenceStepContext semantics trProj world support
      uvars methods)
    (hcheap : CheapBetaResources support)
    (habstract : SingletonAbstractionResources support)
    (hresults : LambdaResultSupport support ty)
    (hcollision : support.CollisionFree)
    (htyType : world.venv.IsType uvars Delta.toCtx tyV)
    (htyTr : TrKExprS world.venv uvars world.nameOf trProj Delta ty tyV)
    (hbodyPre : PreTrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam tyV) :: Delta) body bodyV)
    (hbinder : BinderOpeningResources support name body)
    (hbodyEq : bodyOpen = KExpr.instantiateRevSpec body
      #[.mkFVar fv name] 0)
    (hfresh : fv ∉ Delta.fvars)
    (hbodySupport : support bodyOpen)
    (hbodyOpenPre : PreTrKExprS world.venv uvars world.nameOf trProj
      ((some (fv, Delta.fvars), .vlam tyV) :: Delta) bodyOpen bodyV)
    (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars
        ((some (fv, Delta.fvars), .vlam tyV) :: Delta)) s
      ((do
        let bodyTy ← inferCall bodyOpen
        let bodyTy ← TcM.runIntern (cheapBetaReduce bodyTy)
        let abstracted ← TcM.runIntern (abstractFVars bodyTy #[fv])
        TcM.intern (.mkAll anonN anonBi ty abstracted)).run methods)
      (fun result after =>
        after.inferOnly = false ∧
          FullInferPost trProj world support uvars Delta
            (.lam name bi ty body info) (.lam tyV bodyV) result)
      (fun _ after => after.inferOnly = false) := by
  simp only [ReaderT.run_bind, inferCall, ReaderT.run_monadLift]
  apply TcM.WF.bind
    (TcM.WF.withInv <| callbacks.infer hpolicy hbodySupport hbodyOpenPre)
  intro bodyTy afterBody hbodyPost
  rcases hbodyPost with
    ⟨hIBody, hpolicyBody, hbodyTySupport, hbodyOpenTr,
      bodyTyV, hbodyTyTr, hbodyTy⟩
  have hbodyAbsent : body.FVarAbsent fv :=
    hbodyPre.fvarAbsent (by simpa using hfresh)
  have hbodyTr : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam tyV) :: Delta) body bodyV :=
    hbodyOpenTr.closeOpenedFVarZero hbodyEq hbodyAbsent
      (hbinder.instRevBounds fv) (habstract.bounds hbodySupport fv)
  obtain ⟨bodyTyCoreV, hbodyTyCoreTr, hbodyTyEq⟩ := hbodyTyTr
  have hcheapMeaning := KExpr.cheapBetaReduceResult_meaning theory
    hIBody.2.1.wf hbodyTyCoreTr (hcheap.bounds hbodyTySupport)
  apply TcM.WF.bind
    (TcM.WF.mono
      (TcM.WF.withInv <| TcM.PreservesInferOnly.strengthenWFValue
        (hcheap.whnf_wf hcollision hbodyTySupport)
        (TcM.PreservesInferOnly.runIntern _) hpolicyBody)
      (fun _ _ post => post) (fun _ _ post => post.1))
  intro reduced afterCheap hcheapPost
  rcases hcheapPost with
    ⟨hICheap, hpolicyCheap, rfl, hreducedSupport, _⟩
  have hreducedQ := WhnfMeaning.resultQuot theory hICheap.2.1.wf
    (⟨bodyTyCoreV, hbodyTyCoreTr, hbodyTyEq⟩ :
      TrKExpr world.venv uvars world.nameOf trProj
        ((some (fv, Delta.fvars), .vlam tyV) :: Delta) bodyTy bodyTyV)
    hcheapMeaning
  obtain ⟨reducedV, hreducedTr, hreducedEq⟩ := hreducedQ
  apply TcM.WF.bind
    (TcM.WF.mono
      (TcM.WF.withInv <| TcM.PreservesInferOnly.strengthenWFValue
        (habstract.close_whnf_wf hcollision hreducedSupport hreducedTr)
        (TcM.PreservesInferOnly.runIntern _) hpolicyCheap)
      (fun _ _ post => post) (fun _ _ post => post.1))
  intro abstracted afterAbstract habstractPost
  rcases habstractPost with
    ⟨hIAbstract, hpolicyAbstract, rfl, habstractedSupport, _,
      habstractedTr⟩
  have hresultSupport := hresults habstractedSupport
  apply TcM.WF.mono
    (TcM.WF.mono
      (TcM.WF.withInv <| TcM.PreservesInferOnly.strengthenWFValue
        (TcM.intern_whnf_wf hcollision hresultSupport)
        (TcM.PreservesInferOnly.runIntern _) hpolicyAbstract)
      (fun _ _ post => post) (fun _ _ post => post.1))
  · intro result final hresult
    rcases hresult with ⟨hIFinal, hpolicyFinal, rfl, _⟩
    have hDelta : KVLCtx.WF world.venv uvars Delta := hIFinal.2.1.wf.1
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
    have hsourceTr : TrKExprS world.venv uvars world.nameOf trProj Delta
        (.lam name bi ty body info) (.lam tyV bodyV) :=
      .lam ⟨u, htySort⟩ htyTr hbodyTr
    exact ⟨hpolicyFinal, hresultSupport, hsourceTr,
      .forallE tyV bodyTyV, hresultTr,
      Lean4Lean.VEnv.HasType.lam htySort hbodyTy'⟩
  · intro _ _ herror
    exact herror

/-- Full-mode lambda inference reconstructs the typed binder translation
from its pre-translation and recursively checked domain/body. -/
theorem inferUncached_lam_full_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {uvars : Nat} {Delta : KVLCtx}
    {methods : Methods .anon} {s : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body : KExpr .anon} {info : ExprInfo .anon} {sourceV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (callbacks : FullInferenceStepContext semantics trProj world support
      uvars methods)
    (hcheap : CheapBetaResources support)
    (habstract : SingletonAbstractionResources support)
    (hresults : LambdaResultSupport support ty)
    (htySupport : support ty)
    (hbinder : BinderOpeningResources support name body)
    (hsource : PreTrKExprS world.venv uvars world.nameOf trProj Delta
      (.lam name bi ty body info) sourceV)
    (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((inferUncached inferCall false (.lam name bi ty body info)).run
        methods)
      (fun result after =>
        after.inferOnly = false ∧
          FullInferPost trProj world support uvars Delta
            (.lam name bi ty body info) sourceV result)
      (fun _ after => after.inferOnly = false) := by
  cases hsource with
  | lam htyPre hbodyPre =>
      rename_i tyV bodyV
      unfold inferUncached
      simp only [Bool.not_false, if_true, ReaderT.run_bind,
        ReaderT.run_monadLift, inferCall, pure_bind]
      apply TcM.WF.bind
        (TcM.WF.withInv <| callbacks.infer hpolicy htySupport htyPre)
      intro tyTy afterTy htyPost
      rcases htyPost with
        ⟨hITy, hpolicyTy, htyTySupport, htyTr,
          tyTyV, htyTyTr, htyTy⟩
      apply TcM.WF.bind
        (TcM.WF.withInv <|
          callbacks.ensureSort hpolicyTy htyTySupport htyTyTr)
      intro u afterSort hsortPost
      rcases hsortPost with ⟨hISort, hpolicySort, hu⟩
      have htySort : world.venv.HasType uvars Delta.toCtx tyV
          (.sort u.toVLevel) :=
        htyTy.defeqU_r world.venvWF hISort.2.1.wf.toCtx hu.inputEq
      have htyType : world.venv.IsType uvars Delta.toCtx tyV :=
        ⟨u.toVLevel, htySort⟩
      apply withLctxScope_openBinder_pre_wf
        (layer := .noAccel) (semantics := semantics) (trProj := trProj)
        (world := world) (support := support) (uvars := uvars)
        (Delta := Delta) (methods := methods) (s := afterSort)
        (bi := bi)
        (k := fun bodyOpen fv => do
          let bodyTy ← inferCall bodyOpen
          let bodyTy ← TcM.runIntern (cheapBetaReduce bodyTy)
          let abstracted ← TcM.runIntern (abstractFVars bodyTy #[fv])
          TcM.intern (.mkAll anonN anonBi ty abstracted))
        (Qinner := fun result after =>
          after.inferOnly = false ∧
            FullInferPost trProj world support uvars Delta
              (.lam name bi ty body info) (.lam tyV bodyV) result)
        (Qouter := fun result after =>
          after.inferOnly = false ∧
            FullInferPost trProj world support uvars Delta
              (.lam name bi ty body info) (.lam tyV bodyV) result)
        (Einner := fun _ after => after.inferOnly = false)
        (Eouter := fun _ after => after.inferOnly = false)
        htyTr htyType hbodyPre hrun.collisionFree hbinder hpolicySort
      · intro bodyOpen fv after hfv hbodyEq hbodySupport hfresh
          hbodyOpenPre hpolicyOpen
        subst fv
        exact inferLambdaFullTail_wf
          (semantics := semantics) (trProj := trProj) (world := world)
          (support := support) (uvars := uvars) (Delta := Delta)
          (methods := methods) (s := after) (name := name)
          (bi := bi) (ty := ty) (body := body) (info := info)
          (tyV := tyV) (bodyV := bodyV) theory callbacks hcheap
          habstract hresults hrun.collisionFree htyType htyTr hbodyPre
          hbinder hbodyEq hfresh hbodySupport hbodyOpenPre hpolicyOpen
      · intro result after hresult
        simpa using hresult
      · intro err after herror
        simpa using herror
      · intro err
        exact hpolicySort

/-- Full-inference forall tail after opening its body. -/
private theorem inferForallFullTail_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {fv : FVarId} {name : Mode.anon.F Name}
    {bi : Mode.anon.F Lean.BinderInfo}
    {ty body bodyOpen : KExpr .anon} {info : ExprInfo .anon}
    {tyV bodyV input1 : VExpr} {u1 : KUniv .anon}
    (theory : WhnfTheory trProj world uvars)
    (callbacks : FullInferenceStepContext semantics trProj world support
      uvars methods)
    (habstract : SingletonAbstractionResources support)
    (hresults : ForallResultSupport support)
    (hcollision : support.CollisionFree)
    (htyType : world.venv.IsType uvars Delta.toCtx tyV)
    (htySort : world.venv.HasType uvars Delta.toCtx tyV
      (.sort u1.toVLevel))
    (htyTr : TrKExprS world.venv uvars world.nameOf trProj Delta ty tyV)
    (hu1 : SortView world support uvars Delta input1 u1)
    (hbodyPre : PreTrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam tyV) :: Delta) body bodyV)
    (hbinder : BinderOpeningResources support name body)
    (hbodyEq : bodyOpen = KExpr.instantiateRevSpec body
      #[.mkFVar fv name] 0)
    (hfresh : fv ∉ Delta.fvars)
    (hbodySupport : support bodyOpen)
    (hbodyOpenPre : PreTrKExprS world.venv uvars world.nameOf trProj
      ((some (fv, Delta.fvars), .vlam tyV) :: Delta) bodyOpen bodyV)
    (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars
        ((some (fv, Delta.fvars), .vlam tyV) :: Delta)) s
      ((do
        let bodyTy ← inferCall bodyOpen
        let u2 ← ensureSortDirect bodyTy
        TcM.intern (.mkSort (.mkIMax u1 u2))).run methods)
      (fun result after =>
        after.inferOnly = false ∧
          FullInferPost trProj world support uvars Delta
            (.all name bi ty body info) (.forallE tyV bodyV) result)
      (fun _ after => after.inferOnly = false) := by
  simp only [ReaderT.run_bind, inferCall, ReaderT.run_monadLift]
  apply TcM.WF.bind
    (TcM.WF.withInv <| callbacks.infer hpolicy hbodySupport hbodyOpenPre)
  intro bodyTy afterBody hbodyPost
  rcases hbodyPost with
    ⟨hIBody, hpolicyBody, hbodyTySupport, hbodyOpenTr,
      bodyTyV, hbodyTyTr, hbodyTy⟩
  have hbodyAbsent : body.FVarAbsent fv :=
    hbodyPre.fvarAbsent (by simpa using hfresh)
  have hbodyTr : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam tyV) :: Delta) body bodyV :=
    hbodyOpenTr.closeOpenedFVarZero hbodyEq hbodyAbsent
      (hbinder.instRevBounds fv) (habstract.bounds hbodySupport fv)
  apply TcM.WF.bind
    (TcM.WF.withInv <|
      callbacks.ensureSort hpolicyBody hbodyTySupport hbodyTyTr)
  intro u2 afterSort hu2Post
  rcases hu2Post with ⟨hISort, hpolicySort, hu2⟩
  have hresultSupport := hresults hu1.rootSupport hu2.rootSupport
  apply TcM.WF.mono
    (TcM.WF.mono
      (TcM.WF.withInv <| TcM.PreservesInferOnly.strengthenWFValue
        (TcM.intern_whnf_wf hcollision hresultSupport)
        (TcM.PreservesInferOnly.runIntern _) hpolicySort)
      (fun _ _ post => post) (fun _ _ post => post.1))
  · intro result final hresult
    rcases hresult with ⟨hIFinal, hpolicyFinal, rfl, _⟩
    have hDelta : KVLCtx.WF world.venv uvars Delta := hIFinal.2.1.wf.1
    have hbodySort : world.venv.HasType uvars
        (tyV :: Delta.toCtx) bodyV (.sort u2.toVLevel) := by
      simpa [KVLCtx.toCtx] using
        hbodyTy.defeqU_r world.venvWF hIFinal.2.1.wf hu2.inputEq
    have hbodyType : world.venv.IsType uvars
        (tyV :: Delta.toCtx) bodyV := ⟨u2.toVLevel, hbodySort⟩
    have hsourceTr : TrKExprS world.venv uvars world.nameOf trProj Delta
        (.all name bi ty body info) (.forallE tyV bodyV) :=
      .all htyType hbodyType htyTr hbodyTr
    have hresultTr : TrKExpr world.venv uvars world.nameOf trProj Delta
        (KExpr.mkSort (KUniv.mkIMax u1 u2))
        (.sort (KUniv.mkIMax u1 u2).toVLevel) :=
      (TrKExprS.sort
        (KUniv.toVLevel_mkIMax_wf hu1.levelWF hu2.levelWF)).trKExpr
          world.venvWF.ordered theory.literalWF theory.projections.wf hDelta
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
    exact ⟨hpolicyFinal, hresultSupport, hsourceTr,
      .sort (KUniv.mkIMax u1 u2).toVLevel, hresultTr,
      hforall.defeqU_r world.venvWF hDelta hsortEq⟩
  · intro _ _ herror
    exact herror

/-- Full-mode forall inference validates both domain and body as types and
returns the exact production `imax` sort. -/
theorem inferUncached_all_full_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {uvars : Nat} {Delta : KVLCtx}
    {methods : Methods .anon} {s : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body : KExpr .anon} {info : ExprInfo .anon} {sourceV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (callbacks : FullInferenceStepContext semantics trProj world support
      uvars methods)
    (habstract : SingletonAbstractionResources support)
    (hresults : ForallResultSupport support)
    (htySupport : support ty)
    (hbinder : BinderOpeningResources support name body)
    (hsource : PreTrKExprS world.venv uvars world.nameOf trProj Delta
      (.all name bi ty body info) sourceV)
    (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((inferUncached inferCall false (.all name bi ty body info)).run
        methods)
      (fun result after =>
        after.inferOnly = false ∧
          FullInferPost trProj world support uvars Delta
            (.all name bi ty body info) sourceV result)
      (fun _ after => after.inferOnly = false) := by
  cases hsource with
  | all htyPre hbodyPre =>
      rename_i tyV bodyV
      unfold inferUncached
      simp only [ReaderT.run_bind, ReaderT.run_monadLift, inferCall]
      apply TcM.WF.bind
        (TcM.WF.withInv <| callbacks.infer hpolicy htySupport htyPre)
      intro tyTy afterTy htyPost
      rcases htyPost with
        ⟨hITy, hpolicyTy, htyTySupport, htyTr,
          tyTyV, htyTyTr, htyTy⟩
      apply TcM.WF.bind
        (TcM.WF.withInv <|
          callbacks.ensureSort hpolicyTy htyTySupport htyTyTr)
      intro u1 afterSort hu1Post
      rcases hu1Post with ⟨hISort, hpolicySort, hu1⟩
      have htySort : world.venv.HasType uvars Delta.toCtx tyV
          (.sort u1.toVLevel) :=
        htyTy.defeqU_r world.venvWF hISort.2.1.wf.toCtx hu1.inputEq
      have htyType : world.venv.IsType uvars Delta.toCtx tyV :=
        ⟨u1.toVLevel, htySort⟩
      apply withLctxScope_openBinder_pre_wf
        (layer := .noAccel) (semantics := semantics) (trProj := trProj)
        (world := world) (support := support) (uvars := uvars)
        (Delta := Delta) (methods := methods) (s := afterSort)
        (bi := bi)
        (k := fun bodyOpen _ => do
          let bodyTy ← inferCall bodyOpen
          let u2 ← ensureSortDirect bodyTy
          TcM.intern (.mkSort (.mkIMax u1 u2)))
        (Qinner := fun result after =>
          after.inferOnly = false ∧
            FullInferPost trProj world support uvars Delta
              (.all name bi ty body info) (.forallE tyV bodyV) result)
        (Qouter := fun result after =>
          after.inferOnly = false ∧
            FullInferPost trProj world support uvars Delta
              (.all name bi ty body info) (.forallE tyV bodyV) result)
        (Einner := fun _ after => after.inferOnly = false)
        (Eouter := fun _ after => after.inferOnly = false)
        htyTr htyType hbodyPre hrun.collisionFree hbinder hpolicySort
      · intro bodyOpen fv after hfv hbodyEq hbodySupport hfresh
          hbodyOpenPre hpolicyOpen
        subst fv
        exact inferForallFullTail_wf
          (semantics := semantics) (trProj := trProj) (world := world)
          (support := support) (uvars := uvars) (Delta := Delta)
          (methods := methods) (s := after) (name := name) (bi := bi)
          (ty := ty) (body := body) (info := info)
          (tyV := tyV) (bodyV := bodyV) theory callbacks habstract
          hresults hrun.collisionFree htyType htySort htyTr hu1 hbodyPre
          hbinder hbodyEq hfresh hbodySupport hbodyOpenPre hpolicyOpen
      · intro result after hresult
        simpa using hresult
      · intro err after herror
        simpa using herror
      · intro err
        exact hpolicySort

/-- Full-inference let tail after opening its body with a tagged let fvar. -/
private theorem inferLetFullTail_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {fv : FVarId} {name : Mode.anon.F Name}
    {type value body bodyOpen : KExpr .anon}
    {nondep : Bool} {info : ExprInfo .anon}
    {typeV valueV bodyV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (callbacks : FullInferenceStepContext semantics trProj world support
      uvars methods)
    (habstract : SingletonAbstractionResources support)
    (hsubst : SubstitutionResources support)
    (hcheap : CheapBetaResources support)
    (hcollision : support.CollisionFree)
    (htypeTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      type typeV)
    (hvalueSupport : support value)
    (hvalueTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      value valueV)
    (hvalueType : world.venv.HasType uvars Delta.toCtx valueV typeV)
    (hbodyPre : PreTrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlet typeV valueV) :: Delta) body bodyV)
    (hbinder : BinderOpeningResources support name body)
    (hbodyEq : bodyOpen = KExpr.instantiateRevSpec body
      #[.mkFVar fv name] 0)
    (hfresh : fv ∉ Delta.fvars)
    (hbodySupport : support bodyOpen)
    (hbodyOpenPre : PreTrKExprS world.venv uvars world.nameOf trProj
      ((some (fv, Delta.fvars), .vlet typeV valueV) :: Delta)
      bodyOpen bodyV)
    (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars
        ((some (fv, Delta.fvars), .vlet typeV valueV) :: Delta)) s
      ((do
        let bodyTy ← inferCall bodyOpen
        let abstracted ← TcM.runIntern (abstractFVars bodyTy #[fv])
        let result ← TcM.runIntern (subst abstracted value 0)
        TcM.runIntern (cheapBetaReduce result)).run methods)
      (fun result after =>
        after.inferOnly = false ∧
          FullInferPost trProj world support uvars Delta
            (.letE name type value body nondep info) bodyV result)
      (fun _ after => after.inferOnly = false) := by
  simp only [ReaderT.run_bind, inferCall, ReaderT.run_monadLift]
  apply TcM.WF.bind
    (TcM.WF.withInv <| callbacks.infer hpolicy hbodySupport hbodyOpenPre)
  intro bodyTy afterBody hbodyPost
  rcases hbodyPost with
    ⟨hIBody, hpolicyBody, hbodyTySupport, hbodyOpenTr,
      bodyTyV, hbodyTyTr, hbodyTy⟩
  have hbodyAbsent : body.FVarAbsent fv :=
    hbodyPre.fvarAbsent (by simpa using hfresh)
  have hbodyTr : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlet typeV valueV) :: Delta) body bodyV :=
    hbodyOpenTr.closeOpenedFVarZero hbodyEq hbodyAbsent
      (hbinder.instRevBounds fv) (habstract.bounds hbodySupport fv)
  obtain ⟨bodyTyCoreV, hbodyTyCoreTr, hbodyTyEq⟩ := hbodyTyTr
  apply TcM.WF.bind
    (TcM.WF.mono
      (TcM.WF.withInv <| TcM.PreservesInferOnly.strengthenWFValue
        (habstract.close_whnf_wf hcollision hbodyTySupport hbodyTyCoreTr)
        (TcM.PreservesInferOnly.runIntern _) hpolicyBody)
      (fun _ _ post => post) (fun _ _ post => post.1))
  intro abstracted afterAbstract habstractPost
  rcases habstractPost with
    ⟨hIAbstract, hpolicyAbstract, rfl, habstractedSupport, _,
      habstractedTr⟩
  have hsubstBounds := hsubst.bounds (depth := 0)
    habstractedSupport hvalueSupport
  obtain ⟨_, hvalueCon, _, _, hsubstBig⟩ := hsubstBounds
  have hsubstTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.substSpec
        (KExpr.abstractFVarsResult bodyTy #[fv]) value 0) bodyTyCoreV :=
    TrKExprS.inst_let_lbr world.venvWF.ordered
      theory.projections.weakN hvalueCon habstractedTr hvalueTr (by
        simpa using hsubstBig)
  apply TcM.WF.bind
    (TcM.WF.mono
      (TcM.WF.withInv <| TcM.PreservesInferOnly.strengthenWFValue
        (hsubst.whnf_wf hcollision habstractedSupport hvalueSupport)
        (TcM.PreservesInferOnly.runIntern _) hpolicyAbstract)
      (fun _ _ post => post) (fun _ _ post => post.1))
  intro substituted afterSubst hsubstPost
  rcases hsubstPost with
    ⟨hISubst, hpolicySubst, rfl, hsubstitutedSupport, _⟩
  have hsubstitutedQ : TrKExpr world.venv uvars world.nameOf trProj Delta
      (KExpr.substSpec
        (KExpr.abstractFVarsResult bodyTy #[fv]) value 0) bodyTyV :=
    ⟨bodyTyCoreV, hsubstTr, hbodyTyEq⟩
  have hcheapMeaning := KExpr.cheapBetaReduceResult_meaning theory
    hISubst.2.1.wf.1 hsubstTr (hcheap.bounds hsubstitutedSupport)
  apply TcM.WF.mono
    (TcM.WF.mono
      (TcM.WF.withInv <| TcM.PreservesInferOnly.strengthenWFValue
        (hcheap.whnf_wf hcollision hsubstitutedSupport)
        (TcM.PreservesInferOnly.runIntern _) hpolicySubst)
      (fun _ _ post => post) (fun _ _ post => post.1))
  · intro result final hresult
    rcases hresult with
      ⟨hIFinal, hpolicyFinal, rfl, hresultSupport, _⟩
    have hresultQ := WhnfMeaning.resultQuot theory hIFinal.2.1.wf.1
      hsubstitutedQ hcheapMeaning
    have hbodyTy' : world.venv.HasType uvars Delta.toCtx bodyV bodyTyV := by
      simpa [KVLCtx.toCtx] using hbodyTy
    have hsourceTr : TrKExprS world.venv uvars world.nameOf trProj Delta
        (.letE name type value body nondep info) bodyV :=
      .letE hvalueType htypeTr hvalueTr hbodyTr
    exact ⟨hpolicyFinal, hresultSupport, hsourceTr,
      bodyTyV, hresultQ, hbodyTy'⟩
  · intro _ _ herror
    exact herror

/-- Full-mode let inference validates its annotation and value before
running the production abstraction/substitution/cheap-beta tail. -/
theorem inferUncached_let_full_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {name : Mode.anon.F Name}
    {type value body : KExpr .anon} {nondep : Bool}
    {info : ExprInfo .anon} {sourceV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (callbacks : FullInferenceStepContext semantics trProj world support
      uvars methods)
    (habstract : SingletonAbstractionResources support)
    (hsubst : SubstitutionResources support)
    (hcheap : CheapBetaResources support)
    (htypeSupport : support type)
    (hvalueSupport : support value)
    (hbinder : BinderOpeningResources support name body)
    (hcollision : support.CollisionFree)
    (hsource : PreTrKExprS world.venv uvars world.nameOf trProj Delta
      (.letE name type value body nondep info) sourceV)
    (hpolicy : s.inferOnly = false) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((inferUncached inferCall false
        (.letE name type value body nondep info)).run methods)
      (fun result after =>
        after.inferOnly = false ∧
          FullInferPost trProj world support uvars Delta
            (.letE name type value body nondep info) sourceV result)
      (fun _ after => after.inferOnly = false) := by
  cases hsource with
  | letE htypePre hvaluePre hbodyPre =>
      rename_i typeV valueV
      unfold inferUncached
      simp only [Bool.not_false, if_true, ReaderT.run_bind,
        ReaderT.run_monadLift, inferCall, isDefEqCall, pure_bind]
      apply TcM.WF.bind
        (TcM.WF.withInv <| callbacks.infer hpolicy htypeSupport htypePre)
      intro typeTy afterType htypePost
      rcases htypePost with
        ⟨hIType, hpolicyType, htypeTySupport, htypeTr,
          typeTyV, htypeTyTr, htypeTy⟩
      apply TcM.WF.bind
        (TcM.WF.withInv <|
          callbacks.ensureSort hpolicyType htypeTySupport htypeTyTr)
      intro _ afterSort hsortPost
      rcases hsortPost with ⟨hISort, hpolicySort, _⟩
      apply TcM.WF.bind
        (TcM.WF.withInv <|
          callbacks.infer hpolicySort hvalueSupport hvaluePre)
      intro valueTy afterValue hvaluePost
      rcases hvaluePost with
        ⟨hIValue, hpolicyValue, hvalueTySupport, hvalueTr,
          valueTyV, hvalueTyTr, hvalueTy⟩
      obtain ⟨valueTyCoreV, hvalueTyCoreTr, hvalueTyEq⟩ := hvalueTyTr
      apply TcM.WF.bind
        (TcM.WF.withInv <| callbacks.isDefEq hpolicyValue
          hvalueTySupport htypeSupport hvalueTyCoreTr htypeTr)
      intro equal afterEq hequal
      rcases hequal with ⟨hIEq, hpolicyEq, heq⟩
      cases equal with
      | false =>
          simp only [Bool.not_false, if_true]
          exact TcM.WF.throw fun _ => hpolicyEq
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, if_false]
          have hvalueType : world.venv.HasType uvars Delta.toCtx
              valueV typeV :=
            hvalueTy.defeqU_r world.venvWF hIEq.2.1.wf.toCtx <|
              hvalueTyEq.symm.trans world.venvWF hIEq.2.1.wf.toCtx
                (heq rfl)
          apply withLctxScope_openLet_pre_wf
            (layer := .noAccel) (semantics := semantics) (trProj := trProj)
            (world := world) (support := support) (uvars := uvars)
            (Delta := Delta) (methods := methods) (s := afterEq)
            (k := fun bodyOpen fv => do
              let bodyTy ← inferCall bodyOpen
              let abstracted ← TcM.runIntern (abstractFVars bodyTy #[fv])
              let result ← TcM.runIntern (subst abstracted value 0)
              TcM.runIntern (cheapBetaReduce result))
            (Qinner := fun result after =>
              after.inferOnly = false ∧
                FullInferPost trProj world support uvars Delta
                  (.letE name type value body nondep info) sourceV result)
            (Qouter := fun result after =>
              after.inferOnly = false ∧
                FullInferPost trProj world support uvars Delta
                  (.letE name type value body nondep info) sourceV result)
            (Einner := fun _ after => after.inferOnly = false)
            (Eouter := fun _ after => after.inferOnly = false)
            htypeTr hvalueTr hvalueType hbodyPre hcollision hbinder hpolicyEq
          · intro bodyOpen fv after hfv hbodyEq hbodySupport hfresh
              hbodyOpenPre hpolicyOpen
            subst fv
            exact inferLetFullTail_wf
              (semantics := semantics) (trProj := trProj) (world := world)
              (support := support) (uvars := uvars) (Delta := Delta)
              (methods := methods) (s := after) (name := name)
              (type := type) (value := value) (body := body)
              (nondep := nondep) (info := info)
              (typeV := typeV) (valueV := valueV) (bodyV := sourceV)
              theory callbacks habstract hsubst hcheap hcollision htypeTr
              hvalueSupport hvalueTr hvalueType hbodyPre hbinder hbodyEq
              hfresh hbodySupport hbodyOpenPre hpolicyOpen
          · intro result after hresult
            simpa using hresult
          · intro err after herror
            simpa using herror
          · intro err
            exact hpolicyEq

end RecM

end Ix.Tc
