import Ix.Tc.Verify.Infer.BinderScopes

/-!
# Operational let scopes for inference

`openLet` shares allocation and binder instantiation with `openBinder`, but
pushes an `ldecl` and translates to a Theory `vlet`.  Keeping its proof
separate makes that semantic distinction visible at the API boundary.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace TcM

/-- Opening a translated let either fails before changing the semantic
context, or returns its freshly tagged body under a `vlet` frame. -/
theorem openLet_scope
    {support : RunSupport}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {name : Mode.anon.F Name}
    {ty val body : KExpr .anon} {tyV valV bodyV : VExpr}
    (hty : TrKExprS world.venv uvars world.nameOf trProj Delta ty tyV)
    (hval : TrKExprS world.venv uvars world.nameOf trProj Delta val valV)
    (hvalType : world.venv.HasType uvars Delta.toCtx valV tyV)
    (hbody : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlet tyV valV) :: Delta) body bodyV)
    (hcollision : support.CollisionFree)
    (hresources : BinderOpeningResources support name body) :
    WhnfStateInv layer semantics trProj world support uvars Delta s →
    match TcM.openLet name ty val body s with
    | .ok (bodyOpen, fvId) after =>
        fvId = ⟨s.env.nextFVarId⟩ ∧
        bodyOpen = KExpr.instantiateRevSpec body
          #[.mkFVar ⟨s.env.nextFVarId⟩ name] 0 ∧
        WhnfStateInv layer semantics trProj world support uvars
          ((some (⟨s.env.nextFVarId⟩, Delta.fvars),
            .vlet tyV valV) :: Delta) after ∧
        support bodyOpen ∧
        TrKExprS world.venv uvars world.nameOf trProj
          ((some (⟨s.env.nextFVarId⟩, Delta.fvars),
            .vlet tyV valV) :: Delta) bodyOpen bodyV
    | .error _ after =>
        WhnfStateInv layer semantics trProj world support uvars Delta after ∧
          after = s := by
  intro hI
  have hfreshPost := (TcM.freshFVarId_wf (s := s)
    (layer := layer) (semantics := semantics) (trProj := trProj)
    (world := world) (support := support) (uvars := uvars)
    (Delta := Delta)) hI
  cases hfreshRun : TcM.freshFVarId (m := .anon) s with
  | error err afterFresh =>
      rw [hfreshRun] at hfreshPost
      simp only at hfreshPost
      have hafter : afterFresh = s := hfreshPost.2.2
      subst afterFresh
      have hopenError : TcM.openLet name ty val body s = .error err s := by
        unfold TcM.openLet
        change EStateM.bind (TcM.freshFVarId (m := .anon)) _ s = _
        unfold EStateM.bind
        rw [hfreshRun]
      rw [hopenError]
      exact ⟨hfreshPost.1, rfl⟩
  | ok fvId afterFresh =>
      rw [hfreshRun] at hfreshPost
      simp only at hfreshPost
      rcases hfreshPost.2 with ⟨hfvId, hafterFresh, hnext⟩
      subst fvId
      subst afterFresh
      let fv : KExpr .anon := .mkFVar ⟨s.env.nextFVarId⟩ name
      obtain ⟨afterIntern, hinternRun, hIIntern, hInternFrame⟩ :=
        TcM.intern_whnf_eval hcollision
          (hresources.fvarSupport ⟨s.env.nextFVarId⟩) hfreshPost.1
      let pushState : TcState .anon → TcState .anon := fun state =>
        {state with lctx :=
          state.lctx.push ⟨s.env.nextFVarId⟩ (.ldecl name ty val)}
      let afterPush : TcState .anon := pushState afterIntern
      have hkernelPush :
          KernelStateWF semantics trProj world support afterPush := by
        exact {
          core := hIIntern.1.core.of_env_eq rfl
          internSupport := by simpa [afterPush] using hIIntern.1.internSupport
          caches := by simpa [afterPush] using hIIntern.1.caches
          equivalences := by
            simpa [afterPush, pushState] using hIIntern.1.equivalences }
      have hIPush : WhnfStateInv layer semantics trProj world support uvars
          ((some (⟨s.env.nextFVarId⟩, Delta.fvars),
            .vlet tyV valV) :: Delta) afterPush := by
        apply hI.openFVar hkernelPush
          (TrKLocalDecl.vlet (nm := name) hty hval hvalType)
          (by intro x hx; exact hx)
        · simpa [afterPush, InternUpdateFrame] using
            congrArg TcState.ctx hInternFrame
        · simpa [afterPush, InternUpdateFrame] using
            congrArg TcState.letVals hInternFrame
        · simpa [afterPush, InternUpdateFrame] using
            congrArg TcState.numLetBindings hInternFrame
        · have hlctx : afterIntern.lctx = s.lctx := by
            simpa [InternUpdateFrame] using
              congrArg TcState.lctx hInternFrame
          simp [afterPush, pushState, hlctx]
        · have hnextEq : afterIntern.env.nextFVarId =
              s.env.freshFVarId.2.nextFVarId := by
            simpa [InternUpdateFrame] using congrArg
              (fun state : TcState .anon => state.env.nextFVarId)
              hInternFrame
          simpa [afterPush, pushState, hnextEq] using hnext
        · simpa [afterPush, InternUpdateFrame] using
            congrArg TcState.prims hInternFrame
        · simpa [afterPush, InternUpdateFrame] using
            congrArg TcState.noAccel hInternFrame
      have hopenBound := hresources.instRevBounds ⟨s.env.nextFVarId⟩
      have hbodyOpenTr := hbody.openFVarZero
        (fv := ⟨s.env.nextFVarId⟩) (deps := Delta.fvars) (name := name)
        hI.2.1.nextFVarId_fresh (by simpa using hopenBound.2.2)
      have hbodyOpenSupport : support
          (KExpr.instantiateRevSpec body #[fv] 0) :=
        hresources.instRevSupport ⟨s.env.nextFVarId⟩ _
          (KExpr.InstRevReach.spec ..)
      obtain ⟨afterOpen, hopenRun, hIOpen, hOpenFrame⟩ :=
        instRev_whnf_eval_of_resources hcollision hopenBound
          (hresources.instRevSupport ⟨s.env.nextFVarId⟩) hIPush
      have hopenSuccess : TcM.openLet name ty val body s =
          .ok (KExpr.instantiateRevSpec body #[fv] 0,
            ⟨s.env.nextFVarId⟩) afterOpen := by
        unfold TcM.openLet
        change EStateM.bind (TcM.freshFVarId (m := .anon)) _ s = _
        unfold EStateM.bind
        rw [hfreshRun]
        simp only
        change EStateM.bind (TcM.intern fv) _ _ = _
        unfold EStateM.bind
        rw [hinternRun]
        simp only
        change EStateM.bind
          (modify pushState : TcM .anon PUnit) _ afterIntern = _
        unfold EStateM.bind
        rw [show (modify pushState : TcM .anon PUnit) afterIntern =
          EStateM.Result.ok () afterPush from rfl]
        simp only
        change EStateM.bind
          (TcM.runIntern (instantiateRev body #[fv])) _ afterPush = _
        unfold EStateM.bind
        rw [hopenRun]
        rfl
      rw [hopenSuccess]
      refine ⟨rfl, rfl, hIOpen, ?_, ?_⟩
      · simpa [fv] using hbodyOpenSupport
      · simpa [fv] using hbodyOpenTr

end TcM

namespace RecM

/-- Compose verified let opening with an arbitrary continuation and close
the tagged local on both continuation success and continuation error. -/
theorem withLctxScope_openLet_wf
    {beta : Type} {support : RunSupport}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {name : Mode.anon.F Name}
    {ty val body : KExpr .anon} {tyV valV bodyV : VExpr}
    (hty : TrKExprS world.venv uvars world.nameOf trProj Delta ty tyV)
    (hval : TrKExprS world.venv uvars world.nameOf trProj Delta val valV)
    (hvalType : world.venv.HasType uvars Delta.toCtx valV tyV)
    (hbody : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlet tyV valV) :: Delta) body bodyV)
    (hcollision : support.CollisionFree)
    (hresources : BinderOpeningResources support name body)
    {k : KExpr .anon → FVarId → RecM .anon beta}
    {Qinner Qouter : beta → TcState .anon → Prop}
    (hk : ∀ {bodyOpen fv after},
      fv = ⟨s.env.nextFVarId⟩ →
      bodyOpen = KExpr.instantiateRevSpec body
        #[.mkFVar ⟨s.env.nextFVarId⟩ name] 0 →
      support bodyOpen →
      TrKExprS world.venv uvars world.nameOf trProj
        ((some (⟨s.env.nextFVarId⟩, Delta.fvars),
          .vlet tyV valV) :: Delta) bodyOpen bodyV →
      RecM.WF layer semantics trProj world support uvars
        ((some (⟨s.env.nextFVarId⟩, Delta.fvars),
          .vlet tyV valV) :: Delta) after (k bodyOpen fv) Qinner)
    (hclose : ∀ result after, Qinner result after →
      Qouter result
        {after with lctx := after.lctx.truncate s.lctx.size}) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (withLctxScope do
        let (bodyOpen, fv) ← TcM.openLet name ty val body
        k bodyOpen fv)
      Qouter := by
  intro methods hmethods hI
  rw [RecM.withLctxScope_eq]
  have hopenPost := TcM.openLet_scope hty hval hvalType hbody
    hcollision hresources hI
  cases hopenRun : TcM.openLet name ty val body s with
  | error err afterOpen =>
      rw [hopenRun] at hopenPost
      simp only at hopenPost
      rcases hopenPost with ⟨hIOpen, hafterOpen⟩
      have hscopedError :
          (do
            let (bodyOpen, fv) ←
              (liftM (TcM.openLet name ty val body) :
                RecM .anon (KExpr .anon × FVarId))
            k bodyOpen fv).run methods s = .error err afterOpen := by
        change EStateM.bind (TcM.openLet name ty val body)
          (fun opened => (k opened.1 opened.2).run methods) s = _
        unfold EStateM.bind
        rw [hopenRun]
      rw [hscopedError]
      subst afterOpen
      simp only [LocalContext.truncate_size]
      exact ⟨hIOpen, trivial⟩
  | ok opened afterOpen =>
      rcases opened with ⟨bodyOpen, fv⟩
      rw [hopenRun] at hopenPost
      simp only at hopenPost
      rcases hopenPost with
        ⟨hfv, hbodyEq, hIOpen, hbodySupport, hbodyTr⟩
      have htail := hk hfv hbodyEq hbodySupport hbodyTr
        methods hmethods hIOpen
      cases htailRun : (k bodyOpen fv).run methods afterOpen with
      | ok result after =>
          rw [htailRun] at htail
          simp only at htail
          have hscopedSuccess :
              (do
                let (bodyOpen, fv) ←
                  (liftM (TcM.openLet name ty val body) :
                    RecM .anon (KExpr .anon × FVarId))
                k bodyOpen fv).run methods s = .ok result after := by
            change EStateM.bind (TcM.openLet name ty val body)
              (fun opened => (k opened.1 opened.2).run methods) s = _
            unfold EStateM.bind
            rw [hopenRun]
            exact htailRun
          rw [hscopedSuccess]
          exact ⟨hI.closeFVarAtEntry htail.1, hclose _ _ htail.2⟩
      | error tailErr after =>
          rw [htailRun] at htail
          simp only at htail
          have hscopedError :
              (do
                let (bodyOpen, fv) ←
                  (liftM (TcM.openLet name ty val body) :
                    RecM .anon (KExpr .anon × FVarId))
                k bodyOpen fv).run methods s = .error tailErr after := by
            change EStateM.bind (TcM.openLet name ty val body)
              (fun opened => (k opened.1 opened.2).run methods) s = _
            unfold EStateM.bind
            rw [hopenRun]
            exact htailRun
          rw [hscopedError]
          exact ⟨hI.closeFVarAtEntry htail.1, trivial⟩

end RecM

end Ix.Tc
