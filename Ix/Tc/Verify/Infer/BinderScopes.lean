import Ix.Tc.Verify.Infer.BinderOpening

/-!
# Operational binder scopes for inference

The semantic retagging theorem in `BinderOpening` describes the result of
opening a de Bruijn binder.  This module verifies the production
`TcM.openBinder` helper, including fvar allocation, interning, local-context
extension, walker execution, and the allocation-exhaustion error path.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Finite closure needed by a generic recursive method contract when it
opens `body` with a freshly allocated anonymous-mode fvar.  The fvar id is a
`UInt64`, so quantifying over every possible id still describes a finite
family.  This is deliberately a support resource rather than request-list
membership: a finite execution certificate records only the id reached by
one concrete run, whereas `RecM.WF` ranges over every invariant callback
state.

The reach clause includes the source, every intermediate walker node, and
the final opened body.  The bounds clause is the exact arithmetic contract
consumed by `instantiateRev_spec`. -/
structure BinderOpeningResources (support : RunSupport)
    (name : Mode.anon.F Name) (body : KExpr .anon) : Prop where
  fvarSupport : ∀ fv : FVarId, support (.mkFVar fv name)
  instRevSupport : ∀ (fv : FVarId) (x : KExpr .anon),
    KExpr.InstRevReach #[.mkFVar fv name] body 0 x → support x
  instRevBounds : ∀ fv : FVarId,
    WalkerRequest.Bounds (.instRev body #[.mkFVar fv name])

namespace TcM

/-- Hoare form of request-independent binder instantiation.  This is the
compositional counterpart of `instRev_whnf_eval_of_resources`: callers that
continue in `RecM` can retain the exact opened body and intern-only frame
without selecting a concrete execution request. -/
theorem instRev_whnf_wf_of_resources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {body : KExpr .anon}
    {fvars : Array (KExpr .anon)} {s : TcState .anon}
    (hcollision : support.CollisionFree)
    (hbounds : WalkerRequest.Bounds (.instRev body fvars))
    (hreach : ∀ x, KExpr.InstRevReach fvars body 0 x → support x) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.runIntern (instantiateRev body fvars))
      (fun result after =>
        result = KExpr.instantiateRevSpec body fvars 0 ∧
          InternUpdateFrame s after) :=
  TcM.runIntern_whnf_wf
    (fun it hwf hsupport => by
      have post := Ix.Tc.instantiateRev_spec hcollision.expr hbounds.1
        hbounds.2.2 hreach hwf hsupport.expr
      exact ⟨post.1, post.2.1,
        hsupport.of_expr_univs post.2.2
          (instantiateRev_preservesUnivs body fvars it)⟩)

/-- Request-independent execution of the binder-opening walker.  Generic
recursive closure cannot select one concrete request indexed by a callback's
post-state, so this form consumes the finite support resource directly. -/
theorem instRev_whnf_eval_of_resources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {body : KExpr .anon}
    {fvars : Array (KExpr .anon)} {s : TcState .anon}
    (hcollision : support.CollisionFree)
    (hbounds : WalkerRequest.Bounds (.instRev body fvars))
    (hreach : ∀ x, KExpr.InstRevReach fvars body 0 x → support x)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s) :
    ∃ after,
      TcM.runIntern (instantiateRev body fvars) s =
        .ok (KExpr.instantiateRevSpec body fvars 0) after ∧
      WhnfStateInv layer semantics trProj world support uvars Delta after ∧
      InternUpdateFrame s after :=
  TcM.runIntern_whnf_eval
    (fun it hwf hsupport => by
      have post := Ix.Tc.instantiateRev_spec hcollision.expr hbounds.1
        hbounds.2.2 hreach hwf hsupport.expr
      exact ⟨post.1, post.2.1,
        hsupport.of_expr_univs post.2.2
          (instantiateRev_preservesUnivs body fvars it)⟩)
    hI

/-- Opening a translated binder either fails before changing the semantic
context, or returns its freshly tagged body under the corresponding extended
concrete and ghost contexts. -/
theorem openBinder_scope
    {support : RunSupport}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body : KExpr .anon} {tyV bodyV : VExpr}
    (hty : TrKExprS world.venv uvars world.nameOf trProj Delta ty tyV)
    (htyType : world.venv.IsType uvars Delta.toCtx tyV)
    (hbody : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam tyV) :: Delta) body bodyV)
    (hcollision : support.CollisionFree)
    (hresources : BinderOpeningResources support name body) :
    WhnfStateInv layer semantics trProj world support uvars Delta s →
    match TcM.openBinder name bi ty body s with
    | .ok (bodyOpen, fvId) after =>
        fvId = ⟨s.env.nextFVarId⟩ ∧
        bodyOpen = KExpr.instantiateRevSpec body
          #[.mkFVar ⟨s.env.nextFVarId⟩ name] 0 ∧
        WhnfStateInv layer semantics trProj world support uvars
          ((some (⟨s.env.nextFVarId⟩, Delta.fvars), .vlam tyV) :: Delta)
          after ∧
        support bodyOpen ∧
        TrKExprS world.venv uvars world.nameOf trProj
          ((some (⟨s.env.nextFVarId⟩, Delta.fvars), .vlam tyV) :: Delta)
          bodyOpen bodyV
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
      have hopenError : TcM.openBinder name bi ty body s = .error err s := by
        unfold TcM.openBinder
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
          state.lctx.push ⟨s.env.nextFVarId⟩ (.cdecl name bi ty)}
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
          ((some (⟨s.env.nextFVarId⟩, Delta.fvars), .vlam tyV) :: Delta)
          afterPush := by
        apply hI.openFVar hkernelPush
          (TrKLocalDecl.vlam (nm := name) (bi := bi) hty htyType)
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
      have hopenSuccess : TcM.openBinder name bi ty body s =
          .ok (KExpr.instantiateRevSpec body #[fv] 0,
            ⟨s.env.nextFVarId⟩) afterOpen := by
        unfold TcM.openBinder
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

/-- Compose verified binder opening with an arbitrary continuation under the
tagged context.  `withLctxScope` closes the concrete and ghost fvar frame on
both continuation success and continuation error; allocation exhaustion is
the only pre-push error and restores the unchanged entry state. -/
theorem withLctxScope_openBinder_wf
    {beta : Type} {support : RunSupport}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body : KExpr .anon} {tyV bodyV : VExpr}
    (hty : TrKExprS world.venv uvars world.nameOf trProj Delta ty tyV)
    (htyType : world.venv.IsType uvars Delta.toCtx tyV)
    (hbody : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam tyV) :: Delta) body bodyV)
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
        ((some (⟨s.env.nextFVarId⟩, Delta.fvars), .vlam tyV) :: Delta)
        bodyOpen bodyV →
      RecM.WF layer semantics trProj world support uvars
        ((some (⟨s.env.nextFVarId⟩, Delta.fvars), .vlam tyV) :: Delta)
        after (k bodyOpen fv) Qinner)
    (hclose : ∀ result after, Qinner result after →
      Qouter result
        {after with lctx := after.lctx.truncate s.lctx.size}) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (withLctxScope do
        let (bodyOpen, fv) ← TcM.openBinder name bi ty body
        k bodyOpen fv)
      Qouter := by
  intro methods hmethods hI
  rw [RecM.withLctxScope_eq]
  have hopenPost := TcM.openBinder_scope (bi := bi) hty htyType hbody
    hcollision hresources hI
  cases hopenRun : TcM.openBinder name bi ty body s with
  | error err afterOpen =>
      rw [hopenRun] at hopenPost
      simp only at hopenPost
      rcases hopenPost with ⟨hIOpen, hafterOpen⟩
      have hscopedError :
          (do
            let (bodyOpen, fv) ←
              (liftM (TcM.openBinder name bi ty body) :
                RecM .anon (KExpr .anon × FVarId))
            k bodyOpen fv).run methods s = .error err afterOpen := by
        change EStateM.bind (TcM.openBinder name bi ty body)
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
                  (liftM (TcM.openBinder name bi ty body) :
                    RecM .anon (KExpr .anon × FVarId))
                k bodyOpen fv).run methods s = .ok result after := by
            change EStateM.bind (TcM.openBinder name bi ty body)
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
                  (liftM (TcM.openBinder name bi ty body) :
                    RecM .anon (KExpr .anon × FVarId))
                k bodyOpen fv).run methods s = .error tailErr after := by
            change EStateM.bind (TcM.openBinder name bi ty body)
              (fun opened => (k opened.1 opened.2).run methods) s = _
            unfold EStateM.bind
            rw [hopenRun]
            exact htailRun
          rw [hscopedError]
          exact ⟨hI.closeFVarAtEntry htail.1, trivial⟩

end RecM

end Ix.Tc
