import Ix.Tc.Verify.Whnf.StructEta.CallbackPrefix

/-!
# Scoped telescope state

This module verifies the local telescope operations used while classifying
recursive structure parameters.  Push, pop, and restoration preserve the
ambient WHNF state invariant while tracking the temporary lambda extension
of the caller's context.
-/

namespace Ix.Tc

theorem scratch_pushLocal_run
    {ty : KExpr .anon} {s s' : TcState .anon}
    (hrun : TcM.pushLocal ty s = .ok () s') :
    s'.env = s.env ∧
      s'.ctx = s.ctx.push ty ∧
      s'.letVals = s.letVals.push none ∧
      s'.numLetBindings = s.numLetBindings ∧
      s'.lctx = s.lctx ∧
      s'.prims = s.prims ∧
      s'.noAccel = s.noAccel ∧
      s'.equivManager = s.equivManager := by
  simp only [TcM.pushLocal, EStateM.bind, get, set, pure] at hrun
  cases hrun
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem scratch_pushLocal_ok (ty : KExpr .anon) (s : TcState .anon) :
    ∃ after, TcM.pushLocal ty s = .ok () after := by
  unfold TcM.pushLocal
  exact ⟨_, rfl⟩

theorem scratch_pushLocal_inv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s s' : TcState .anon}
    {ty : KExpr .anon} {tyV : Lean4Lean.VExpr}
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Delta ty tyV)
    (htype : world.venv.IsType uvars Delta.toCtx tyV)
    (hrun : TcM.pushLocal ty s = .ok () s') :
    WhnfStateInv layer semantics trProj world support uvars
      ((none, .vlam tyV) :: Delta) s' := by
  obtain ⟨henv, hctx, hlet, hnum, hlctx, hprims, hnoAccel, hequiv⟩ :=
    scratch_pushLocal_run hrun
  refine ⟨?_, ?_, ?_⟩
  · exact {
      core := hI.1.core.of_env_eq henv
      internSupport := by simpa only [henv] using hI.1.internSupport
      caches := by simpa only [henv] using hI.1.caches
      equivalences := by simpa only [hequiv] using hI.1.equivalences }
  · exact hI.2.1.pushLocal htr htype hctx hlet hnum hlctx (by simp [henv])
  · cases layer with
    | structuralNoAccel =>
        simpa only [WhnfLayer.StateOK, hnoAccel] using hI.2.2
    | noAccel =>
        simpa only [WhnfLayer.StateOK, hprims, hnoAccel] using hI.2.2
    | accelerated =>
      simpa only [WhnfLayer.StateOK, hprims] using hI.2.2

theorem scratch_lam_back
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {s : TcState .anon} {Delta : KVLCtx} {tyV : Lean4Lean.VExpr}
    (h : CtxRecon env uvars nameOf trProj s
      ((none, .vlam tyV) :: Delta)) :
    s.letVals.back? = some none := by
  obtain ⟨ty, bs, hbs, _⟩ := h.recon.bvar_lam_inv
  have hmap := congrArg (List.map Prod.snd) hbs
  rw [List.map_reverse,
    List.map_snd_zip (by simpa [h.size_eq])] at hmap
  have hhead := congrArg List.head? hmap
  simpa only [List.head?_reverse, List.head?_cons, List.map_cons,
    Array.getLast?_toList] using hhead

theorem scratch_popLocal_run
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {s s' : TcState .anon} {Delta : KVLCtx} {tyV : Lean4Lean.VExpr}
    (hctxRecon : CtxRecon env uvars nameOf trProj s
      ((none, .vlam tyV) :: Delta))
    (hrun : TcM.popLocal s = .ok () s') :
    s'.env = s.env ∧
      s'.ctx = s.ctx.pop ∧
      s'.letVals = s.letVals.pop ∧
      s'.numLetBindings = s.numLetBindings ∧
      s'.lctx = s.lctx ∧
      s'.prims = s.prims ∧
      s'.noAccel = s.noAccel ∧
      s'.equivManager = s.equivManager := by
  have hback := scratch_lam_back hctxRecon
  simp only [TcM.popLocal, EStateM.bind, get, set, pure, hback] at hrun
  cases hrun
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  simp only [hback]

theorem scratch_popLocal_ok (s : TcState .anon) :
    ∃ after, TcM.popLocal s = .ok () after := by
  unfold TcM.popLocal
  exact ⟨_, rfl⟩

theorem scratch_popLocal_inv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s s' : TcState .anon}
    {tyV : Lean4Lean.VExpr}
    (hI : WhnfStateInv layer semantics trProj world support uvars
      ((none, .vlam tyV) :: Delta) s)
    (hrun : TcM.popLocal s = .ok () s') :
    WhnfStateInv layer semantics trProj world support uvars Delta s' := by
  obtain ⟨henv, hctx, hlet, hnum, hlctx, hprims, hnoAccel, hequiv⟩ :=
    scratch_popLocal_run hI.2.1 hrun
  refine ⟨?_, ?_, ?_⟩
  · exact {
      core := hI.1.core.of_env_eq henv
      internSupport := by simpa only [henv] using hI.1.internSupport
      caches := by simpa only [henv] using hI.1.caches
      equivalences := by simpa only [hequiv] using hI.1.equivalences }
  · exact hI.2.1.pop_lam hctx hlet hnum hlctx (by simp [henv])
  · cases layer with
    | structuralNoAccel =>
        simpa only [WhnfLayer.StateOK, hnoAccel] using hI.2.2
    | noAccel =>
        simpa only [WhnfLayer.StateOK, hprims, hnoAccel] using hI.2.2
    | accelerated =>
      simpa only [WhnfLayer.StateOK, hprims] using hI.2.2

inductive ScratchLamExtension (base : KVLCtx) : Nat → KVLCtx → Prop
  | zero : ScratchLamExtension base 0 base
  | succ {n : Nat} {current : KVLCtx} {tyV : Lean4Lean.VExpr} :
      ScratchLamExtension base n current →
      ScratchLamExtension base (n + 1) ((none, .vlam tyV) :: current)

namespace ScratchLamExtension

theorem bvars {base : KVLCtx} :
    ∀ {n current}, ScratchLamExtension base n current →
      current.bvars = base.bvars + n
  | _, _, .zero => rfl
  | _, _, .succ h => by
      simp only [KVLCtx.bvars, bvars h]
      omega

end ScratchLamExtension

theorem scratch_restoreDepth_go
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars saved : Nat} {base : KVLCtx}
    (hbase : base.bvars = saved)
    {n current s}
    (hExtension : ScratchLamExtension base n current)
    (hI : WhnfStateInv layer semantics trProj world support uvars current s) :
    ∃ final,
      TcM.restoreDepth.go (m := .anon) saved n s = .ok () final ∧
        WhnfStateInv layer semantics trProj world support uvars base final := by
  induction hExtension generalizing s with
  | zero => exact ⟨_, rfl, hI⟩
  | @succ n current tyV hExtension ih =>
      have hgt : s.ctx.size > saved := by
        rw [← hI.2.1.bvars_eq, ScratchLamExtension.bvars (.succ hExtension),
          hbase]
        omega
      cases hpop : TcM.popLocal s with
      | error err after =>
          obtain ⟨actual, hactual⟩ := scratch_popLocal_ok s
          rw [hpop] at hactual
          contradiction
      | ok value after =>
          cases value
          have hAfter := scratch_popLocal_inv hI hpop
          obtain ⟨final, hgo, hFinal⟩ :=
            ih hAfter
          refine ⟨final, ?_, hFinal⟩
          rw [TcM.restoreDepth.go.eq_2]
          change EStateM.bind (get : TcM .anon (TcState .anon))
            (fun observed =>
              if observed.ctx.size > saved then do
                TcM.popLocal
                TcM.restoreDepth.go saved n
              else pure ()) s = .ok () final
          unfold EStateM.bind
          rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
          simp only [hgt, if_true]
          change EStateM.bind TcM.popLocal
            (fun _ => TcM.restoreDepth.go saved n) s = .ok () final
          unfold EStateM.bind
          rw [hpop]
          simp only
          exact hgo

theorem scratch_restoreDepth
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {base current : KVLCtx} {n : Nat}
    {initial s : TcState .anon}
    (hInitial : WhnfStateInv layer semantics trProj world support uvars
      base initial)
    (hExtension : ScratchLamExtension base n current)
    (hI : WhnfStateInv layer semantics trProj world support uvars current s) :
    ∃ final,
      TcM.restoreDepth (m := .anon) initial.ctx.size s = .ok () final ∧
        WhnfStateInv layer semantics trProj world support uvars base final := by
  have hbase : base.bvars = initial.ctx.size := hInitial.2.1.bvars_eq
  have hcurrent : s.ctx.size - initial.ctx.size = n := by
    rw [← hI.2.1.bvars_eq, ScratchLamExtension.bvars hExtension, hbase]
    omega
  obtain ⟨final, hgo, hFinal⟩ :=
    scratch_restoreDepth_go hbase hExtension hI
  refine ⟨final, ?_, hFinal⟩
  unfold TcM.restoreDepth
  change TcM.restoreDepth.go initial.ctx.size
    (s.ctx.size - initial.ctx.size) s = .ok () final
  rw [hcurrent, hgo]

theorem scratch_bind_ok
    {ε σ α β : Type} {x : EStateM ε σ α} {f : α → EStateM ε σ β}
    {s after : σ} {value : α}
    (hrun : x s = .ok value after) :
    (x >>= f) s = f value after := by
  change EStateM.bind x f s = f value after
  unfold EStateM.bind
  rw [hrun]

theorem scratch_bind_error
    {ε σ α β : Type} {x : EStateM ε σ α} {f : α → EStateM ε σ β}
    {s after : σ} {err : ε}
    (hrun : x s = .error err after) :
    (x >>= f) s = .error err after := by
  change EStateM.bind x f s = .error err after
  unfold EStateM.bind
  rw [hrun]

namespace RecM

structure ScratchTelescopeInputSupport (support : RunSupport) : Prop where
  body : ∀ {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
      {dom body : KExpr .anon} {info : ExprInfo .anon},
    support (.all name bi dom body info) → support body

def ScratchScopedState
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (base : KVLCtx) (s : TcState .anon) : Prop :=
  ∃ n current,
    ScratchLamExtension base n current ∧
      WhnfStateInv layer semantics trProj world support uvars current s

def ScratchScopedExpr
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (base : KVLCtx) (e : KExpr .anon)
    (s : TcState .anon) : Prop :=
  ∃ n current eV,
    ScratchLamExtension base n current ∧
      WhnfStateInv layer semantics trProj world support uvars current s ∧
      support e ∧
      TrKExprS world.venv uvars world.nameOf trProj current e eV

theorem scratch_peelMajorForalls_succ_run
    (fuel : Nat) (ty : KExpr .anon) (methods : Methods .anon)
    (s : TcState .anon) :
    (peelMajorForalls (fuel + 1) ty).run methods s =
      (methods.whnf ty >>= fun reduced =>
        ((match reduced with
        | .all _ _ dom body _ => do
            TcM.pushLocal dom
            peelMajorForalls fuel body
        | _ => throw (TcError.other
            "get_major_inductive_id: not enough foralls")) :
          RecM .anon (KExpr .anon)).run methods) s := by
  have hwhnf :
      (whnfRec ty).run methods = methods.whnf ty := by
    funext state
    exact whnfRec_run ty methods state
  rw [peelMajorForalls, ReaderT.run_bind, hwhnf]
  apply congrArg
    (fun continuation : KExpr .anon → TcM .anon (KExpr .anon) =>
      (methods.whnf ty >>= continuation) s)
  funext reduced
  cases reduced <;> rfl

theorem scratch_peelMajorForalls_scoped
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ScratchTelescopeInputSupport support)
    {base : KVLCtx} :
    ∀ fuel {n current ty s tyV},
      ScratchLamExtension base n current →
      support ty →
      TrKExprS world.venv uvars world.nameOf trProj current ty tyV →
      WhnfStateInv layer semantics trProj world support uvars current s →
      match (peelMajorForalls fuel ty).run methods s with
      | .ok result after =>
          ScratchScopedExpr layer semantics trProj world support uvars base
            result after
      | .error _ after =>
          ScratchScopedState layer semantics trProj world support uvars base
            after
  | 0, _, _, _, _, _, hExtension, hsupport, htr, hI => by
      exact ⟨_, _, _, hExtension, hI, hsupport, htr⟩
  | fuel + 1, n, current, source, s, sourceV, hExtension, hsupport, htr,
      hI => by
      have hcallback := hmethods.whnf hsupport htr hI
      cases hrun : methods.whnf source s with
      | error err after =>
          rw [hrun] at hcallback
          have hwhole :
              (peelMajorForalls (fuel + 1) source).run methods s =
                .error err after := by
            rw [scratch_peelMajorForalls_succ_run]
            exact scratch_bind_error hrun
          rw [hwhole]
          exact ⟨n, current, hExtension, hcallback.1⟩
      | ok reduced after =>
          rw [hrun] at hcallback
          cases reduced
          case all name bi dom body info =>
              obtain ⟨resultV, hresultTr, _⟩ := hcallback.2.2
              cases hresultTr with
              | all hdomType hbodyType hdomTr hbodyTr =>
                  obtain ⟨afterPush, hpush⟩ :=
                    scratch_pushLocal_ok dom after
                  have hPushI :=
                    scratch_pushLocal_inv hcallback.1 hdomTr hdomType hpush
                  have hbodySupport := hinputs.body hcallback.2.1
                  have hrecursive :=
                    scratch_peelMajorForalls_scoped hmethods hinputs fuel
                      (.succ hExtension) hbodySupport hbodyTr hPushI
                  cases hrec :
                      (peelMajorForalls fuel body).run methods afterPush with
                  | ok result final =>
                      rw [hrec] at hrecursive
                      have hwhole :
                          (peelMajorForalls (fuel + 1) source).run methods s =
                            .ok result final := by
                        rw [scratch_peelMajorForalls_succ_run,
                          scratch_bind_ok hrun]
                        rw [ReaderT.run_bind, ReaderT.run_monadLift,
                          monadLift_self,
                          scratch_bind_ok hpush, hrec]
                      rw [hwhole]
                      exact hrecursive
                  | error recErr final =>
                      rw [hrec] at hrecursive
                      have hwhole :
                          (peelMajorForalls (fuel + 1) source).run methods s =
                            .error recErr final := by
                        rw [scratch_peelMajorForalls_succ_run,
                          scratch_bind_ok hrun]
                        rw [ReaderT.run_bind, ReaderT.run_monadLift,
                          monadLift_self,
                          scratch_bind_ok hpush, hrec]
                      rw [hwhole]
                      exact hrecursive
          all_goals
              have hwhole :
                  (peelMajorForalls (fuel + 1) source).run methods s =
                    .error (.other
                      "get_major_inductive_id: not enough foralls") after := by
                rw [scratch_peelMajorForalls_succ_run,
                  scratch_bind_ok hrun]
                rfl
              rw [hwhole]
              exact ⟨n, current, hExtension, hcallback.1⟩

private theorem scratch_collectSpineGo_const_references
    {id : KId .anon} {us : Array (KUniv .anon)}
    {info : ExprInfo .anon} :
    ∀ (e : KExpr .anon) (acc args : Array (KExpr .anon)),
      KExpr.collectSpine.go e acc = (.const id us info, args) →
      e.References id
  | .app f a appInfo, acc, args, h => by
      simp only [KExpr.collectSpine.go] at h
      exact Or.inl
        (scratch_collectSpineGo_const_references f (acc.push a) args h)
  | .const actual actualUs actualInfo, acc, args, h => by
      simp only [KExpr.collectSpine.go] at h
      cases h
      rfl
  | .var .., _, _, h
  | .fvar .., _, _, h
  | .sort .., _, _, h
  | .lam .., _, _, h
  | .all .., _, _, h
  | .letE .., _, _, h
  | .prj .., _, _, h
  | .nat .., _, _, h
  | .str .., _, _, h => by
      simp only [KExpr.collectSpine.go] at h
      cases h

theorem scratch_collectSpine_const_references
    {e : KExpr .anon} {id : KId .anon}
    {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)}
    (h : e.collectSpine = (.const id us info, args)) :
    e.References id :=
  scratch_collectSpineGo_const_references e #[] args h

def ScratchScopedId
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (base : KVLCtx) (id : KId .anon)
    (s : TcState .anon) : Prop :=
  ScratchScopedState layer semantics trProj world support uvars base s ∧
    world.trusted id

def ScratchTrustedReferences (world : VerifyWorld)
    (support : RunSupport) : Prop :=
  ∀ {source : KExpr .anon} {id : KId .anon},
    support source → source.References id → world.trusted id

theorem scratch_scanMajorInductive_succ_run
    (fuel : Nat) (ty : KExpr .anon) (methods : Methods .anon)
    (s : TcState .anon) :
    (scanMajorInductive (fuel + 1) ty).run methods s =
      (methods.whnf ty >>= fun reduced =>
        (scanMajorInductiveStep (scanMajorInductive fuel) reduced).run
          methods) s := by
  have hwhnf :
      (whnfRec ty).run methods = methods.whnf ty := by
    funext state
    exact whnfRec_run ty methods state
  rw [scanMajorInductive, ReaderT.run_bind, hwhnf]

theorem scratch_scanMajorInductive_scoped
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ScratchTelescopeInputSupport support)
    (hfault : ∀ {Delta : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hreferences : ScratchTrustedReferences world support)
    {base : KVLCtx} :
    ∀ fuel {n current ty s tyV},
      ScratchLamExtension base n current →
      support ty →
      TrKExprS world.venv uvars world.nameOf trProj current ty tyV →
      WhnfStateInv layer semantics trProj world support uvars current s →
      match (scanMajorInductive fuel ty).run methods s with
      | .ok id after =>
          ScratchScopedId layer semantics trProj world support uvars base
            id after
      | .error _ after =>
          ScratchScopedState layer semantics trProj world support uvars base
            after
  | 0, n, current, source, s, sourceV, hExtension, hsupport, htr, hI => by
      exact ⟨n, current, hExtension, hI⟩
  | fuel + 1, n, current, source, s, sourceV, hExtension, hsupport, htr,
      hI => by
      have hcallback := hmethods.whnf hsupport htr hI
      cases hrun : methods.whnf source s with
      | error err after =>
          rw [hrun] at hcallback
          have hwhole :
              (scanMajorInductive (fuel + 1) source).run methods s =
                .error err after := by
            rw [scratch_scanMajorInductive_succ_run]
            exact scratch_bind_error hrun
          rw [hwhole]
          exact ⟨n, current, hExtension, hcallback.1⟩
      | ok reduced after =>
          rw [hrun] at hcallback
          cases reduced
          case all name bi dom body info =>
              obtain ⟨resultV, hresultTr, _⟩ := hcallback.2.2
              cases hresultTr with
              | all hdomType hbodyType hdomTr hbodyTr =>
                  have hbodySupport := hinputs.body hcallback.2.1
                  have hcontinue :
                      ∀ {before : TcState .anon},
                        WhnfStateInv layer semantics trProj world support
                          uvars current before →
                        match
                          ((do
                            TcM.pushLocal dom
                            scanMajorInductive fuel body) :
                              RecM .anon (KId .anon)).run methods before with
                        | .ok id final =>
                            ScratchScopedId layer semantics trProj world
                              support uvars base id final
                        | .error _ final =>
                            ScratchScopedState layer semantics trProj world
                              support uvars base final := by
                    intro before hBefore
                    obtain ⟨afterPush, hpush⟩ :=
                      scratch_pushLocal_ok dom before
                    have hPushI :=
                      scratch_pushLocal_inv hBefore hdomTr hdomType hpush
                    have hrecursive :=
                      scratch_scanMajorInductive_scoped hmethods hinputs
                        hfault hreferences fuel (.succ hExtension)
                        hbodySupport hbodyTr hPushI
                    cases hrec :
                        (scanMajorInductive fuel body).run methods afterPush with
                    | ok id final =>
                        rw [hrec] at hrecursive
                        have hwhole :
                            ((do
                              TcM.pushLocal dom
                              scanMajorInductive fuel body) :
                                RecM .anon (KId .anon)).run methods before =
                              .ok id final := by
                          rw [ReaderT.run_bind, ReaderT.run_monadLift,
                            monadLift_self, scratch_bind_ok hpush, hrec]
                        rw [hwhole]
                        exact hrecursive
                    | error recErr final =>
                        rw [hrec] at hrecursive
                        have hwhole :
                            ((do
                              TcM.pushLocal dom
                              scanMajorInductive fuel body) :
                                RecM .anon (KId .anon)).run methods before =
                              .error recErr final := by
                          rw [ReaderT.run_bind, ReaderT.run_monadLift,
                            monadLift_self, scratch_bind_ok hpush, hrec]
                        rw [hwhole]
                        exact hrecursive
                  rcases hspine : dom.collectSpine with ⟨head, args⟩
                  rw [scratch_scanMajorInductive_succ_run,
                    scratch_bind_ok hrun]
                  simp only [scanMajorInductiveStep, hspine]
                  cases head <;> try exact hcontinue hcallback.1
                  case const id us headInfo =>
                    have hlookup :=
                      TcM.tryGetConst_wf (hfault (Delta := current)) id
                        after hcallback.1
                    cases hlookupRun : TcM.tryGetConst id after with
                    | error lookupErr afterLookup =>
                        rw [hlookupRun] at hlookup
                        rw [ReaderT.run_bind, ReaderT.run_monadLift,
                          monadLift_self,
                          scratch_bind_error hlookupRun]
                        exact ⟨n, current, hExtension, hlookup.1⟩
                    | ok found afterLookup =>
                        rw [hlookupRun] at hlookup
                        rw [ReaderT.run_bind, ReaderT.run_monadLift,
                          monadLift_self, scratch_bind_ok hlookupRun]
                        cases found with
                        | none => exact hcontinue hlookup.1
                        | some entry =>
                            cases entry <;> simp only
                            case indc =>
                              exact
                                ⟨⟨n, current, hExtension, hlookup.1⟩,
                                  hreferences hcallback.2.1 <| by
                                    simp only [KExpr.References]
                                    exact Or.inl
                                      (scratch_collectSpine_const_references
                                        hspine)⟩
                            all_goals exact hcontinue hlookup.1
          all_goals
              have hwhole :
                  (scanMajorInductive (fuel + 1) source).run methods s =
                    .error (.other
                      "get_major_inductive_id: expected forall at major")
                      after := by
                rw [scratch_scanMajorInductive_succ_run,
                  scratch_bind_ok hrun]
                rfl
              rw [hwhole]
              exact ⟨n, current, hExtension, hcallback.1⟩

theorem scratch_majorInductiveBody_scoped
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ScratchTelescopeInputSupport support)
    (hfault : ∀ {Delta : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hreferences : ScratchTrustedReferences world support)
    {base : KVLCtx} {recTy : KExpr .anon} {recTyV : Lean4Lean.VExpr}
    {s : TcState .anon} (skip : UInt64)
    (hrecSupport : support recTy)
    (hrecTr : TrKExprS world.venv uvars world.nameOf trProj base recTy recTyV)
    (hI : WhnfStateInv layer semantics trProj world support uvars base s) :
    match
      ((do
        let ty ← peelMajorForalls skip.toNat recTy
        scanMajorInductive 9 ty) : RecM .anon (KId .anon)).run methods s with
    | .ok id after =>
        ScratchScopedId layer semantics trProj world support uvars base id after
    | .error _ after =>
        ScratchScopedState layer semantics trProj world support uvars base
          after := by
  have hpeel :=
    scratch_peelMajorForalls_scoped hmethods hinputs skip.toNat
      (ScratchLamExtension.zero (base := base)) hrecSupport hrecTr hI
  cases hpeelRun :
      (peelMajorForalls skip.toNat recTy).run methods s with
  | error err after =>
      rw [hpeelRun] at hpeel
      rw [ReaderT.run_bind, scratch_bind_error hpeelRun]
      exact hpeel
  | ok ty after =>
      rw [hpeelRun] at hpeel
      obtain ⟨n, current, tyV, hExtension, hAfter, htySupport, htyTr⟩ :=
        hpeel
      have hscan :=
        scratch_scanMajorInductive_scoped hmethods hinputs hfault hreferences 9
          hExtension htySupport htyTr hAfter
      cases hscanRun : (scanMajorInductive 9 ty).run methods after with
      | error err final =>
          rw [hscanRun] at hscan
          rw [ReaderT.run_bind, scratch_bind_ok hpeelRun, hscanRun]
          exact hscan
      | ok id final =>
          rw [hscanRun] at hscan
          rw [ReaderT.run_bind, scratch_bind_ok hpeelRun, hscanRun]
          exact hscan

theorem scratch_getMajorInductiveId_run
    (recTy : KExpr .anon) (skip : UInt64) (methods : Methods .anon)
    (s : TcState .anon) :
    (getMajorInductiveId recTy skip).run methods s =
      tryFinally
        (((do
          let ty ← peelMajorForalls skip.toNat recTy
          scanMajorInductive 9 ty) : RecM .anon (KId .anon)).run methods)
        (TcM.restoreDepth s.ctx.size) s := by
  rfl

theorem scratch_tryFinally_ok
    {ε σ α β : Type} {x : EStateM ε σ α}
    {finalizer : EStateM ε σ β} {s after final : σ}
    {value : α} {cleanup : β}
    (hbody : x s = .ok value after)
    (hcleanup : finalizer after = .ok cleanup final) :
    tryFinally x finalizer s = .ok value final := by
  unfold tryFinally
  change EStateM.map (fun pair : α × β => pair.1)
    (tryFinally' x (fun _ => finalizer)) s = .ok value final
  unfold EStateM.map MonadFinally.tryFinally' EStateM.instMonadFinally
  simp only [hbody, hcleanup]

theorem scratch_tryFinally_error
    {ε σ α β : Type} {x : EStateM ε σ α}
    {finalizer : EStateM ε σ β} {s after final : σ}
    {err : ε} {cleanup : β}
    (hbody : x s = .error err after)
    (hcleanup : finalizer after = .ok cleanup final) :
    tryFinally x finalizer s = .error err final := by
  unfold tryFinally
  change EStateM.map (fun pair : α × β => pair.1)
    (tryFinally' x (fun _ => finalizer)) s = .error err final
  unfold EStateM.map MonadFinally.tryFinally' EStateM.instMonadFinally
  simp only [hbody, hcleanup]

theorem scratch_getMajorInductiveId_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ScratchTelescopeInputSupport support)
    (hfault : ∀ {Delta : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hreferences : ScratchTrustedReferences world support)
    {Delta : KVLCtx} {recTy : KExpr .anon} {recTyV : Lean4Lean.VExpr}
    {s : TcState .anon} (skip : UInt64)
    (hrecSupport : support recTy)
    (hrecTr :
      TrKExprS world.venv uvars world.nameOf trProj Delta recTy recTyV) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((getMajorInductiveId recTy skip).run methods)
      (fun id _ => world.trusted id) := by
  intro hI
  have hbody :=
    scratch_majorInductiveBody_scoped hmethods hinputs hfault hreferences
      skip hrecSupport hrecTr hI
  cases hbodyRun :
      ((do
        let ty ← peelMajorForalls skip.toNat recTy
        scanMajorInductive 9 ty) : RecM .anon (KId .anon)).run methods s with
  | ok id after =>
      rw [hbodyRun] at hbody
      obtain ⟨⟨n, current, hExtension, hAfter⟩, htrusted⟩ := hbody
      obtain ⟨final, hrestore, hFinal⟩ :=
        scratch_restoreDepth hI hExtension hAfter
      have hrun :
          (getMajorInductiveId recTy skip).run methods s = .ok id final := by
        rw [scratch_getMajorInductiveId_run]
        exact scratch_tryFinally_ok hbodyRun hrestore
      rw [hrun]
      exact ⟨hFinal, htrusted⟩
  | error err after =>
      rw [hbodyRun] at hbody
      obtain ⟨n, current, hExtension, hAfter⟩ := hbody
      obtain ⟨final, hrestore, hFinal⟩ :=
        scratch_restoreDepth hI hExtension hAfter
      have hrun :
          (getMajorInductiveId recTy skip).run methods s = .error err final := by
        rw [scratch_getMajorInductiveId_run]
        exact scratch_tryFinally_error hbodyRun hrestore
      rw [hrun]
      exact ⟨hFinal, trivial⟩

end RecM
end Ix.Tc
