import Ix.Tc.Verify.Whnf.StructEta.ScopedTelescope

/-!
# Scoped recursion-classifier steps

This module lifts the scoped telescope invariant through the individual
classifier callbacks and bounded iteration steps.  It records both successful
results and partial-error states before the complete classifier loop is
assembled.
-/

namespace Ix.Tc
namespace RecM

def ScratchScopedForInStep
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (base : KVLCtx) :
    ForInStep (KExpr .anon) → TcState .anon → Prop
  | .done e, s
  | .yield e, s =>
      ScratchScopedExpr layer semantics trProj world support uvars base e s

def ScratchScopedBoundedStep
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (base : KVLCtx) :
    BoundedStep (KExpr .anon) Bool → TcState .anon → Prop
  | .done _, s =>
      ScratchScopedState layer semantics trProj world support uvars base s
  | .next e, s =>
      ScratchScopedExpr layer semantics trProj world support uvars base e s

theorem scratch_computeIsRecParamStep_run
    (ty : KExpr .anon) (methods : Methods .anon) (s : TcState .anon) :
    (computeIsRecParamStep ty).run methods s =
      (methods.whnf ty >>= fun reduced =>
        (computeIsRecParamStepAfterWhnf ty reduced).run methods) s := by
  have hwhnf :
      (whnfRec ty).run methods = methods.whnf ty := by
    funext state
    exact whnfRec_run ty methods state
  rw [computeIsRecParamStep, ReaderT.run_bind, hwhnf]

theorem scratch_computeIsRecParamStep_scoped
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ScratchTelescopeInputSupport support)
    {base : KVLCtx} {n : Nat} {current : KVLCtx}
    {ty : KExpr .anon} {tyV : Lean4Lean.VExpr} {s : TcState .anon}
    (hExtension : ScratchLamExtension base n current)
    (hsupport : support ty)
    (htr : TrKExprS world.venv uvars world.nameOf trProj current ty tyV)
    (hI : WhnfStateInv layer semantics trProj world support uvars current s) :
    match (computeIsRecParamStep ty).run methods s with
    | .ok step after =>
        ScratchScopedForInStep layer semantics trProj world support uvars base
          step after
    | .error _ after =>
        ScratchScopedState layer semantics trProj world support uvars base
          after := by
  have hcallback := hmethods.whnf hsupport htr hI
  cases hrun : methods.whnf ty s with
  | error err after =>
      rw [hrun] at hcallback
      have hwhole :
          (computeIsRecParamStep ty).run methods s = .error err after := by
        rw [scratch_computeIsRecParamStep_run]
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
          obtain ⟨afterPush, hpush⟩ := scratch_pushLocal_ok dom after
          have hPushI :=
            scratch_pushLocal_inv hcallback.1 hdomTr hdomType hpush
          have hwhole :
              (computeIsRecParamStep ty).run methods s =
                .ok (.yield body) afterPush := by
            rw [scratch_computeIsRecParamStep_run, scratch_bind_ok hrun,
              computeIsRecParamStepAfterWhnf, ReaderT.run_bind,
              ReaderT.run_monadLift, monadLift_self, scratch_bind_ok hpush]
            rfl
          rw [hwhole]
          exact ⟨n + 1, _, _, .succ hExtension, hPushI,
            hinputs.body hcallback.2.1, hbodyTr⟩
      all_goals
        have hwhole :
            (computeIsRecParamStep ty).run methods s =
              .ok (.done ty) after := by
          rw [scratch_computeIsRecParamStep_run, scratch_bind_ok hrun]
          simp [computeIsRecParamStepAfterWhnf]
        rw [hwhole]
        exact ⟨n, current, tyV, hExtension, hcallback.1, hsupport, htr⟩

theorem scratch_computeIsRecFieldStep_run
    (blockAddrs : Array Address) (ty : KExpr .anon)
    (methods : Methods .anon) (s : TcState .anon) :
    (computeIsRecFieldStep blockAddrs ty).run methods s =
      (methods.whnf ty >>= fun reduced =>
        (computeIsRecFieldStepAfterWhnf blockAddrs reduced).run methods) s := by
  have hwhnf :
      (whnfRec ty).run methods = methods.whnf ty := by
    funext state
    exact whnfRec_run ty methods state
  rw [computeIsRecFieldStep, ReaderT.run_bind, hwhnf]

theorem scratch_computeIsRecFieldStep_scoped
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ScratchTelescopeInputSupport support)
    {base : KVLCtx} {n : Nat} {current : KVLCtx}
    {blockAddrs : Array Address}
    {ty : KExpr .anon} {tyV : Lean4Lean.VExpr} {s : TcState .anon}
    (hExtension : ScratchLamExtension base n current)
    (hsupport : support ty)
    (htr : TrKExprS world.venv uvars world.nameOf trProj current ty tyV)
    (hI : WhnfStateInv layer semantics trProj world support uvars current s) :
    match (computeIsRecFieldStep blockAddrs ty).run methods s with
    | .ok step after =>
        ScratchScopedBoundedStep layer semantics trProj world support uvars base
          step after
    | .error _ after =>
        ScratchScopedState layer semantics trProj world support uvars base
          after := by
  have hcallback := hmethods.whnf hsupport htr hI
  cases hrun : methods.whnf ty s with
  | error err after =>
      rw [hrun] at hcallback
      have hwhole :
          (computeIsRecFieldStep blockAddrs ty).run methods s =
            .error err after := by
        rw [scratch_computeIsRecFieldStep_run]
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
          cases hmentions : exprMentionsAnyAddr dom blockAddrs with
          | false =>
              obtain ⟨afterPush, hpush⟩ := scratch_pushLocal_ok dom after
              have hPushI :=
                scratch_pushLocal_inv hcallback.1 hdomTr hdomType hpush
              have hwhole :
                  (computeIsRecFieldStep blockAddrs ty).run methods s =
                    .ok (.next body) afterPush := by
                rw [scratch_computeIsRecFieldStep_run, scratch_bind_ok hrun,
                  computeIsRecFieldStepAfterWhnf, hmentions]
                simp only [Bool.false_eq_true, if_false, pure_bind]
                rw [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self,
                  scratch_bind_ok hpush]
                rfl
              rw [hwhole]
              exact ⟨n + 1, _, _, .succ hExtension, hPushI,
                hinputs.body hcallback.2.1, hbodyTr⟩
          | true =>
              have hwhole :
                  (computeIsRecFieldStep blockAddrs ty).run methods s =
                    .ok (.done true) after := by
                rw [scratch_computeIsRecFieldStep_run, scratch_bind_ok hrun]
                simp [computeIsRecFieldStepAfterWhnf, hmentions]
              rw [hwhole]
              exact ⟨n, current, hExtension, hcallback.1⟩
      all_goals
        have hwhole :
            (computeIsRecFieldStep blockAddrs ty).run methods s =
              .ok (.done false) after := by
          rw [scratch_computeIsRecFieldStep_run, scratch_bind_ok hrun]
          simp [computeIsRecFieldStepAfterWhnf]
        rw [hwhole]
        exact ⟨n, current, hExtension, hcallback.1⟩

theorem scratch_computeIsRecParams_scoped
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ScratchTelescopeInputSupport support)
    {base : KVLCtx} :
    ∀ (indices : List Nat) {n current ty s tyV},
      ScratchLamExtension base n current →
      support ty →
      TrKExprS world.venv uvars world.nameOf trProj current ty tyV →
      WhnfStateInv layer semantics trProj world support uvars current s →
      match
        (forIn (m := RecM .anon) indices ty
          (fun _ ty => computeIsRecParamStep ty)).run methods s
      with
      | .ok result after =>
          ScratchScopedExpr layer semantics trProj world support uvars base
            result after
      | .error _ after =>
          ScratchScopedState layer semantics trProj world support uvars base
            after
  | [], n, current, ty, s, tyV, hExtension, hsupport, htr, hI => by
      rw [List.forIn_nil]
      exact ⟨n, current, tyV, hExtension, hI, hsupport, htr⟩
  | index :: indices, n, current, ty, s, tyV, hExtension, hsupport, htr, hI => by
      have hstep :=
        scratch_computeIsRecParamStep_scoped hmethods hinputs hExtension
          hsupport htr hI
      cases hrun : (computeIsRecParamStep ty).run methods s with
      | error err after =>
          rw [hrun] at hstep
          have hwhole :
              (forIn (m := RecM .anon) (index :: indices) ty
                (fun _ ty => computeIsRecParamStep ty)).run methods s =
                .error err after := by
            rw [List.forIn_cons, ReaderT.run_bind]
            exact scratch_bind_error hrun
          rw [hwhole]
          exact hstep
      | ok action after =>
          rw [hrun] at hstep
          cases action with
          | done result =>
              have hwhole :
                  (forIn (m := RecM .anon) (index :: indices) ty
                    (fun _ ty => computeIsRecParamStep ty)).run methods s =
                    .ok result after := by
                rw [List.forIn_cons, ReaderT.run_bind,
                  scratch_bind_ok hrun]
                rfl
              rw [hwhole]
              exact hstep
          | yield next =>
              obtain ⟨nextN, nextCurrent, nextV, nextExtension, hAfter,
                hnextSupport, hnextTr⟩ := hstep
              have htail :=
                scratch_computeIsRecParams_scoped hmethods hinputs indices
                  nextExtension hnextSupport hnextTr hAfter
              cases htailRun :
                  (forIn (m := RecM .anon) indices next
                    (fun _ ty => computeIsRecParamStep ty)).run methods after with
              | error tailErr final =>
                  rw [htailRun] at htail
                  have hwhole :
                      (forIn (m := RecM .anon) (index :: indices) ty
                        (fun _ ty => computeIsRecParamStep ty)).run methods s =
                        .error tailErr final := by
                    rw [List.forIn_cons, ReaderT.run_bind,
                      scratch_bind_ok hrun]
                    exact htailRun
                  rw [hwhole]
                  exact htail
              | ok result final =>
                  rw [htailRun] at htail
                  have hwhole :
                      (forIn (m := RecM .anon) (index :: indices) ty
                        (fun _ ty => computeIsRecParamStep ty)).run methods s =
                        .ok result final := by
                    rw [List.forIn_cons, ReaderT.run_bind,
                      scratch_bind_ok hrun]
                    exact htailRun
                  rw [hwhole]
                  exact htail

theorem scratch_computeIsRecFields_scoped
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ScratchTelescopeInputSupport support)
    {base : KVLCtx} {blockAddrs : Array Address} :
    ∀ fuel {n current ty s tyV},
      ScratchLamExtension base n current →
      support ty →
      TrKExprS world.venv uvars world.nameOf trProj current ty tyV →
      WhnfStateInv layer semantics trProj world support uvars current s →
      match
        (runBounded (computeIsRecFieldStep blockAddrs) fuel ty).run methods s
      with
      | .ok _ after =>
          ScratchScopedState layer semantics trProj world support uvars base
            after
      | .error _ after =>
          ScratchScopedState layer semantics trProj world support uvars base
            after
  | 0, n, current, ty, s, tyV, hExtension, hsupport, htr, hI => by
      rw [runBounded]
      exact ⟨n, current, hExtension, hI⟩
  | fuel + 1, n, current, ty, s, tyV, hExtension, hsupport, htr, hI => by
      have hstep :=
        scratch_computeIsRecFieldStep_scoped (blockAddrs := blockAddrs)
          hmethods hinputs hExtension hsupport htr hI
      cases hrun :
          (computeIsRecFieldStep blockAddrs ty).run methods s with
      | error err after =>
          rw [hrun] at hstep
          have hwhole :
              (runBounded (computeIsRecFieldStep blockAddrs) (fuel + 1) ty).run
                  methods s =
                .error err after := by
            rw [runBounded, ReaderT.run_bind]
            exact scratch_bind_error hrun
          rw [hwhole]
          exact hstep
      | ok action after =>
          rw [hrun] at hstep
          cases action with
          | done result =>
              have hwhole :
                  (runBounded (computeIsRecFieldStep blockAddrs) (fuel + 1)
                      ty).run methods s =
                    .ok result after := by
                rw [runBounded, ReaderT.run_bind, scratch_bind_ok hrun]
                rfl
              rw [hwhole]
              exact hstep
          | next next =>
              obtain ⟨nextN, nextCurrent, nextV, nextExtension, hAfter,
                hnextSupport, hnextTr⟩ := hstep
              have htail :=
                scratch_computeIsRecFields_scoped (blockAddrs := blockAddrs)
                  hmethods hinputs fuel nextExtension hnextSupport hnextTr hAfter
              cases htailRun :
                  (runBounded (computeIsRecFieldStep blockAddrs) fuel next).run
                    methods after with
              | error tailErr final =>
                  rw [htailRun] at htail
                  have hwhole :
                      (runBounded (computeIsRecFieldStep blockAddrs) (fuel + 1)
                          ty).run methods s =
                        .error tailErr final := by
                    rw [runBounded, ReaderT.run_bind,
                      scratch_bind_ok hrun]
                    exact htailRun
                  rw [hwhole]
                  exact htail
              | ok result final =>
                  rw [htailRun] at htail
                  have hwhole :
                      (runBounded (computeIsRecFieldStep blockAddrs) (fuel + 1)
                          ty).run methods s =
                        .ok result final := by
                    rw [runBounded, ReaderT.run_bind,
                      scratch_bind_ok hrun]
                    exact htailRun
                  rw [hwhole]
                  exact htail

theorem scratch_computeIsRecCtorBody_scoped
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ScratchTelescopeInputSupport support)
    {base : KVLCtx} {ctorTy : KExpr .anon}
    {ctorTyV : Lean4Lean.VExpr} {s : TcState .anon}
    (nParams : Nat) (blockAddrs : Array Address)
    (hctorSupport : support ctorTy)
    (hctorTr :
      TrKExprS world.venv uvars world.nameOf trProj base ctorTy ctorTyV)
    (hI : WhnfStateInv layer semantics trProj world support uvars base s) :
    match
      ((do
        let ty ← forIn [0:nParams] ctorTy fun _ ty =>
          computeIsRecParamStep ty
        runBounded (computeIsRecFieldStep blockAddrs) maxWhnfFuel.toNat ty) :
          RecM .anon Bool).run methods s
    with
    | .ok _ after =>
        ScratchScopedState layer semantics trProj world support uvars base after
    | .error _ after =>
        ScratchScopedState layer semantics trProj world support uvars base after := by
  rw [_root_.Std.Legacy.Range.forIn_eq_forIn_range']
  have hparams :=
    scratch_computeIsRecParams_scoped hmethods hinputs
      (List.range'
        ([0:nParams] : _root_.Std.Legacy.Range).start
        ([0:nParams] : _root_.Std.Legacy.Range).size
        ([0:nParams] : _root_.Std.Legacy.Range).step)
      (ScratchLamExtension.zero (base := base)) hctorSupport hctorTr hI
  cases hparamsRun :
      (forIn (m := RecM .anon)
        (List.range'
          ([0:nParams] : _root_.Std.Legacy.Range).start
          ([0:nParams] : _root_.Std.Legacy.Range).size
          ([0:nParams] : _root_.Std.Legacy.Range).step)
        ctorTy
        (fun _ ty => computeIsRecParamStep ty)).run methods s with
  | error err after =>
      rw [hparamsRun] at hparams
      rw [ReaderT.run_bind, scratch_bind_error hparamsRun]
      exact hparams
  | ok ty after =>
      rw [hparamsRun] at hparams
      obtain ⟨n, current, tyV, hExtension, hAfter, htySupport, htyTr⟩ :=
        hparams
      have hfields :=
        scratch_computeIsRecFields_scoped (blockAddrs := blockAddrs)
          hmethods hinputs maxWhnfFuel.toNat hExtension htySupport htyTr hAfter
      cases hfieldsRun :
          (runBounded (computeIsRecFieldStep blockAddrs) maxWhnfFuel.toNat
            ty).run methods after with
      | error err final =>
          rw [hfieldsRun] at hfields
          rw [ReaderT.run_bind, scratch_bind_ok hparamsRun, hfieldsRun]
          exact hfields
      | ok result final =>
          rw [hfieldsRun] at hfields
          rw [ReaderT.run_bind, scratch_bind_ok hparamsRun, hfieldsRun]
          exact hfields

theorem scratch_computeIsRecCtor_run
    (ctorTy : KExpr .anon) (nParams : Nat)
    (blockAddrs : Array Address) (methods : Methods .anon)
    (s : TcState .anon) :
    (computeIsRecCtor ctorTy nParams blockAddrs).run methods s =
      tryFinally
        (((do
          let ty ← forIn [0:nParams] ctorTy fun _ ty =>
            computeIsRecParamStep ty
          runBounded (computeIsRecFieldStep blockAddrs)
            maxWhnfFuel.toNat ty) : RecM .anon Bool).run methods)
        (TcM.restoreDepth s.ctx.size) s := by
  rfl

theorem scratch_computeIsRecCtor_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ScratchTelescopeInputSupport support)
    {Delta : KVLCtx} {ctorTy : KExpr .anon}
    {ctorTyV : Lean4Lean.VExpr} {s : TcState .anon}
    (nParams : Nat) (blockAddrs : Array Address)
    (hctorSupport : support ctorTy)
    (hctorTr :
      TrKExprS world.venv uvars world.nameOf trProj Delta ctorTy ctorTyV) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((computeIsRecCtor ctorTy nParams blockAddrs).run methods)
      (fun _ _ => True) := by
  intro hI
  have hbody :=
    scratch_computeIsRecCtorBody_scoped hmethods hinputs nParams blockAddrs
      hctorSupport hctorTr hI
  cases hbodyRun :
      ((do
        let ty ← forIn [0:nParams] ctorTy fun _ ty =>
          computeIsRecParamStep ty
        runBounded (computeIsRecFieldStep blockAddrs)
          maxWhnfFuel.toNat ty) : RecM .anon Bool).run methods s with
  | ok result after =>
      rw [hbodyRun] at hbody
      obtain ⟨n, current, hExtension, hAfter⟩ := hbody
      obtain ⟨final, hrestore, hFinal⟩ :=
        scratch_restoreDepth hI hExtension hAfter
      have hrun :
          (computeIsRecCtor ctorTy nParams blockAddrs).run methods s =
            .ok result final := by
        rw [scratch_computeIsRecCtor_run]
        exact scratch_tryFinally_ok hbodyRun hrestore
      rw [hrun]
      exact ⟨hFinal, trivial⟩
  | error err after =>
      rw [hbodyRun] at hbody
      obtain ⟨n, current, hExtension, hAfter⟩ := hbody
      obtain ⟨final, hrestore, hFinal⟩ :=
        scratch_restoreDepth hI hExtension hAfter
      have hrun :
          (computeIsRecCtor ctorTy nParams blockAddrs).run methods s =
            .error err final := by
        rw [scratch_computeIsRecCtor_run]
        exact scratch_tryFinally_error hbodyRun hrestore
      rw [hrun]
      exact ⟨hFinal, trivial⟩

end RecM
end Ix.Tc
