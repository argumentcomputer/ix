import Ix.Tc.Verify.Check.InferencePolicy
import Ix.Tc.Verify.Check.PreTranslationOpening
import Ix.Tc.Verify.Infer.BinderScopes
import Ix.Tc.Verify.Infer.LetScopes

/-!
# Binder scopes for pre-typed checker ingress

The ordinary inference scope theorem assumes the binder body already has a
typed `TrKExprS` witness.  K3 cannot make that assumption: full inference is
the operation which must construct the witness.  This wrapper combines the
factored operational binder-opening core with `PreTrKExprS.openFVarZero` and
the independent inference-policy frame.
-/

namespace Ix.Tc

namespace TcM

/-- Opening a binder with a typed domain and a merely pre-translated body
returns the exact opened body under the tagged pre-translation context. -/
theorem openBinder_pre_scope
    {support : RunSupport}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {type body : KExpr .anon} {typeV bodyV : Lean4Lean.VExpr}
    (htype : TrKExprS world.venv uvars world.nameOf trProj Delta type typeV)
    (htypeType : world.venv.IsType uvars Delta.toCtx typeV)
    (hbody : PreTrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam typeV) :: Delta) body bodyV)
    (hcollision : support.CollisionFree)
    (hresources : BinderOpeningResources support name body) :
    WhnfStateInv layer semantics trProj world support uvars Delta s →
    match TcM.openBinder name bi type body s with
    | .ok (bodyOpen, fvId) after =>
        fvId = ⟨s.env.nextFVarId⟩ ∧
        bodyOpen = KExpr.instantiateRevSpec body
          #[.mkFVar ⟨s.env.nextFVarId⟩ name] 0 ∧
        WhnfStateInv layer semantics trProj world support uvars
          ((some (⟨s.env.nextFVarId⟩, Delta.fvars), .vlam typeV) :: Delta)
          after ∧
        support bodyOpen ∧
        ⟨s.env.nextFVarId⟩ ∉ Delta.fvars ∧
        PreTrKExprS world.venv uvars world.nameOf trProj
          ((some (⟨s.env.nextFVarId⟩, Delta.fvars), .vlam typeV) :: Delta)
          bodyOpen bodyV ∧
        after.inferOnly = s.inferOnly
    | .error _ after =>
        WhnfStateInv layer semantics trProj world support uvars Delta after ∧
          after = s := by
  intro hI
  have hbase := TcM.openBinder_scope_base (bi := bi) htype htypeType
    hcollision hresources hI
  have hpolicy := TcM.PreservesInferOnly.openBinder name bi type body
  cases hopen : TcM.openBinder name bi type body s with
  | error err after =>
      rw [hopen] at hbase
      simpa only using hbase
  | ok opened after =>
      rcases opened with ⟨bodyOpen, fv⟩
      rw [hopen] at hbase
      simp only
      rcases hbase with ⟨hfv, hbodyEq, hIopen, hsupport⟩
      have hopenBound := hresources.instRevBounds ⟨s.env.nextFVarId⟩
      have hbodyOpen := hbody.openFVarZero
        (fv := ⟨s.env.nextFVarId⟩) (deps := Delta.fvars) (name := name)
        hI.2.1.nextFVarId_fresh (by simpa using hopenBound.2.2)
      have hpolicyAfter := hpolicy.ok hopen
      refine ⟨hfv, hbodyEq, hIopen, hsupport,
        hI.2.1.nextFVarId_fresh, ?_, hpolicyAfter⟩
      subst fv
      subst bodyOpen
      exact hbodyOpen

/-- Opening a let with typed type/value and a merely pre-translated body
returns the exact opened body under the tagged `vlet` context. -/
theorem openLet_pre_scope
    {support : RunSupport}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {name : Mode.anon.F Name}
    {type value body : KExpr .anon}
    {typeV valueV bodyV : Lean4Lean.VExpr}
    (htype : TrKExprS world.venv uvars world.nameOf trProj Delta type typeV)
    (hvalue : TrKExprS world.venv uvars world.nameOf trProj Delta value valueV)
    (hvalueType : world.venv.HasType uvars Delta.toCtx valueV typeV)
    (hbody : PreTrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlet typeV valueV) :: Delta) body bodyV)
    (hcollision : support.CollisionFree)
    (hresources : BinderOpeningResources support name body) :
    WhnfStateInv layer semantics trProj world support uvars Delta s →
    match TcM.openLet name type value body s with
    | .ok (bodyOpen, fvId) after =>
        fvId = ⟨s.env.nextFVarId⟩ ∧
        bodyOpen = KExpr.instantiateRevSpec body
          #[.mkFVar ⟨s.env.nextFVarId⟩ name] 0 ∧
        WhnfStateInv layer semantics trProj world support uvars
          ((some (⟨s.env.nextFVarId⟩, Delta.fvars),
            .vlet typeV valueV) :: Delta) after ∧
        support bodyOpen ∧
        ⟨s.env.nextFVarId⟩ ∉ Delta.fvars ∧
        PreTrKExprS world.venv uvars world.nameOf trProj
          ((some (⟨s.env.nextFVarId⟩, Delta.fvars),
            .vlet typeV valueV) :: Delta) bodyOpen bodyV ∧
        after.inferOnly = s.inferOnly
    | .error _ after =>
        WhnfStateInv layer semantics trProj world support uvars Delta after ∧
          after = s := by
  intro hI
  have hbase := TcM.openLet_scope_base htype hvalue hvalueType
    hcollision hresources hI
  have hpolicy := TcM.PreservesInferOnly.openLet name type value body
  cases hopen : TcM.openLet name type value body s with
  | error err after =>
      rw [hopen] at hbase
      simpa only using hbase
  | ok opened after =>
      rcases opened with ⟨bodyOpen, fv⟩
      rw [hopen] at hbase
      simp only
      rcases hbase with ⟨hfv, hbodyEq, hIopen, hsupport⟩
      have hopenBound := hresources.instRevBounds ⟨s.env.nextFVarId⟩
      have hbodyOpen := hbody.openFVarZero
        (fv := ⟨s.env.nextFVarId⟩) (deps := Delta.fvars) (name := name)
        hI.2.1.nextFVarId_fresh (by simpa using hopenBound.2.2)
      have hpolicyAfter := hpolicy.ok hopen
      refine ⟨hfv, hbodyEq, hIopen, hsupport,
        hI.2.1.nextFVarId_fresh, ?_, hpolicyAfter⟩
      subst fv
      subst bodyOpen
      exact hbodyOpen

end TcM

namespace RecM

/-- Scope a pre-translated binder around one fixed recursive method table.
Unlike the ordinary K2 scope rule, the body need not be typed before the
continuation runs: the continuation receives its exact opened
pre-translation and may establish typing by recursive full inference. -/
theorem withLctxScope_openBinder_pre_wf
    {beta : Type} {support : RunSupport}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {type body : KExpr .anon} {typeV bodyV : Lean4Lean.VExpr}
    (htype : TrKExprS world.venv uvars world.nameOf trProj Delta type typeV)
    (htypeType : world.venv.IsType uvars Delta.toCtx typeV)
    (hbody : PreTrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam typeV) :: Delta) body bodyV)
    (hcollision : support.CollisionFree)
    (hresources : BinderOpeningResources support name body)
    (hpolicy : s.inferOnly = false)
    {k : KExpr .anon → FVarId → RecM .anon beta}
    {Qinner Qouter : beta → TcState .anon → Prop}
    {Einner Eouter : TcError .anon → TcState .anon → Prop}
    (hk : ∀ {bodyOpen fv after},
      fv = ⟨s.env.nextFVarId⟩ →
      bodyOpen = KExpr.instantiateRevSpec body
        #[.mkFVar ⟨s.env.nextFVarId⟩ name] 0 →
      support bodyOpen →
      ⟨s.env.nextFVarId⟩ ∉ Delta.fvars →
      PreTrKExprS world.venv uvars world.nameOf trProj
        ((some (⟨s.env.nextFVarId⟩, Delta.fvars), .vlam typeV) :: Delta)
        bodyOpen bodyV →
      after.inferOnly = false →
      TcM.WF
        (WhnfStateInv layer semantics trProj world support uvars
          ((some (⟨s.env.nextFVarId⟩, Delta.fvars), .vlam typeV) :: Delta))
        after ((k bodyOpen fv).run methods) Qinner Einner)
    (hclose : ∀ result after, Qinner result after →
      Qouter result
        {after with lctx := after.lctx.truncate s.lctx.size})
    (hcloseError : ∀ err after, Einner err after →
      Eouter err {after with lctx := after.lctx.truncate s.lctx.size})
    (hopenError : ∀ err, Eouter err s) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((withLctxScope do
        let (bodyOpen, fv) ←
          (liftM (TcM.openBinder name bi type body) :
            RecM .anon (KExpr .anon × FVarId))
        k bodyOpen fv).run methods)
      Qouter Eouter := by
  intro hI
  rw [RecM.withLctxScope_eq]
  have hopenPost := TcM.openBinder_pre_scope (bi := bi) htype htypeType
    hbody hcollision hresources hI
  cases hopenRun : TcM.openBinder name bi type body s with
  | error err afterOpen =>
      rw [hopenRun] at hopenPost
      simp only at hopenPost
      rcases hopenPost with ⟨hIOpen, hafterOpen⟩
      have hscopedError :
          (do
            let (bodyOpen, fv) ←
              (liftM (TcM.openBinder name bi type body) :
                RecM .anon (KExpr .anon × FVarId))
            k bodyOpen fv).run methods s = .error err afterOpen := by
        change EStateM.bind (TcM.openBinder name bi type body)
          (fun opened => (k opened.1 opened.2).run methods) s = _
        unfold EStateM.bind
        rw [hopenRun]
      rw [hscopedError]
      subst afterOpen
      simp only [LocalContext.truncate_size]
      exact ⟨hIOpen, hopenError err⟩
  | ok opened afterOpen =>
      rcases opened with ⟨bodyOpen, fv⟩
      rw [hopenRun] at hopenPost
      simp only at hopenPost
      rcases hopenPost with
        ⟨hfv, hbodyEq, hIOpen, hbodySupport, hfresh, hbodyPre,
          hopenPolicy⟩
      have htail := hk hfv hbodyEq hbodySupport hfresh hbodyPre
        (hopenPolicy.trans hpolicy) hIOpen
      cases htailRun : (k bodyOpen fv).run methods afterOpen with
      | ok result after =>
          rw [htailRun] at htail
          simp only at htail
          have hscopedSuccess :
              (do
                let (bodyOpen, fv) ←
                  (liftM (TcM.openBinder name bi type body) :
                    RecM .anon (KExpr .anon × FVarId))
                k bodyOpen fv).run methods s = .ok result after := by
            change EStateM.bind (TcM.openBinder name bi type body)
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
                  (liftM (TcM.openBinder name bi type body) :
                    RecM .anon (KExpr .anon × FVarId))
                k bodyOpen fv).run methods s = .error tailErr after := by
            change EStateM.bind (TcM.openBinder name bi type body)
              (fun opened => (k opened.1 opened.2).run methods) s = _
            unfold EStateM.bind
            rw [hopenRun]
            exact htailRun
          rw [hscopedError]
          exact ⟨hI.closeFVarAtEntry htail.1,
            hcloseError _ _ htail.2⟩

/-- Fixed-method-table scope rule for a pre-translated let body. -/
theorem withLctxScope_openLet_pre_wf
    {beta : Type} {support : RunSupport}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {name : Mode.anon.F Name}
    {type value body : KExpr .anon}
    {typeV valueV bodyV : Lean4Lean.VExpr}
    (htype : TrKExprS world.venv uvars world.nameOf trProj Delta type typeV)
    (hvalue : TrKExprS world.venv uvars world.nameOf trProj Delta value valueV)
    (hvalueType : world.venv.HasType uvars Delta.toCtx valueV typeV)
    (hbody : PreTrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlet typeV valueV) :: Delta) body bodyV)
    (hcollision : support.CollisionFree)
    (hresources : BinderOpeningResources support name body)
    (hpolicy : s.inferOnly = false)
    {k : KExpr .anon → FVarId → RecM .anon beta}
    {Qinner Qouter : beta → TcState .anon → Prop}
    {Einner Eouter : TcError .anon → TcState .anon → Prop}
    (hk : ∀ {bodyOpen fv after},
      fv = ⟨s.env.nextFVarId⟩ →
      bodyOpen = KExpr.instantiateRevSpec body
        #[.mkFVar ⟨s.env.nextFVarId⟩ name] 0 →
      support bodyOpen →
      ⟨s.env.nextFVarId⟩ ∉ Delta.fvars →
      PreTrKExprS world.venv uvars world.nameOf trProj
        ((some (⟨s.env.nextFVarId⟩, Delta.fvars),
          .vlet typeV valueV) :: Delta) bodyOpen bodyV →
      after.inferOnly = false →
      TcM.WF
        (WhnfStateInv layer semantics trProj world support uvars
          ((some (⟨s.env.nextFVarId⟩, Delta.fvars),
            .vlet typeV valueV) :: Delta))
        after ((k bodyOpen fv).run methods) Qinner Einner)
    (hclose : ∀ result after, Qinner result after →
      Qouter result
        {after with lctx := after.lctx.truncate s.lctx.size})
    (hcloseError : ∀ err after, Einner err after →
      Eouter err {after with lctx := after.lctx.truncate s.lctx.size})
    (hopenError : ∀ err, Eouter err s) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((withLctxScope do
        let (bodyOpen, fv) ←
          (liftM (TcM.openLet name type value body) :
            RecM .anon (KExpr .anon × FVarId))
        k bodyOpen fv).run methods)
      Qouter Eouter := by
  intro hI
  rw [RecM.withLctxScope_eq]
  have hopenPost := TcM.openLet_pre_scope htype hvalue hvalueType hbody
    hcollision hresources hI
  cases hopenRun : TcM.openLet name type value body s with
  | error err afterOpen =>
      rw [hopenRun] at hopenPost
      simp only at hopenPost
      rcases hopenPost with ⟨hIOpen, hafterOpen⟩
      have hscopedError :
          (do
            let (bodyOpen, fv) ←
              (liftM (TcM.openLet name type value body) :
                RecM .anon (KExpr .anon × FVarId))
            k bodyOpen fv).run methods s = .error err afterOpen := by
        change EStateM.bind (TcM.openLet name type value body)
          (fun opened => (k opened.1 opened.2).run methods) s = _
        unfold EStateM.bind
        rw [hopenRun]
      rw [hscopedError]
      subst afterOpen
      simp only [LocalContext.truncate_size]
      exact ⟨hIOpen, hopenError err⟩
  | ok opened afterOpen =>
      rcases opened with ⟨bodyOpen, fv⟩
      rw [hopenRun] at hopenPost
      simp only at hopenPost
      rcases hopenPost with
        ⟨hfv, hbodyEq, hIOpen, hbodySupport, hfresh, hbodyPre,
          hopenPolicy⟩
      have htail := hk hfv hbodyEq hbodySupport hfresh hbodyPre
        (hopenPolicy.trans hpolicy) hIOpen
      cases htailRun : (k bodyOpen fv).run methods afterOpen with
      | ok result after =>
          rw [htailRun] at htail
          simp only at htail
          have hscopedSuccess :
              (do
                let (bodyOpen, fv) ←
                  (liftM (TcM.openLet name type value body) :
                    RecM .anon (KExpr .anon × FVarId))
                k bodyOpen fv).run methods s = .ok result after := by
            change EStateM.bind (TcM.openLet name type value body)
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
                  (liftM (TcM.openLet name type value body) :
                    RecM .anon (KExpr .anon × FVarId))
                k bodyOpen fv).run methods s = .error tailErr after := by
            change EStateM.bind (TcM.openLet name type value body)
              (fun opened => (k opened.1 opened.2).run methods) s = _
            unfold EStateM.bind
            rw [hopenRun]
            exact htailRun
          rw [hscopedError]
          exact ⟨hI.closeFVarAtEntry htail.1,
            hcloseError _ _ htail.2⟩

end RecM

end Ix.Tc
