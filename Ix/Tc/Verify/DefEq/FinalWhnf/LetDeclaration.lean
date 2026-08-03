import Ix.Tc.Verify.DefEq.FinalWhnf.Contracts
import Ix.Tc.Verify.Infer.LetScopes

/-!
# Final-WHNF let-declaration comparison

The final comparator normally sees lets only when earlier reduction leaves
them stuck.  Production still compares their types and values, opens both
bodies with one common fvar under the left let declaration, and compares the
opened bodies recursively.  This module verifies that exact scoped program,
including allocation failure and scope restoration on callback errors.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Finite constructor descent and body-opening coverage for supported lets.
The right body is opened with the left let's display name, so body resources
are exposed for every anonymous-mode name. -/
structure FinalWhnfLetResources (support : RunSupport) : Prop where
  components : ∀ {name ty val body nondep info},
    support (.letE name ty val body nondep info) →
      support ty ∧ support val ∧
        ∀ commonName, BinderOpeningResources support commonName body

namespace TcM

/-- Exact operational contract for `openLetWithFV`.  On success it returns
the common canonical fvar as well as the first opened body; allocation
exhaustion is the only error and leaves the entry state unchanged. -/
theorem openLetWithFV_scope
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
    match TcM.openLetWithFV name ty val body s with
    | .ok (bodyOpen, fv, fvId) after =>
        fvId = ⟨s.env.nextFVarId⟩ ∧
        fv = KExpr.mkFVar ⟨s.env.nextFVarId⟩ name ∧
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
      have hopenError : TcM.openLetWithFV name ty val body s =
          .error err s := by
        unfold TcM.openLetWithFV
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
      have hopenSuccess : TcM.openLetWithFV name ty val body s =
          .ok (KExpr.instantiateRevSpec body #[fv] 0, fv,
            ⟨s.env.nextFVarId⟩) afterOpen := by
        unfold TcM.openLetWithFV
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
      refine ⟨rfl, rfl, rfl, hIOpen, ?_, ?_⟩
      · simpa [fv] using hbodyOpenSupport
      · simpa [fv] using hbodyOpenTr

end TcM

namespace RecM

/-- Scope an exact `openLetWithFV` continuation and restore the entry local
context on success and failure. -/
theorem withLctxScope_openLetWithFV_wf
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
    {k : KExpr .anon → KExpr .anon → FVarId → RecM .anon beta}
    {Qinner Qouter : beta → TcState .anon → Prop}
    (hk : ∀ {bodyOpen fv fvId after},
      fvId = ⟨s.env.nextFVarId⟩ →
      fv = KExpr.mkFVar ⟨s.env.nextFVarId⟩ name →
      bodyOpen = KExpr.instantiateRevSpec body
        #[.mkFVar ⟨s.env.nextFVarId⟩ name] 0 →
      support bodyOpen →
      TrKExprS world.venv uvars world.nameOf trProj
        ((some (⟨s.env.nextFVarId⟩, Delta.fvars),
          .vlet tyV valV) :: Delta) bodyOpen bodyV →
      RecM.WF layer semantics trProj world support uvars
        ((some (⟨s.env.nextFVarId⟩, Delta.fvars),
          .vlet tyV valV) :: Delta) after (k bodyOpen fv fvId) Qinner)
    (hclose : ∀ result after, Qinner result after →
      Qouter result
        {after with lctx := after.lctx.truncate s.lctx.size}) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (withLctxScope do
        let (bodyOpen, fv, fvId) ←
          TcM.openLetWithFV name ty val body
        k bodyOpen fv fvId)
      Qouter := by
  intro methods hmethods hI
  rw [RecM.withLctxScope_eq]
  have hopenPost := TcM.openLetWithFV_scope hty hval hvalType hbody
    hcollision hresources hI
  cases hopenRun : TcM.openLetWithFV name ty val body s with
  | error err afterOpen =>
      rw [hopenRun] at hopenPost
      simp only at hopenPost
      rcases hopenPost with ⟨hIOpen, hafterOpen⟩
      have hscopedError :
          (do
            let (bodyOpen, fv, fvId) ←
              (liftM (TcM.openLetWithFV name ty val body) :
                RecM .anon (KExpr .anon × KExpr .anon × FVarId))
            k bodyOpen fv fvId).run methods s = .error err afterOpen := by
        change EStateM.bind (TcM.openLetWithFV name ty val body)
          (fun opened => (k opened.1 opened.2.1 opened.2.2).run methods) s = _
        unfold EStateM.bind
        rw [hopenRun]
      rw [hscopedError]
      subst afterOpen
      simp only [LocalContext.truncate_size]
      exact ⟨hIOpen, trivial⟩
  | ok opened afterOpen =>
      rcases opened with ⟨bodyOpen, fv, fvId⟩
      rw [hopenRun] at hopenPost
      simp only at hopenPost
      rcases hopenPost with
        ⟨hfvId, hfv, hbodyEq, hIOpen, hbodySupport, hbodyTr⟩
      have htail := hk hfvId hfv hbodyEq hbodySupport hbodyTr
        methods hmethods hIOpen
      cases htailRun : (k bodyOpen fv fvId).run methods afterOpen with
      | ok result after =>
          rw [htailRun] at htail
          simp only at htail
          have hscopedSuccess :
              (do
                let (bodyOpen, fv, fvId) ←
                  (liftM (TcM.openLetWithFV name ty val body) :
                    RecM .anon (KExpr .anon × KExpr .anon × FVarId))
                k bodyOpen fv fvId).run methods s = .ok result after := by
            change EStateM.bind (TcM.openLetWithFV name ty val body)
              (fun opened =>
                (k opened.1 opened.2.1 opened.2.2).run methods) s = _
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
                let (bodyOpen, fv, fvId) ←
                  (liftM (TcM.openLetWithFV name ty val body) :
                    RecM .anon (KExpr .anon × KExpr .anon × FVarId))
                k bodyOpen fv fvId).run methods s =
                  .error tailErr after := by
            change EStateM.bind (TcM.openLetWithFV name ty val body)
              (fun opened =>
                (k opened.1 opened.2.1 opened.2.2).run methods) s = _
            unfold EStateM.bind
            rw [hopenRun]
            exact htailRun
          rw [hscopedError]
          exact ⟨hI.closeFVarAtEntry htail.1, trivial⟩

/-- Exhaustive proof of the final-WHNF let helper. -/
theorem tryDefEqWhnfLet_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftName rightName : Mode.anon.F Name}
    {ty1 val1 body1 ty2 val2 body2 : KExpr .anon}
    {leftNondep rightNondep : Bool}
    {leftInfo rightInfo : ExprInfo .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (resources : FinalWhnfLetResources support)
    (hleftSupport :
      support (.letE leftName ty1 val1 body1 leftNondep leftInfo))
    (hrightSupport :
      support (.letE rightName ty2 val2 body2 rightNondep rightInfo))
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.letE leftName ty1 val1 body1 leftNondep leftInfo) leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.letE rightName ty2 val2 body2 rightNondep rightInfo) rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfLet leftName ty1 val1 body1 ty2 val2 body2)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  obtain ⟨hty1Support, hval1Support, hbody1Resources⟩ :=
    resources.components hleftSupport
  obtain ⟨hty2Support, hval2Support, hbody2Resources⟩ :=
    resources.components hrightSupport
  cases hleft with
  | letE hval1Type hty1 hval1 hbody1 =>
      cases hright with
      | letE hval2Type hty2 hval2 hbody2 =>
          unfold tryDefEqWhnfLet
          apply RecM.WF.bind <|
            RecM.isDefEqCall_wf hty1Support hty2Support hty1 hty2
          intro typesEqual afterTypes htypes
          cases typesEqual with
          | false =>
              simp only [Bool.false_eq_true, if_false]
              exact RecM.WF.pure fun _ => trivial
          | true =>
              simp only [if_true]
              apply RecM.WF.bind <|
                RecM.isDefEqCall_wf hval1Support hval2Support hval1 hval2
              intro valuesEqual afterValues hvalues
              cases valuesEqual with
              | false =>
                  simp only [Bool.false_eq_true, if_false]
                  exact RecM.WF.pure fun _ => trivial
              | true =>
                  simp only [if_true]
                  apply RecM.WF.bind <| by
                    apply withLctxScope_openLetWithFV_wf
                      (layer := layer) (semantics := semantics)
                      (trProj := trProj) (world := world) (uvars := uvars)
                      (Delta := Delta) (s := afterValues)
                      (k := fun body1Open fv _ => do
                        let body2Open ←
                          TcM.runIntern (instantiateRev body2 #[fv])
                        isDefEqCall body1Open body2Open)
                      (Qinner := fun answer _ => answer = true →
                        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)
                      (Qouter := fun answer _ => answer = true →
                        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)
                      hty1 hval1 hval1Type hbody1 hcollision
                      (hbody1Resources leftName)
                    · intro body1Open fv fvId afterOpen hfvId hfv
                        hbody1OpenEq hbody1OpenSupport hbody1OpenTr
                      subst fvId
                      subst fv
                      let fresh : FVarId :=
                        ⟨afterValues.env.nextFVarId⟩
                      let common : KExpr .anon := .mkFVar fresh leftName
                      have hrightBounds :=
                        (hbody2Resources leftName).instRevBounds fresh
                      apply RecM.WF.bind
                        (RecM.WF.withInv <| RecM.WF.liftTcM <|
                          TcM.instRev_whnf_wf_of_resources hcollision
                            hrightBounds
                            ((hbody2Resources leftName).instRevSupport
                              fresh))
                      intro body2Open afterBody2 hbody2Post
                      rcases hbody2Post with
                        ⟨hIBody2, hbody2OpenEq, _⟩
                      subst body2Open
                      have hDelta : KVLCtx.WF world.venv uvars Delta :=
                        hIBody2.2.1.wf.1
                      have hfresh : fresh ∉ Delta.fvars := by
                        exact (hIBody2.2.1.wf.2.1 fresh Delta.fvars rfl).1
                      obtain ⟨level, hty1Sort⟩ :=
                        hval1Type.isType world.venvWF hDelta.toCtx
                      have htypeTyped : world.venv.IsDefEq uvars
                          Delta.toCtx _ _ (.sort level) :=
                        (htypes rfl).of_l world.venvWF hDelta.toCtx
                          hty1Sort
                      have hvalueTyped : world.venv.IsDefEq uvars
                          Delta.toCtx _ _ _ :=
                        (hvalues rfl).of_l world.venvWF hDelta.toCtx
                          hval1Type
                      have hcontexts : KVLCtx.IsDefEq world.venv uvars
                          ((some (fresh, Delta.fvars),
                            .vlet _ _) :: Delta)
                          ((some (fresh, Delta.fvars),
                            .vlet _ _) :: Delta) :=
                        .cons
                          (KVLCtx.IsDefEq.refl world.venvWF.ordered hDelta)
                          (by
                            intro candidate deps heq
                            cases heq
                            exact ⟨hfresh, fun _ h => h⟩)
                          (.vlet hvalueTyped htypeTyped)
                      have hbody2Raw := hbody2.openFVarZero
                        (fv := fresh) (deps := Delta.fvars)
                        (name := leftName) hfresh
                        (by simpa using hrightBounds.2.2)
                      obtain ⟨body2V', hbody2Retag⟩ :=
                        hbody2Raw.defeqDFC world.venvWF theory.literalWF
                          theory.projections
                          (hcontexts.symm world.venvWF.ordered)
                      have hbody2Support : support
                          (KExpr.instantiateRevSpec body2 #[common] 0) :=
                        (hbody2Resources leftName).instRevSupport fresh _
                          (KExpr.InstRevReach.spec ..)
                      apply RecM.WF.mono
                        (RecM.isDefEqCall_wf hbody1OpenSupport
                          hbody2Support hbody1OpenTr
                          (by simpa [common] using hbody2Retag))
                      · intro answer final hanswer resultTrue
                        have hbody2Bridge : world.venv.IsDefEqU uvars
                            Delta.toCtx body2V' rightV := by
                          simpa [KVLCtx.toCtx] using
                            TrKExprS.uniq world.venvWF theory.literalWF
                              theory.projections hcontexts hbody2Retag
                              hbody2Raw
                        exact (hanswer resultTrue).trans world.venvWF
                          hcontexts.wf.toCtx hbody2Bridge
                      · intro _ _ _
                        trivial
                    · intro answer after hanswer
                      exact hanswer
                  intro bodiesEqual afterBodies hbodies
                  cases bodiesEqual with
                  | false =>
                      simp only [Bool.false_eq_true, if_false]
                      exact RecM.WF.pure fun _ => trivial
                  | true =>
                      simp only [if_true]
                      exact RecM.WF.pure fun _ => hbodies

namespace TryDefEqWhnfLet

/-- Package the scoped let proof for constructor-prefix assembly. -/
theorem ofResources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (resources : FinalWhnfLetResources support) :
    TryDefEqWhnfLet.WFAt layer semantics trProj world support uvars := by
  intro Delta state leftName rightName ty1 val1 body1 ty2 val2 body2
    leftNondep rightNondep leftInfo rightInfo leftV rightV hleftSupport
    hrightSupport hleft hright
  exact tryDefEqWhnfLet_wf theory hcollision resources hleftSupport
    hrightSupport hleft hright

end TryDefEqWhnfLet

end RecM

end Ix.Tc
