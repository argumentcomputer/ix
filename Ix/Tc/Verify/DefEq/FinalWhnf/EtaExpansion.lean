import Ix.Tc.Verify.DefEq.FinalWhnf.Contracts
import Ix.Tc.Verify.DefEq.ProofIrrelevance

/-!
# Final-WHNF lambda eta

This module verifies the concrete eta expansion built by
`tryEtaExpansion`: inference exposes the non-lambda operand's function type,
the operand is lifted under one binder, and the generated
`λ x, liftedOperand x` is compared recursively.  The finite resources below
cover the exact lift footprint and generated syntax; no semantic eta callback
is assumed.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Finite walker and generated-node closure for lambda eta. -/
structure FinalWhnfEtaResources (support : RunSupport) : Prop where
  liftBounds : ∀ {source : KExpr .anon}, support source →
    WalkerRequest.Bounds (.lift source 1 0)
  liftReach : ∀ {source : KExpr .anon}, support source → ∀ x,
    KExpr.LiftReach 1 source 0 x → support x
  forallDomain : ∀ {name : Mode.anon.F Name}
      {bi : Mode.anon.F Lean.BinderInfo} {ty body : KExpr .anon}
      {info : ExprInfo .anon},
    support (.all name bi ty body info) → support ty
  variableNode : support (KExpr.mkVar 0 RecM.anonN : KExpr .anon)
  application : ∀ {source : KExpr .anon}, support source →
    support (KExpr.mkApp (KExpr.liftSpec source 1 0)
      (KExpr.mkVar 0 RecM.anonN : KExpr .anon))
  lambda : ∀ {source ty : KExpr .anon} {name : Mode.anon.F Name}
      {bi : Mode.anon.F Lean.BinderInfo},
    support source → support ty →
    support (KExpr.mkLam name bi ty
      (KExpr.mkApp (KExpr.liftSpec source 1 0)
        (KExpr.mkVar 0 RecM.anonN : KExpr .anon)))

namespace TcM

/-- Request-independent Hoare rule for the lifting walker used by eta. -/
theorem lift_whnf_wf_of_resources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {source : KExpr .anon}
    {shift cutoff : UInt64} {state : TcState .anon}
    (hcollision : support.CollisionFree)
    (hbounds : WalkerRequest.Bounds (.lift source shift cutoff))
    (hreach : ∀ x, KExpr.LiftReach shift source cutoff x → support x) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta)
      state (TcM.runIntern (lift source shift cutoff))
      (fun result after =>
        result = KExpr.liftSpec source shift cutoff ∧
          InternUpdateFrame state after) :=
  TcM.runIntern_whnf_wf
    (fun intern hwf hsupport => by
      have post := Ix.Tc.lift_spec hcollision.expr hbounds.1 hbounds.2.1
        hreach hwf hsupport.expr
      exact ⟨post.1, post.2.1,
        hsupport.of_expr_univs post.2.2
          (lift_preservesUnivs source shift cutoff intern)⟩)

end TcM

namespace RecM

/-- The generated eta lambda translates exactly to Theory's eta redex. -/
theorem compareEtaExpansion_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {target source domain : KExpr .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {targetV sourceV domainV codomainV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (resources : FinalWhnfEtaResources support)
    (hcollision : support.CollisionFree)
    (htargetSupport : support target) (hsourceSupport : support source)
    (htarget : TrKExprS world.venv uvars world.nameOf trProj Delta target
      targetV)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hdomainSupport : support domain)
    (hdomainType : world.venv.IsType uvars Delta.toCtx domainV)
    (hdomain : TrKExprS world.venv uvars world.nameOf trProj Delta domain
      domainV)
    (hsourceType : world.venv.HasType uvars Delta.toCtx sourceV
      (.forallE domainV codomainV)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (compareEtaExpansion target source name bi domain)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx targetV sourceV) := by
  unfold compareEtaExpansion
  have hliftBounds := resources.liftBounds hsourceSupport
  have hliftReach := resources.liftReach hsourceSupport
  apply RecM.WF.bind <| RecM.WF.withInv <| RecM.WF.liftTcM <|
    TcM.lift_whnf_wf_of_resources hcollision hliftBounds hliftReach
  intro lifted afterLift hliftPost
  rcases hliftPost with ⟨hILift, rfl, _⟩
  have hliftedSupport : support (KExpr.liftSpec source 1 0) :=
    hliftReach _ (KExpr.LiftReach.spec 1 source 0)
  have hcontextLift : KVLCtx.KBVLift Delta
      ((none, .vlam domainV) :: Delta) 1 0 1 0 :=
    .skip (.vlam domainV) .refl
  have hlifted : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam domainV) :: Delta) (KExpr.liftSpec source 1 0)
      sourceV.lift := by
    exact TrKExprS.weakBV_lbr world.venvWF.ordered
      theory.projections.weakN hliftBounds.1 hsource hcontextLift rfl rfl
      hliftBounds.2.1 hliftBounds.2.2
  apply RecM.WF.bind <| RecM.WF.withInv <| RecM.WF.liftTcM <|
    TcM.intern_whnf_wf hcollision resources.variableNode
  intro variableNode afterVariable hvariablePost
  rcases hvariablePost with ⟨hIVariable, rfl, _⟩
  have hvariable : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam domainV) :: Delta)
      (KExpr.mkVar 0 anonN : KExpr .anon) (.bvar 0) := by
    rw [KExpr.mkVar_shape]
    exact .var rfl
  have hbodySupport := resources.application hsourceSupport
  apply RecM.WF.bind <| RecM.WF.withInv <| RecM.WF.liftTcM <|
    TcM.intern_whnf_wf hcollision hbodySupport
  intro body afterBody hbodyPost
  rcases hbodyPost with ⟨hIBody, rfl, _⟩
  have hbody : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam domainV) :: Delta)
      (KExpr.mkApp (KExpr.liftSpec source 1 0)
        (KExpr.mkVar 0 anonN : KExpr .anon))
      (.app sourceV.lift (.bvar 0)) := by
    rw [KExpr.mkApp_shape]
    exact .app (hsourceType.weak world.venvWF.ordered)
      (.bvar .zero) hlifted hvariable
  have hlambdaSupport := resources.lambda (name := name) (bi := bi)
    hsourceSupport hdomainSupport
  apply RecM.WF.bind <| RecM.WF.withInv <| RecM.WF.liftTcM <|
    TcM.intern_whnf_wf hcollision hlambdaSupport
  intro lambdaNode afterLambda hlambdaPost
  rcases hlambdaPost with ⟨hILambda, rfl, _⟩
  have hlambda : TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.mkLam name bi domain
        (KExpr.mkApp (KExpr.liftSpec source 1 0)
          (KExpr.mkVar 0 anonN : KExpr .anon)))
      (.lam domainV (.app sourceV.lift (.bvar 0))) := by
    rw [KExpr.mkLam_shape]
    exact .lam hdomainType hdomain hbody
  apply RecM.WF.mono
    (RecM.isDefEqCall_wf htargetSupport hlambdaSupport htarget hlambda)
  · intro answer final hanswer htrue
    exact (hanswer htrue).trans world.venvWF hILambda.2.1.wf
      ⟨_, .eta hsourceType⟩
  · intro _ _ _
    trivial

/-- Inference and WHNF expose the function type consumed by the concrete eta
builder.  Caught callback errors and non-function results are conservative
negative answers. -/
theorem tryEtaExpansionAfterGuard_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {target source : KExpr .anon} {targetV sourceV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (resources : FinalWhnfEtaResources support)
    (hcollision : support.CollisionFree)
    (hwhnf : DefEqDirectWhnf.WFAt layer semantics trProj world support
      uvars)
    (htargetSupport : support target) (hsourceSupport : support source)
    (htarget : TrKExprS world.venv uvars world.nameOf trProj Delta target
      targetV)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryEtaExpansionAfterGuard target source)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx targetV sourceV) := by
  unfold tryEtaExpansionAfterGuard
  apply RecM.WF.bind
    (tryOptionalInferOnlyCall_wf hsourceSupport hsource)
  intro inferred afterInfer hinferred
  cases inferred with
  | none =>
      simp only
      exact RecM.WF.pure fun _ htrue => by contradiction
  | some inferred =>
      rcases hinferred with
        ⟨hinferredSupport, inferredV, hinferredTr, hsourceInferred⟩
      obtain ⟨inferredCoreV, hinferredCoreTr, hinferredCoreEq⟩ :=
        hinferredTr
      simp only
      apply RecM.WF.bind <| tryOptional_wf <| RecM.WF.withInv <|
        hwhnf hinferredSupport hinferredCoreTr
      intro reduced afterWhnf hreduced
      cases reduced with
      | none =>
          simp only
          exact RecM.WF.pure fun _ htrue => by contradiction
      | some reduced =>
          rcases hreduced with
            ⟨hIWhnf, hreducedSupport, reducedV, hreducedTr,
              hinferredCoreReduced⟩
          cases reduced with
          | var idx name info =>
              simp only
              exact RecM.WF.pure fun _ htrue => by contradiction
          | fvar id name info =>
              simp only
              exact RecM.WF.pure fun _ htrue => by contradiction
          | sort level info =>
              simp only
              exact RecM.WF.pure fun _ htrue => by contradiction
          | const id levels info =>
              simp only
              exact RecM.WF.pure fun _ htrue => by contradiction
          | app fn arg info =>
              simp only
              exact RecM.WF.pure fun _ htrue => by contradiction
          | lam name bi domain body info =>
              simp only
              exact RecM.WF.pure fun _ htrue => by contradiction
          | all name bi domain body info =>
              cases hreducedTr with
              | all hdomainType hcodomainType hdomainTr hcodomainTr =>
                  simp only
                  have hDelta : KVLCtx.WF world.venv uvars Delta :=
                    hIWhnf.2.1.wf
                  have hsourceCore : world.venv.HasType uvars Delta.toCtx
                      sourceV inferredCoreV :=
                    hsourceInferred.defeqU_r world.venvWF hDelta
                      hinferredCoreEq.symm
                  have hsourceFunction : world.venv.HasType uvars
                      Delta.toCtx sourceV (.forallE _ _) :=
                    hsourceCore.defeqU_r world.venvWF hDelta
                      hinferredCoreReduced
                  exact compareEtaExpansion_wf theory resources hcollision
                    htargetSupport hsourceSupport htarget hsource
                    (resources.forallDomain hreducedSupport) hdomainType
                    hdomainTr hsourceFunction
          | letE name ty val body nondep info =>
              simp only
              exact RecM.WF.pure fun _ htrue => by contradiction
          | prj id field value info =>
              simp only
              exact RecM.WF.pure fun _ htrue => by contradiction
          | nat value blob info =>
              simp only
              exact RecM.WF.pure fun _ htrue => by contradiction
          | str value blob info =>
              simp only
              exact RecM.WF.pure fun _ htrue => by contradiction

/-- Exhaust the syntactic lambda/non-lambda guard around the verified eta
construction. -/
theorem tryEtaExpansion_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {target source : KExpr .anon} {targetV sourceV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (resources : FinalWhnfEtaResources support)
    (hcollision : support.CollisionFree)
    (hwhnf : DefEqDirectWhnf.WFAt layer semantics trProj world support
      uvars)
    (htargetSupport : support target) (hsourceSupport : support source)
    (htarget : TrKExprS world.venv uvars world.nameOf trProj Delta target
      targetV)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryEtaExpansion target source)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx targetV sourceV) := by
  cases target <;> cases source <;>
    simp only [tryEtaExpansion, Bool.not_false, Bool.not_true,
      Bool.false_or, Bool.true_or, if_true]
  all_goals first
    | exact tryEtaExpansionAfterGuard_wf theory resources hcollision hwhnf
        htargetSupport hsourceSupport htarget hsource
    | exact RecM.WF.pure fun _ htrue => by contradiction

/-- The ordered, bidirectional eta attempts are sound; a successful reverse
attempt is flipped with Theory symmetry. -/
theorem tryDefEqWhnfEtaAfterGuard_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (resources : FinalWhnfEtaResources support)
    (hcollision : support.CollisionFree)
    (hwhnf : DefEqDirectWhnf.WFAt layer semantics trProj world support
      uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfEtaAfterGuard left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold tryDefEqWhnfEtaAfterGuard
  apply RecM.WF.bind <|
    tryEtaExpansion_wf theory resources hcollision hwhnf hleftSupport
      hrightSupport hleft hright
  intro accepted afterFirst hfirst
  cases accepted with
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun _ _ => hfirst rfl
  | false =>
      simp only [Bool.false_eq_true, if_false]
      apply RecM.WF.bind <|
        tryEtaExpansion_wf theory resources hcollision hwhnf
          hrightSupport hleftSupport hright hleft
      intro reverseAccepted afterSecond hsecond
      cases reverseAccepted with
      | true =>
          simp only [if_true]
          exact RecM.WF.pure fun _ _ => (hsecond rfl).symm
      | false =>
          simp only [Bool.false_eq_true, if_false]
          exact RecM.WF.pure fun _ => trivial

/-- Exhaust the outer "either operand is a lambda" phase guard. -/
theorem tryDefEqWhnfEta_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (resources : FinalWhnfEtaResources support)
    (hcollision : support.CollisionFree)
    (hwhnf : DefEqDirectWhnf.WFAt layer semantics trProj world support
      uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfEta left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  cases left <;> cases right <;>
    simp only [tryDefEqWhnfEta, Bool.false_or, Bool.true_or, if_true]
  all_goals
    exact tryDefEqWhnfEtaAfterGuard_wf theory resources hcollision hwhnf
      hleftSupport hrightSupport hleft hright

namespace TryDefEqWhnfEta

/-- Package the concrete eta phase. -/
theorem ofResources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (resources : FinalWhnfEtaResources support)
    (hcollision : support.CollisionFree)
    (hwhnf : DefEqDirectWhnf.WFAt layer semantics trProj world support
      uvars) :
    TryDefEqWhnfEta.WFAt layer semantics trProj world support uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact tryDefEqWhnfEta_wf theory resources hcollision hwhnf hleftSupport
    hrightSupport hleft hright

end TryDefEqWhnfEta

/-- Compose the eta phase with the exact remainder of the final-WHNF
fallback chain. -/
theorem isDefEqWhnfAfterNat_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (heta : TryDefEqWhnfEta.WFAt layer semantics trProj world support uvars)
    (htail : IsDefEqWhnfAfterEta.WFAt layer semantics trProj world support
      uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqWhnfAfterNat left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold isDefEqWhnfAfterNat
  apply RecM.WF.bind <|
    heta hleftSupport hrightSupport hleft hright
  intro result afterEta hresult
  cases result with
  | none => exact htail hleftSupport hrightSupport hleft hright
  | some answer => exact RecM.WF.pure fun _ => hresult

namespace IsDefEqWhnfAfterNat

/-- Package eta with the remaining post-eta contract. -/
theorem ofEta
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (resources : FinalWhnfEtaResources support)
    (hcollision : support.CollisionFree)
    (hwhnf : DefEqDirectWhnf.WFAt layer semantics trProj world support
      uvars)
    (htail : IsDefEqWhnfAfterEta.WFAt layer semantics trProj world support
      uvars) :
    IsDefEqWhnfAfterNat.WFAt layer semantics trProj world support uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact isDefEqWhnfAfterNat_wf
    (TryDefEqWhnfEta.ofResources theory resources hcollision hwhnf) htail
    hleftSupport hrightSupport hleft hright

end IsDefEqWhnfAfterNat

end RecM

end Ix.Tc
