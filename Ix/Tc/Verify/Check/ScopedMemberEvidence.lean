import Ix.Tc.Verify.Check.MemberEvidence
import Ix.Tc.Verify.Check.ScopedBoundedPipelines
import Ix.Tc.Verify.Check.SafetyFrame

/-!
# Run-scoped evidence from standalone member checking

The production trace decomposition mirrors `MemberEvidence`, but every
validator, inference, DefEq, and safety-traversal state retains the finite
suffix-model domain.  The semantic promotion is ghost-only, so the final
state carries the original model's `StateInScope` witness alongside the
rebased checker invariant.
-/

namespace Ix.Tc

namespace RecM

private theorem scopedRunTcBind {a b : Type}
    (x : TcM .anon a) (k : a → TcM .anon b)
    (state : TcState .anon) :
    (x >>= k) state = match x state with
      | .ok value after => k value after
      | .error err after => .error err after := by
  show EStateM.bind x k state = _
  unfold EStateM.bind
  cases x state <;> rfl

private theorem scopedRunInferEnsureSort
    (source : KExpr .anon) (methods : Methods .anon)
    {before afterInfer after : TcState .anon}
    {inferred : KExpr .anon} {sort : KUniv .anon}
    (hinfer : (infer source).run methods before = .ok inferred afterInfer)
    (hsort : (ensureSortDirect inferred).run methods afterInfer =
      .ok sort after) :
    ((do
      let inferred ← infer source
      let _ ← ensureSortDirect inferred).run methods) before =
        .ok () after := by
  simp only [ReaderT.run_bind]
  change EStateM.bind ((infer source).run methods) _ before = _
  unfold EStateM.bind
  rw [hinfer]
  change EStateM.map _ ((ensureSortDirect inferred).run methods) afterInfer = _
  unfold EStateM.map
  rw [hsort]

private theorem scopedRunInferDefEqTrue
    (value declaredType : KExpr .anon) (methods : Methods .anon)
    {before afterInfer after : TcState .anon}
    {inferredType : KExpr .anon}
    (hinfer : (infer value).run methods before = .ok inferredType afterInfer)
    (hdefeq : (isDefEq inferredType declaredType).run methods afterInfer =
      .ok true after) :
    ((do
      let inferredType ← infer value
      if !(← isDefEq inferredType declaredType) then
        throw TcError.declTypeMismatch).run methods) before = .ok () after := by
  simp only [ReaderT.run_bind]
  change EStateM.bind ((infer value).run methods) _ before = _
  unfold EStateM.bind
  rw [hinfer]
  change EStateM.bind ((isDefEq inferredType declaredType).run methods) _
    afterInfer = _
  unfold EStateM.bind
  rw [hdefeq]
  rfl

theorem checkConstMember_axiom_scoped_sound
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {support : RunSupport} {calls : Methods.CallDomain}
    {methods : Methods .anon}
    (context : ScopedStandalonePipelineResources model support calls methods)
    (hmethods : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) support calls
      (Methods.next methods))
    (hmethodPolicy : (Methods.next methods).PreservesInferOnly)
    {id : KId .anon} {name : Mode.anon.F Name}
    {levelParams : Mode.anon.F (Array Name)} {isUnsafe : Bool}
    {levels : UInt64} {type : KExpr .anon}
    {typeV : Lean4Lean.VExpr}
    (hresources : StandaloneValidationResources support
      (.axio name levelParams isUnsafe levels type))
    (hsourceCall : context.typeSources type)
    (hsource : PreTrKExprS world.venv levels.toNat world.nameOf trProj
      [] type typeV)
    (huvars : model.keys.uvars = levels.toNat)
    {state after : TcState .anon}
    (hpolicy : state.inferOnly = false)
    (hI : ScopedWhnfStateInv model .noAccel
      (kernelCacheSemantics model.keys trProj) support [] state)
    (hfault : TcM.LazyFaultPreserves
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support []))
    (hrun :
      (checkConstMember id (.axio name levelParams isUnsafe levels type)).run
        methods state = .ok () after) :
    ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support [] after ∧
      after.inferOnly = false ∧
      TrKExprS world.venv levels.toNat world.nameOf trProj [] type typeV ∧
      TypeCheckEvidence trProj world support levels.toNat [] typeV := by
  have hframe := validateConstWellScoped_frame hresources methods
    (hfault.withInferOnly false) state ⟨hI, hpolicy⟩
  unfold checkConstMember at hrun
  simp only [Mode.F.hasDups, Bool.false_eq_true, if_false,
    ReaderT.run_bind, pure_bind] at hrun
  cases hvalidation :
      (validateConstWellScoped
        (.axio name levelParams isUnsafe levels type)).run methods state with
  | error err failed =>
      rw [scopedRunTcBind, hvalidation] at hrun
      contradiction
  | ok validationValue afterValidation =>
      rw [scopedRunTcBind, hvalidation] at hrun
      have hIValidation : ScopedWhnfStateInv model .noAccel
          (kernelCacheSemantics model.keys trProj) support []
          afterValidation := by
        rw [hvalidation] at hframe
        exact hframe.1.1
      have hpolicyValidation : afterValidation.inferOnly = false := by
        rw [hvalidation] at hframe
        exact hframe.1.2
      have hsource' : PreTrKExprS world.venv model.keys.uvars world.nameOf
          trProj [] type typeV := by
        simpa [huvars] using hsource
      have hpipeline := checkTypePipeline_scoped_sound context hmethods
        hmethodPolicy hsourceCall hsource' hpolicyValidation hIValidation hrun
      simpa [huvars] using hpipeline

theorem checkConstMember_defn_scoped_sound
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {support : RunSupport} {calls : Methods.CallDomain}
    {methods : Methods .anon}
    (context : ScopedStandalonePipelineResources model support calls methods)
    (hmethods : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) support calls
      (Methods.next methods))
    (hmethodPolicy : (Methods.next methods).PreservesInferOnly)
    {id : KId .anon} {name : Mode.anon.F Name}
    {levelParams : Mode.anon.F (Array Name)} {kind : Ix.DefKind}
    {safety : Ix.DefinitionSafety} {hints : Lean.ReducibilityHints}
    {levels : UInt64} {type value : KExpr .anon}
    {leanAll : Mode.anon.F (Array (KId .anon))} {block : KId .anon}
    {typeV valueV : Lean4Lean.VExpr}
    (hresources : StandaloneValidationResources support
      (.defn name levelParams kind safety hints levels type value leanAll
        block))
    (htypeCall : context.typeSources type)
    (hvalueCall : context.valueSources value type)
    (htype : PreTrKExprS world.venv levels.toNat world.nameOf trProj
      [] type typeV)
    (hvalue : PreTrKExprS world.venv levels.toNat world.nameOf trProj
      [] value valueV)
    (huvars : model.keys.uvars = levels.toNat)
    {state after : TcState .anon}
    (hpolicy : state.inferOnly = false)
    (hI : ScopedWhnfStateInv model .noAccel
      (kernelCacheSemantics model.keys trProj) support [] state)
    (hfault : TcM.LazyFaultPreserves
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support []))
    (hrun :
      (checkConstMember id
        (.defn name levelParams kind safety hints levels type value leanAll
          block)).run methods state = .ok () after) :
    ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support [] after ∧
      TypeCheckEvidence trProj world support levels.toNat [] typeV ∧
      ValueCheckEvidence world levels.toNat [] valueV typeV := by
  have hframe := validateConstWellScoped_frame hresources methods
    (hfault.withInferOnly false) state ⟨hI, hpolicy⟩
  unfold checkConstMember at hrun
  simp only [Mode.F.hasDups, Bool.false_eq_true, if_false,
    ReaderT.run_bind, pure_bind] at hrun
  cases hvalidation :
      (validateConstWellScoped
        (.defn name levelParams kind safety hints levels type value leanAll
          block)).run methods state with
  | error err failed =>
      simp only [scopedRunTcBind, hvalidation] at hrun
      contradiction
  | ok validationValue afterValidation =>
      simp only [scopedRunTcBind, hvalidation] at hrun
      have hIValidation : ScopedWhnfStateInv model .noAccel
          (kernelCacheSemantics model.keys trProj) support []
          afterValidation := by
        rw [hvalidation] at hframe
        exact hframe.1.1
      have hpolicyValidation : afterValidation.inferOnly = false := by
        rw [hvalidation] at hframe
        exact hframe.1.2
      have htype' : PreTrKExprS world.venv model.keys.uvars world.nameOf
          trProj [] type typeV := by
        simpa [huvars] using htype
      have hvalue' : PreTrKExprS world.venv model.keys.uvars world.nameOf
          trProj [] value valueV := by
        simpa [huvars] using hvalue
      cases hinferType : (infer type).run methods afterValidation with
      | error err failed =>
          simp only [hinferType] at hrun
          contradiction
      | ok inferred afterInferType =>
          simp only [hinferType] at hrun
          cases hsort : (ensureSortDirect inferred).run methods afterInferType with
          | error err failed =>
              simp only [hsort] at hrun
              contradiction
          | ok level afterType =>
              simp only [hsort] at hrun
              have htypePipeline :
                  ((do
                    let inferred ← infer type
                    let _ ← ensureSortDirect inferred).run methods)
                      afterValidation = .ok () afterType :=
                scopedRunInferEnsureSort type methods hinferType hsort
              have htypePost := checkTypePipeline_scoped_sound context
                hmethods hmethodPolicy htypeCall htype' hpolicyValidation
                hIValidation htypePipeline
              have hIType := htypePost.1
              have hpolicyType := htypePost.2.1
              have htypeTr := htypePost.2.2.1
              have htypeEvidence := htypePost.2.2.2
              by_cases htheorem : kind == .thm && !univEq level .mkZero
              · simp only [htheorem, if_true] at hrun
                contradiction
              · simp only [htheorem, Bool.false_eq_true, if_false,
                  ReaderT.run_bind] at hrun
                cases hinferValue : (infer value).run methods afterType with
                | error err failed =>
                    simp only [scopedRunTcBind, hinferValue] at hrun
                    contradiction
                | ok inferredType afterInferValue =>
                    simp only [scopedRunTcBind, hinferValue] at hrun
                    cases hanswer :
                        (isDefEq inferredType type).run methods afterInferValue with
                    | error err failed =>
                        simp only [hanswer] at hrun
                        contradiction
                    | ok answer afterDefEq =>
                        simp only [hanswer] at hrun
                        cases answer with
                        | false =>
                            simp only [Bool.not_false, if_true] at hrun
                            contradiction
                        | true =>
                            have hvaluePipeline :
                                ((do
                                  let inferredType ← infer value
                                  if !(← isDefEq inferredType type) then
                                    throw TcError.declTypeMismatch).run methods)
                                    afterType = .ok () afterDefEq :=
                              scopedRunInferDefEqTrue value type methods
                                hinferValue hanswer
                            have hvaluePost :=
                              checkValuePipeline_scoped_sound context hmethods
                                hvalueCall hvalue' htypeTr hpolicyType hIType
                                hvaluePipeline
                            have hIDefEq := hvaluePost.1
                            have hvalueEvidence := hvaluePost.2
                            by_cases hsafety : safety != .unsaf
                            · simp only [Bool.not_true, Bool.false_eq_true,
                                if_false] at hrun
                              simp only [hsafety, if_true,
                                ReaderT.run_bind] at hrun
                              cases htypeSafety :
                                  (checkNoUnsafeRefs type safety).run methods
                                    afterDefEq with
                              | error err failed =>
                                  rw [scopedRunTcBind, htypeSafety] at hrun
                                  contradiction
                              | ok typeSafetyValue afterTypeSafety =>
                                  rw [scopedRunTcBind, htypeSafety] at hrun
                                  have htypePost :=
                                    checkNoUnsafeRefs_frame type safety methods
                                      (ScopedWhnfStateInv model .noAccel
                                        (kernelCacheSemantics model.keys
                                          trProj) support [])
                                      hfault afterDefEq hIDefEq
                                  rw [htypeSafety] at htypePost
                                  cases hvalueSafety :
                                      (checkNoUnsafeRefs value safety).run
                                        methods afterTypeSafety with
                                  | error err failed =>
                                      simp only [hvalueSafety] at hrun
                                      contradiction
                                  | ok valueSafetyValue afterValueSafety =>
                                      simp only [hvalueSafety] at hrun
                                      cases hrun
                                      have hvalueSafetyPost :=
                                        checkNoUnsafeRefs_frame value safety
                                          methods
                                          (ScopedWhnfStateInv model .noAccel
                                            (kernelCacheSemantics model.keys
                                              trProj) support [])
                                          hfault afterTypeSafety htypePost.1
                                      rw [hvalueSafety] at hvalueSafetyPost
                                      exact ⟨hvalueSafetyPost.1,
                                        by simpa [huvars] using htypeEvidence,
                                        by simpa [huvars] using hvalueEvidence⟩
                            · simp only [Bool.not_true, Bool.false_eq_true,
                                if_false] at hrun
                              simp only [hsafety] at hrun
                              cases hrun
                              exact ⟨hIDefEq,
                                by simpa [huvars] using htypeEvidence,
                                by simpa [huvars] using hvalueEvidence⟩

theorem checkConstMember_scoped_sound
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {support : RunSupport} {calls : Methods.CallDomain}
    {methods : Methods .anon}
    (context : ScopedStandalonePipelineResources model support calls methods)
    (hmethods : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) support calls
      (Methods.next methods))
    (hmethodPolicy : (Methods.next methods).PreservesInferOnly)
    {id : KId .anon} {concrete : KConst .anon}
    {decl : Lean4Lean.VDecl}
    (hingress : PreDeclRel world.venv world.nameOf trProj id concrete decl)
    (hcovers : context.Covers concrete)
    (hresources : StandaloneValidationResources support concrete)
    (huvars : model.keys.uvars = concrete.lvls.toNat)
    {state after : TcState .anon}
    (hpolicy : state.inferOnly = false)
    (hI : ScopedWhnfStateInv model .noAccel
      (kernelCacheSemantics model.keys trProj) support [] state)
    (hfault : TcM.LazyFaultPreserves
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support []))
    (hrun : (checkConstMember id concrete).run methods state =
      .ok () after) :
    ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support [] after ∧
      StandaloneCheckEvidence trProj world support decl := by
  cases hingress with
  | @«axiom» name levelParams isUnsafe levels type theoryName typeV _ htype =>
      cases hresources with
      | «axiom» hcoverage hsize =>
          cases hcovers with
          | «axiom» htypeCall =>
              have hresult := checkConstMember_axiom_scoped_sound context
                hmethods hmethodPolicy (.axiom hcoverage hsize) htypeCall
                htype huvars hpolicy hI hfault hrun
              exact ⟨hresult.1, .axiom hresult.2.2.2⟩
  | @defn name levelParams kind safety hints levels type value leanAll block
      theoryName typeV valueV decl _ htype hvalue hkind =>
      cases hresources with
      | defn htypeCoverage htypeSize hvalueCoverage hvalueSize =>
          cases hcovers with
          | defn htypeCall hvalueCall =>
              have hevidence := checkConstMember_defn_scoped_sound context
                hmethods hmethodPolicy
                (.defn htypeCoverage htypeSize hvalueCoverage hvalueSize)
                htypeCall hvalueCall htype hvalue huvars hpolicy hI hfault hrun
              cases hkind with
              | defn =>
                  exact ⟨hevidence.1, .defn hevidence.2.1 hevidence.2.2⟩
              | opaq =>
                  exact ⟨hevidence.1, .opaque hevidence.2.1 hevidence.2.2⟩
              | thm =>
                  exact ⟨hevidence.1, .opaque hevidence.2.1 hevidence.2.2⟩

/-- End-to-end scoped member theorem, including ghost-only promotion. -/
theorem checkConstMember_scoped_pending_sound
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {support : RunSupport} {calls : Methods.CallDomain}
    {methods : Methods .anon}
    (context : ScopedStandalonePipelineResources model support calls methods)
    (hmethods : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) support calls
      (Methods.next methods))
    (hmethodPolicy : (Methods.next methods).PreservesInferOnly)
    {id : KId .anon} {concrete : KConst .anon}
    {decl : Lean4Lean.VDecl}
    (hprojection : trProj.SubstCompatible)
    (hliterals : ∀ literal, world.venv.ContainsLits literal)
    (hpending : PendingDecl trProj world id decl)
    (hcatalog : world.catalog id = some concrete)
    (hresources : StandaloneValidationResources support concrete)
    (hcovers : context.Covers concrete)
    (hcollision : support.CollisionFree)
    (huvars : model.keys.uvars = concrete.lvls.toNat)
    {state after : TcState .anon}
    (hpolicy : state.inferOnly = false)
    (hI : ScopedWhnfStateInv model .noAccel
      (kernelCacheSemantics model.keys trProj) support [] state)
    (hfault : TcM.LazyFaultPreserves
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support []))
    (hrun : (checkConstMember id concrete).run methods state =
      .ok () after) :
    StandaloneCheckResult trProj world support id concrete decl ∧
      ∃ world',
        Promotes world (fun target => target = id) world' ∧
        WhnfStateInv .noAccel
          (kernelCacheSemantics model.keys trProj) trProj world' support
          model.keys.uvars [] after ∧
        model.StateInScope after ∧
        TrustedDecl trProj world' id decl := by
  obtain ⟨afterValidation, hvalidation⟩ :=
    checkConstMember_validation_success hresources hrun
  have hingress := hpending.toPre_of_validation hprojection hliterals hcatalog
    hresources hcollision hvalidation
  have hevidence := checkConstMember_scoped_sound context hmethods
    hmethodPolicy hingress hcovers hresources huvars hpolicy hI hfault hrun
  obtain ⟨world', hpromotes, hcore, htrusted⟩ :=
    PendingDecl.promoteOfAccepted hevidence.1.1.1.core hpending
      hevidence.2.accepted
  exact ⟨⟨hingress, hevidence.2⟩, world', hpromotes,
    hevidence.1.1.rebaseWorld hpromotes.1 hcore, hevidence.1.2, htrusted⟩

end RecM

end Ix.Tc
