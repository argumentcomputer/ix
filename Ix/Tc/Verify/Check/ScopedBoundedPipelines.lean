import Ix.Tc.Verify.Check.BoundedPipelines
import Ix.Tc.Verify.RecursiveMethods.ScopedCallDomains

/-!
# Run-scoped standalone-checker pipelines

This is K3's bounded type/value pipeline with `StateInScope` retained across
every method callback.  It deliberately consumes `Methods.ScopedWFAtOn`
directly and contains no conversion to the legacy global suffix model.
-/

namespace Ix.Tc

namespace Methods

/-- Strong full inference over one bounded call domain and one finite suffix
state domain. -/
def ScopedFullInferenceWFAtOn
    {trProj : RawProjRel} {world : VerifyWorld}
    (model : ScopedKernelSuffixModel trProj world)
    (support : RunSupport) (calls : CallDomain) (methods : Methods .anon) :
    Prop :=
  ∀ {Delta : KVLCtx} {s : TcState .anon}
      {source : KExpr .anon} {sourceV : Lean4Lean.VExpr},
    calls.infer source →
    s.inferOnly = false →
    PreTrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
      sourceV →
    TcM.WF
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support Delta) s
      (methods.infer source)
      (fun result after =>
        after.inferOnly = false ∧
          FullInferPost trProj world support model.keys.uvars Delta source
            sourceV result)
      (fun _ after => after.inferOnly = false)

namespace ScopedFullInferenceWFAtOn

/-- Ordinary scoped inference upgrades to the K3 contract wherever raw
ingress is intrinsically typed. -/
theorem ofTypedIngress
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {support : RunSupport} {calls : CallDomain} {methods : Methods .anon}
    (semantic : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) support calls methods)
    (policy : methods.PreservesInferOnly)
    (upgrade : ∀ {Delta : KVLCtx} {source : KExpr .anon}
        {sourceV : Lean4Lean.VExpr},
      calls.infer source →
      PreTrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
        sourceV →
      TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
        sourceV) :
    Methods.ScopedFullInferenceWFAtOn model support calls methods := by
  intro Delta s source sourceV hcall hbefore hsource
  have htyped := upgrade hcall hsource
  apply TcM.WF.mono
    (TcM.PreservesInferOnly.strengthenWFValue
      (semantic.infer hcall htyped) (policy.infer source) hbefore)
  · intro _ _ post
    exact ⟨post.1, FullInferPost.of_typed htyped post.2⟩
  · intro _ _ post
    exact post.1

/-- A singleton sort domain is intrinsically typed. -/
theorem ofSingletonSort
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {support : RunSupport} {u : KUniv .anon} {info : ExprInfo .anon}
    {methods : Methods .anon}
    (semantic : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) support
      (.singletonInfer (.sort u info)) methods)
    (policy : methods.PreservesInferOnly) :
    Methods.ScopedFullInferenceWFAtOn model support
      (.singletonInfer (.sort u info)) methods := by
  apply ofTypedIngress semantic policy
  intro Delta source sourceV hcall hsource
  change source = .sort u info at hcall
  subst source
  cases hsource with
  | sort hu => exact .sort hu

end ScopedFullInferenceWFAtOn

end Methods

/-- Declaration-local K3 resources whose method contracts preserve the
finite suffix-state witness. -/
structure ScopedStandalonePipelineResources
    {trProj : RawProjRel} {world : VerifyWorld}
    (model : ScopedKernelSuffixModel trProj world)
    (support : RunSupport) (calls : Methods.CallDomain)
    (methods : Methods .anon) : Type where
  fullInference : Methods.ScopedFullInferenceWFAtOn model support calls
    (Methods.next methods)
  sorts : SortComponentResources support
  typeSources : KExpr .anon → Prop
  valueSources : KExpr .anon → KExpr .anon → Prop
  typeInfer : ∀ {source}, typeSources source → calls.infer source
  valueInfer : ∀ {value declaredType},
    valueSources value declaredType → calls.infer value
  typeWhnf : ∀ {Delta : KVLCtx} {source : KExpr .anon}
      {sourceV : Lean4Lean.VExpr} {inferred : KExpr .anon},
    typeSources source →
    FullInferPost trProj world support model.keys.uvars Delta source sourceV
      inferred →
    calls.AdmitsEnsureSortDirect inferred
  valueDefEq : ∀ {Delta : KVLCtx} {value declaredType : KExpr .anon}
      {valueV : Lean4Lean.VExpr} {inferred : KExpr .anon},
    valueSources value declaredType →
    FullInferPost trProj world support model.keys.uvars Delta value valueV
      inferred →
    calls.isDefEq inferred declaredType

namespace ScopedStandalonePipelineResources

inductive Covers
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {support : RunSupport} {calls : Methods.CallDomain}
    {methods : Methods .anon}
    (resources : ScopedStandalonePipelineResources model support calls
      methods) : KConst .anon → Prop
  | axiom
      {name : Mode.anon.F Name} {levelParams : Mode.anon.F (Array Name)}
      {isUnsafe : Bool} {levels : UInt64} {type : KExpr .anon} :
    resources.typeSources type →
    Covers resources (.axio name levelParams isUnsafe levels type)
  | defn
      {name : Mode.anon.F Name} {levelParams : Mode.anon.F (Array Name)}
      {kind : Ix.DefKind} {safety : Ix.DefinitionSafety}
      {hints : Lean.ReducibilityHints} {levels : UInt64}
      {type value : KExpr .anon}
      {leanAll : Mode.anon.F (Array (KId .anon))} {block : KId .anon} :
    resources.typeSources type →
    resources.valueSources value type →
    Covers resources
      (.defn name levelParams kind safety hints levels type value leanAll
        block)

/-- Exact scoped resources for a concrete sort axiom. -/
def singletonSortAxiom
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {support : RunSupport} {u : KUniv .anon} {info : ExprInfo .anon}
    {methods : Methods .anon}
    (hfull : Methods.ScopedFullInferenceWFAtOn model support
      (.singletonInfer (.sort u info)) (Methods.next methods))
    (hsorts : SortComponentResources support)
    (hresults : ∀ {result : KExpr .anon}, support result →
      ∃ resultUniv resultInfo, result = .sort resultUniv resultInfo) :
    ScopedStandalonePipelineResources model support
      (.singletonInfer (.sort u info)) methods where
  fullInference := hfull
  sorts := hsorts
  typeSources := fun source => source = .sort u info
  valueSources := fun _ _ => False
  typeInfer hsource := hsource
  valueInfer hsource := False.elim hsource
  typeWhnf := by
    intro Delta source sourceV inferred hsource hpost
    obtain ⟨resultUniv, resultInfo, rfl⟩ := hresults hpost.1
    trivial
  valueDefEq hsource := False.elim hsource

end ScopedStandalonePipelineResources

namespace RecM

private theorem ensureSortDirect_scopedWFAtOn
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {support : RunSupport} {calls : Methods.CallDomain}
    {methods : Methods .anon} {Delta : KVLCtx} {s : TcState .anon}
    {input : KExpr .anon} {inputV : Lean4Lean.VExpr}
    (hmethods : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) support calls
      (Methods.next methods))
    (hresources : SortComponentResources support)
    (hcall : calls.AdmitsEnsureSortDirect input)
    (hinputSupport : support input)
    (hinput : TrKExpr world.venv model.keys.uvars world.nameOf trProj Delta
      input inputV) :
    TcM.WF
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support Delta) s
      ((ensureSortDirect input).run methods)
      (fun result _ => SortView world support model.keys.uvars Delta inputV
        result) := by
  obtain ⟨inputCoreV, hinputCore, hinputEq⟩ := hinput
  cases input <;> simp only [ensureSortDirect, ReaderT.run_pure, pure_bind]
  case sort result info =>
    apply TcM.WF.pure
    intro _
    obtain ⟨hsize, hsubterms⟩ := hresources hinputSupport
    cases hinputCore with
    | sort hlevel =>
        exact {
          sizeBound := hsize
          subtermSupport := hsubterms
          levelWF := hlevel
          inputEq := hinputEq.symm }
  all_goals
    have hwhnf := hmethods.whnf (s := s) hcall hinputCore
    simp only [Methods.next] at hwhnf
    unfold ensureSortWhnf
    simp only [ReaderT.run_bind]
    apply TcM.WF.bind hwhnf
    intro reduced after hred
    rcases hred with ⟨hreducedSupport, reducedV, hreducedTr,
      hcoreReduced⟩
    cases reduced <;> simp only
    case sort result info =>
      cases hreducedTr with
      | sort hlevel =>
          obtain ⟨hsize, hsubterms⟩ := hresources hreducedSupport
          exact TcM.WF.pure fun hI =>
            { sizeBound := hsize
              subtermSupport := hsubterms
              levelWF := hlevel
              inputEq := hinputEq.symm.trans world.venvWF
                hI.1.2.1.wf.toCtx hcoreReduced }
    all_goals
      exact TcM.WF.throw fun _ => trivial

theorem checkTypePipeline_scoped_sound
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {support : RunSupport} {calls : Methods.CallDomain}
    {methods : Methods .anon}
    (resources : ScopedStandalonePipelineResources model support calls
      methods)
    (hmethods : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) support calls
      (Methods.next methods))
    (hpolicyMethods : (Methods.next methods).PreservesInferOnly)
    {Delta : KVLCtx} {s after : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsourceCall : resources.typeSources source)
    (hsource : PreTrKExprS world.venv model.keys.uvars world.nameOf trProj
      Delta source sourceV)
    (hpolicy : s.inferOnly = false)
    (hI : ScopedWhnfStateInv model .noAccel
      (kernelCacheSemantics model.keys trProj) support Delta s)
    (hrun :
      ((do
        let inferred ← infer source
        let _ ← ensureSortDirect inferred).run methods) s = .ok () after) :
    ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support Delta after ∧
      after.inferOnly = false ∧
        TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
          sourceV ∧
        TypeCheckEvidence trProj world support model.keys.uvars Delta
          sourceV := by
  have hinfer : TcM.WF
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support Delta) s
      ((infer source).run methods)
      (fun result after => after.inferOnly = false ∧
        FullInferPost trProj world support model.keys.uvars Delta source
          sourceV result)
      (fun _ after => after.inferOnly = false) := by
    simpa [Methods.next] using
      resources.fullInference (resources.typeInfer hsourceCall) hpolicy hsource
  have hpipeline : TcM.WF
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support Delta) s
      ((do
        let inferred ← infer source
        let _ ← ensureSortDirect inferred).run methods)
      (fun _ after => after.inferOnly = false ∧
        TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
          sourceV ∧
        TypeCheckEvidence trProj world support model.keys.uvars Delta
          sourceV)
      (fun _ after => after.inferOnly = false) := by
    simp only [ReaderT.run_bind, ReaderT.run_pure]
    apply TcM.WF.bind hinfer
    intro inferred afterInfer hinferred
    rcases hinferred with
      ⟨hpolicyAfter, hinferredSupport, hsourceTr, inferredV,
        hinferredTr, hsourceType⟩
    have hfull : FullInferPost trProj world support model.keys.uvars Delta
        source sourceV inferred :=
      ⟨hinferredSupport, hsourceTr, inferredV, hinferredTr, hsourceType⟩
    have hsortSemantic := ensureSortDirect_scopedWFAtOn (s := afterInfer)
      hmethods resources.sorts (resources.typeWhnf hsourceCall hfull)
      hinferredSupport hinferredTr
    have hwhnfPolicy : ∀ candidate,
        ((whnf candidate).run methods).PreservesInferOnly := by
      intro candidate
      simpa [Methods.next] using hpolicyMethods.whnf candidate
    have hsort : TcM.WF
        (ScopedWhnfStateInv model .noAccel
          (kernelCacheSemantics model.keys trProj) support Delta)
        afterInfer ((ensureSortDirect inferred).run methods)
        (fun result after => after.inferOnly = false ∧
          SortView world support model.keys.uvars Delta inferredV result)
        (fun _ after => after.inferOnly = false) := by
      apply TcM.WF.mono
        (TcM.PreservesInferOnly.strengthenWFValue hsortSemantic
          (ensureSortDirect_preservesInferOnly hwhnfPolicy) hpolicyAfter)
      · intro _ _ post
        exact post
      · intro _ _ post
        exact post.1
    apply TcM.WF.bind hsort
    intro sort _ hsortPost
    exact TcM.WF.pure fun _ =>
      ⟨hsortPost.1, hsourceTr, inferred, inferredV, hinferredTr,
        hsourceType, sort, hsortPost.2⟩
  have hpost := hpipeline hI
  rw [hrun] at hpost
  exact hpost

theorem checkValuePipeline_scoped_sound
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {support : RunSupport} {calls : Methods.CallDomain}
    {methods : Methods .anon}
    (resources : ScopedStandalonePipelineResources model support calls
      methods)
    (hmethods : Methods.ScopedWFAtOn model .noAccel
      (kernelCacheSemantics model.keys trProj) support calls
      (Methods.next methods))
    {Delta : KVLCtx} {s after : TcState .anon}
    {value declaredType : KExpr .anon}
    {valueV declaredTypeV : Lean4Lean.VExpr}
    (hvalueCall : resources.valueSources value declaredType)
    (hvalue : PreTrKExprS world.venv model.keys.uvars world.nameOf trProj
      Delta value valueV)
    (hdeclared : TrKExprS world.venv model.keys.uvars world.nameOf trProj
      Delta declaredType declaredTypeV)
    (hpolicy : s.inferOnly = false)
    (hI : ScopedWhnfStateInv model .noAccel
      (kernelCacheSemantics model.keys trProj) support Delta s)
    (hrun :
      ((do
        let inferredType ← infer value
        if !(← isDefEq inferredType declaredType) then
          throw TcError.declTypeMismatch).run methods) s = .ok () after) :
    ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support Delta after ∧
      ValueCheckEvidence world model.keys.uvars Delta valueV
        declaredTypeV := by
  have hinfer : TcM.WF
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support Delta) s
      ((infer value).run methods)
      (fun result after => after.inferOnly = false ∧
        FullInferPost trProj world support model.keys.uvars Delta value valueV
          result)
      (fun _ after => after.inferOnly = false) := by
    simpa [Methods.next] using
      resources.fullInference (resources.valueInfer hvalueCall) hpolicy hvalue
  have hpipeline : TcM.WF
      (ScopedWhnfStateInv model .noAccel
        (kernelCacheSemantics model.keys trProj) support Delta) s
      ((do
        let inferredType ← infer value
        if !(← isDefEq inferredType declaredType) then
          throw TcError.declTypeMismatch).run methods)
      (fun _ _ => ValueCheckEvidence world model.keys.uvars Delta valueV
        declaredTypeV) := by
    simp only [ReaderT.run_bind]
    apply TcM.WF.bind
      (TcM.WF.mono hinfer (fun _ _ post => post)
        (fun _ _ _ => by trivial))
    intro inferredType afterInfer hinferred
    rcases hinferred with
      ⟨_hpolicyAfter, hinferredSupport, hvalueTr, inferredTypeV,
        hinferredTr, hvalueType⟩
    have hfull : FullInferPost trProj world support model.keys.uvars Delta
        value valueV inferredType :=
      ⟨hinferredSupport, hvalueTr, inferredTypeV, hinferredTr, hvalueType⟩
    obtain ⟨inferredCoreV, hinferredCore, hcoreEq⟩ := hinferredTr
    have hdefeq : TcM.WF
        (ScopedWhnfStateInv model .noAccel
          (kernelCacheSemantics model.keys trProj) support Delta)
        afterInfer ((isDefEq inferredType declaredType).run methods)
        (fun answer _ => answer = true →
          world.venv.IsDefEqU model.keys.uvars Delta.toCtx inferredCoreV
            declaredTypeV) := by
      simpa [Methods.next] using
        hmethods.isDefEq (resources.valueDefEq hvalueCall hfull)
          hinferredCore hdeclared
    apply TcM.WF.bind hdefeq
    intro answer _ heq
    cases answer with
    | false =>
        simp only [Bool.not_false, if_true]
        exact TcM.WF.throw fun _ => trivial
    | true =>
        simp only [Bool.not_true, Bool.false_eq]
        exact TcM.WF.pure fun hI =>
          ⟨inferredCoreV,
            hvalueType.defeqU_r world.venvWF hI.1.2.1.wf.toCtx hcoreEq.symm,
            heq rfl⟩
  have hpost := hpipeline hI
  rw [hrun] at hpost
  exact hpost

end RecM

end Ix.Tc
