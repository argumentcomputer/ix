import Ix.Tc.Verify.Check.CheckerEvidence
import Ix.Tc.Verify.Check.FullInferenceKnot
import Ix.Tc.Verify.Check.RecursiveMethodPolicy
import Ix.Tc.Verify.RecursiveMethods.CallDomains

/-!
# Bounded standalone-checker pipelines

The legacy K3 checker proof quantified strong full inference over every
expression in one finite `RunSupport`.  That is too strong: a successful sort
inference places its successor sort in the result footprint, and reusing the
same footprint as the next input domain demands an infinite successor tower.

This module separates the two roles.  `RunSupport` remains the finite state,
cache, collision, and result footprint.  `Methods.FullInferenceWFAtOn`
restricts the stronger pretranslation-to-typing contract to one explicit
method-call domain.  `StandalonePipelineResources` then records only the
type/value calls made by one concrete standalone declaration and the bounded
follow-up calls made on their results.
-/

namespace Ix.Tc

namespace Methods

namespace CallDomain

/-- `ensureSortDirect` performs no recursive WHNF call when its input is
already syntactically a sort.  Every other input must be admitted by the
domain's WHNF component. -/
def AdmitsEnsureSortDirect (calls : CallDomain) : KExpr .anon → Prop
  | .sort _ _ => True
  | source => calls.whnf source

end CallDomain

/-- Strong K3 inference, restricted to the inference calls admitted at one
finite method-table depth.  Unlike ordinary C1A inference, the premise is an
untyped `PreTrKExprS` and the successful postcondition constructs the typed
translation. -/
def FullInferenceWFAtOn
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat)
    (calls : CallDomain) (methods : Methods .anon) : Prop :=
  ∀ {Delta : KVLCtx} {s : TcState .anon}
      {source : KExpr .anon} {sourceV : Lean4Lean.VExpr},
    calls.infer source →
    s.inferOnly = false →
    PreTrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      (methods.infer source)
      (fun result after =>
        after.inferOnly = false ∧
          FullInferPost trProj world support uvars Delta source sourceV
            result)
      (fun _ after => after.inferOnly = false)

namespace FullInferenceWFAtOn

/-- Ordinary bounded inference already implies the stronger K3 contract on
an input domain whose pretranslations can be upgraded without running the
checker.  This covers syntax-directed typed leaves such as sorts while
retaining the independent inference-policy frame on both outcomes. -/
theorem ofTypedIngress
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {calls : CallDomain} {methods : Methods .anon}
    (semantic : Methods.WFAtOn .noAccel semantics trProj world support
      uvars calls methods)
    (policy : methods.PreservesInferOnly)
    (upgrade : ∀ {Delta : KVLCtx} {source : KExpr .anon}
        {sourceV : Lean4Lean.VExpr},
      calls.infer source →
      PreTrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
      TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV) :
    Methods.FullInferenceWFAtOn semantics trProj world support uvars calls
      methods := by
  intro Delta s source sourceV hcall hbefore hsource
  have htyped := upgrade hcall hsource
  apply TcM.WF.mono
    (TcM.PreservesInferOnly.strengthenWFValue
      (semantic.infer hcall htyped) (policy.infer source) hbefore)
  · intro _ _ post
    exact ⟨post.1, FullInferPost.of_typed htyped post.2⟩
  · intro _ _ post
    exact post.1

/-- A singleton sort domain is a typed-ingress domain: its `PreTrKExprS`
constructor already contains the level well-formedness needed by
`TrKExprS.sort`. -/
theorem ofSingletonSort
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {u : KUniv .anon} {info : ExprInfo .anon} {methods : Methods .anon}
    (semantic : Methods.WFAtOn .noAccel semantics trProj world support
      uvars (.singletonInfer (.sort u info)) methods)
    (policy : methods.PreservesInferOnly) :
    Methods.FullInferenceWFAtOn semantics trProj world support uvars
      (.singletonInfer (.sort u info)) methods := by
  apply ofTypedIngress semantic policy
  intro Delta source sourceV hcall hsource
  change source = .sort u info at hcall
  subst source
  cases hsource with
  | sort hu => exact .sort hu

/-- Restrict the legacy all-support strong contract to an explicit call
domain.  This is a migration adapter; new public results consume the bounded
contract directly. -/
theorem ofFullInferenceWFAt
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {calls : CallDomain} {methods : Methods .anon}
    (within : calls.Within support)
    (contract : Methods.FullInferenceWFAt semantics trProj world support
      uvars methods) :
    Methods.FullInferenceWFAtOn semantics trProj world support uvars calls
      methods := by
  intro Delta s source sourceV hcall hpolicy hsource
  exact contract hpolicy (within.infer hcall) hsource

/-- The exhausted method table satisfies the strong contract for every
bounded domain because its inference field throws without changing state. -/
theorem methodsOut
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat)
    (calls : CallDomain) :
    Methods.FullInferenceWFAtOn semantics trProj world support uvars calls
      (Ix.Tc.methodsOut : Methods .anon) := by
  intro Delta s source sourceV hcall hpolicy hsource
  exact TcM.WF.throw fun _ => hpolicy

end FullInferenceWFAtOn

end Methods

/-- Declaration-local resources for the two production checker pipelines.

`calls` is the successor-layer domain: `checkConstMember` executes
`RecM.infer`, `RecM.whnf`, and `RecM.isDefEq` over `methods`, which are exactly
the fields of `Methods.next methods`.  The two source predicates need not be
closed under results; the explicit `typeWhnf` and `valueDefEq` fields admit
only the follow-up calls actually made by the pipelines. -/
structure StandalonePipelineResources
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat)
    (calls : Methods.CallDomain) (methods : Methods .anon) : Type where
  fullInference : Methods.FullInferenceWFAtOn semantics trProj world support
    uvars calls (Methods.next methods)
  sorts : SortComponentResources support
  typeSources : KExpr .anon → Prop
  valueSources : KExpr .anon → KExpr .anon → Prop
  typeInfer : ∀ {source}, typeSources source → calls.infer source
  valueInfer : ∀ {value declaredType},
    valueSources value declaredType → calls.infer value
  typeWhnf : ∀ {Delta : KVLCtx} {source : KExpr .anon}
      {sourceV : Lean4Lean.VExpr} {inferred : KExpr .anon},
    typeSources source →
    FullInferPost trProj world support uvars Delta source sourceV inferred →
    calls.AdmitsEnsureSortDirect inferred
  valueDefEq : ∀ {Delta : KVLCtx} {value declaredType : KExpr .anon}
      {valueV : Lean4Lean.VExpr} {inferred : KExpr .anon},
    valueSources value declaredType →
    FullInferPost trProj world support uvars Delta value valueV inferred →
    calls.isDefEq inferred declaredType

namespace StandalonePipelineResources

/-- The exact declaration roots admitted by a bounded pipeline resource.
Only standalone axioms and definition-family declarations have constructors;
the remaining production shapes belong to the later atomic-block theorem. -/
inductive Covers
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    (resources : StandalonePipelineResources semantics trProj world support
      uvars calls methods) : KConst .anon → Prop
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

/-- Compatibility constructor from the legacy all-support full-inference
context.  Its resulting call domain is explicitly `.support support`, making
the old over-approximation visible instead of baking it into the new public
interface. -/
def ofFullInferenceWFAt
    {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (hfull : Methods.FullInferenceWFAt semantics trProj world support uvars
      (Methods.next methods))
    (hsorts : SortComponentResources support) :
    StandalonePipelineResources semantics trProj world support uvars
      (.support support) methods where
  fullInference := Methods.FullInferenceWFAtOn.ofFullInferenceWFAt
    (Methods.CallDomain.support_within support) hfull
  sorts := hsorts
  typeSources := support
  valueSources := fun value declaredType =>
    support value ∧ support declaredType
  typeInfer hsource := hsource
  valueInfer hsource := hsource.1
  typeWhnf := by
    intro Delta source sourceV inferred hsource hpost
    cases inferred <;> simp [Methods.CallDomain.AdmitsEnsureSortDirect]
    all_goals exact hpost.1
  valueDefEq hsource hpost := ⟨hpost.1, hsource.2⟩

/-- Exact resources for an axiom whose type is one concrete sort.  The
result-footprint premise is intentionally representation-level: if every
possible inference result in this small fixture is syntactically a sort,
`ensureSortDirect` takes its no-callback fast path. -/
def singletonSortAxiom
    {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {u : KUniv .anon} {info : ExprInfo .anon}
    {methods : Methods .anon}
    (hfull : Methods.FullInferenceWFAtOn semantics trProj world support uvars
      (.singletonInfer (.sort u info)) (Methods.next methods))
    (hsorts : SortComponentResources support)
    (hresults : ∀ {result : KExpr .anon}, support result →
      ∃ resultUniv resultInfo, result = .sort resultUniv resultInfo) :
    StandalonePipelineResources semantics trProj world support uvars
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

end StandalonePipelineResources

namespace RecM

/-- Sort exposure using one explicitly admitted direct-WHNF call rather than
the legacy all-support `DirectWhnf.WFAt` callback. -/
private theorem ensureSortDirect_wfAtOn
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    {Delta : KVLCtx} {s : TcState .anon} {input : KExpr .anon}
    {inputV : Lean4Lean.VExpr}
    (hmethods : Methods.WFAtOn .noAccel semantics trProj world support uvars
      calls (Methods.next methods))
    (hresources : SortComponentResources support)
    (hcall : calls.AdmitsEnsureSortDirect input)
    (hinputSupport : support input)
    (hinput : TrKExpr world.venv uvars world.nameOf trProj Delta input
      inputV) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((ensureSortDirect input).run methods)
      (fun result _ => SortView world support uvars Delta inputV result) := by
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
    rcases hred with
      ⟨hreducedSupport, reducedV, hreducedTr, hcoreReduced⟩
    cases reduced <;> simp only
    case sort result info =>
      cases hreducedTr with
      | sort hlevel =>
          obtain ⟨hsize, hsubterms⟩ := hresources hreducedSupport
          exact TcM.WF.pure fun hI =>
            { sizeBound := hsize
              subtermSupport := hsubterms
              levelWF := hlevel
              inputEq := hinputEq.symm.trans world.venvWF hI.2.1.wf.toCtx
                hcoreReduced }
    all_goals
      exact TcM.WF.throw fun _ => trivial

/-- A bounded successful type pipeline constructs the same K3 evidence as
the legacy proof, but every method call is justified by the declaration's
successor-layer call domain. -/
theorem checkTypePipeline_bounded_sound
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    (resources : StandalonePipelineResources semantics trProj world support
      uvars calls methods)
    (hmethods : Methods.WFAtOn .noAccel semantics trProj world support uvars
      calls (Methods.next methods))
    (hpolicyMethods : (Methods.next methods).PreservesInferOnly)
    {Delta : KVLCtx} {s after : TcState .anon}
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsourceCall : resources.typeSources source)
    (hsource : PreTrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hpolicy : s.inferOnly = false)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Delta s)
    (hrun :
      ((do
        let inferred ← infer source
        let _ ← ensureSortDirect inferred).run methods) s = .ok () after) :
    WhnfStateInv .noAccel semantics trProj world support uvars Delta after ∧
      after.inferOnly = false ∧
        TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV ∧
        TypeCheckEvidence trProj world support uvars Delta sourceV := by
  have hinfer : TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((infer source).run methods)
      (fun result after => after.inferOnly = false ∧
        FullInferPost trProj world support uvars Delta source sourceV result)
      (fun _ after => after.inferOnly = false) := by
    simpa [Methods.next] using
      resources.fullInference (resources.typeInfer hsourceCall) hpolicy hsource
  have hpipeline : TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((do
        let inferred ← infer source
        let _ ← ensureSortDirect inferred).run methods)
      (fun _ after => after.inferOnly = false ∧
        TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV ∧
        TypeCheckEvidence trProj world support uvars Delta sourceV)
      (fun _ after => after.inferOnly = false) := by
    simp only [ReaderT.run_bind, ReaderT.run_pure]
    apply TcM.WF.bind hinfer
    intro inferred afterInfer hinferred
    rcases hinferred with
      ⟨hpolicyAfter, hinferredSupport, hsourceTr, inferredV,
        hinferredTr, hsourceType⟩
    have hfull : FullInferPost trProj world support uvars Delta source sourceV
        inferred :=
      ⟨hinferredSupport, hsourceTr, inferredV, hinferredTr, hsourceType⟩
    have hsortSemantic := ensureSortDirect_wfAtOn (s := afterInfer) hmethods
      resources.sorts (resources.typeWhnf hsourceCall hfull)
      hinferredSupport hinferredTr
    have hwhnfPolicy : ∀ candidate,
        ((whnf candidate).run methods).PreservesInferOnly := by
      intro candidate
      simpa [Methods.next] using hpolicyMethods.whnf candidate
    have hsort : TcM.WF
        (WhnfStateInv .noAccel semantics trProj world support uvars Delta)
        afterInfer ((ensureSortDirect inferred).run methods)
        (fun result after => after.inferOnly = false ∧
          SortView world support uvars Delta inferredV result)
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
      ⟨hsortPost.1, hsourceTr,
        inferred, inferredV, hinferredTr, hsourceType, sort, hsortPost.2⟩
  have hpost := hpipeline hI
  rw [hrun] at hpost
  exact hpost

/-- A bounded successful value pipeline proves that the translated value has
the declaration's advertised type.  The inferred result/declared-type DefEq
call is admitted explicitly rather than by all-support quantification. -/
theorem checkValuePipeline_bounded_sound
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {calls : Methods.CallDomain} {methods : Methods .anon}
    (resources : StandalonePipelineResources semantics trProj world support
      uvars calls methods)
    (hmethods : Methods.WFAtOn .noAccel semantics trProj world support uvars
      calls (Methods.next methods))
    {Delta : KVLCtx} {s after : TcState .anon}
    {value declaredType : KExpr .anon}
    {valueV declaredTypeV : Lean4Lean.VExpr}
    (hvalueCall : resources.valueSources value declaredType)
    (hvalue : PreTrKExprS world.venv uvars world.nameOf trProj Delta value
      valueV)
    (hdeclared : TrKExprS world.venv uvars world.nameOf trProj Delta
      declaredType declaredTypeV)
    (hpolicy : s.inferOnly = false)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Delta s)
    (hrun :
      ((do
        let inferredType ← infer value
        if !(← isDefEq inferredType declaredType) then
          throw TcError.declTypeMismatch).run methods) s = .ok () after) :
    WhnfStateInv .noAccel semantics trProj world support uvars Delta after ∧
      ValueCheckEvidence world uvars Delta valueV declaredTypeV := by
  have hinfer : TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((infer value).run methods)
      (fun result after => after.inferOnly = false ∧
        FullInferPost trProj world support uvars Delta value valueV result)
      (fun _ after => after.inferOnly = false) := by
    simpa [Methods.next] using
      resources.fullInference (resources.valueInfer hvalueCall) hpolicy hvalue
  have hpipeline : TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((do
        let inferredType ← infer value
        if !(← isDefEq inferredType declaredType) then
          throw TcError.declTypeMismatch).run methods)
      (fun _ _ => ValueCheckEvidence world uvars Delta valueV declaredTypeV) := by
    simp only [ReaderT.run_bind]
    apply TcM.WF.bind
      (TcM.WF.mono hinfer (fun _ _ post => post)
        (fun _ _ _ => by trivial))
    intro inferredType afterInfer hinferred
    rcases hinferred with
      ⟨_hpolicyAfter, hinferredSupport, hvalueTr, inferredTypeV,
        hinferredTr, hvalueType⟩
    have hfull : FullInferPost trProj world support uvars Delta value valueV
        inferredType :=
      ⟨hinferredSupport, hvalueTr, inferredTypeV, hinferredTr, hvalueType⟩
    obtain ⟨inferredCoreV, hinferredCore, hcoreEq⟩ := hinferredTr
    have hdefeq : TcM.WF
        (WhnfStateInv .noAccel semantics trProj world support uvars Delta)
        afterInfer
        ((isDefEq inferredType declaredType).run methods)
        (fun answer _ => answer = true →
          world.venv.IsDefEqU uvars Delta.toCtx inferredCoreV declaredTypeV) := by
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
        exact TcM.WF.pure fun _ =>
          ⟨inferredCoreV,
            hvalueType.defeqU_r world.venvWF hI.2.1.wf.toCtx hcoreEq.symm,
            heq rfl⟩
  have hpost := hpipeline hI
  rw [hrun] at hpost
  exact hpost

end RecM

end Ix.Tc
