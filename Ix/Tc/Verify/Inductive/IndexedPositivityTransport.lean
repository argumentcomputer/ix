import Ix.Tc.Verify.Inductive.IndexedCandidateOperations
import Ix.Tc.Verify.Inductive.IndexedProductionPositivity
import Ix.Tc.Verify.Inductive.ExactLeanSyntax

/-!
# IndexedVec positivity transport

This module instantiates the operation-shaped positivity boundary for the
production-ingressed `IndexedVec` constructor.  The two nonrecursive field
domains close through the root-free branch.  The recursive tail retains the
exact Ix WHNF cache transition, so the correspondence does not silently treat
the stateful production reducer as a pure function.
-/

namespace Ix.Tc.IndexedRecursiveFixture

open Lean4Lean.InductiveReplayFixtures

/-! ## Finite Lean4Lean observations at the trust boundary

The upstream replay modules are useful for naming the exact candidate states,
but their proof lemmas intentionally depend on reflected implementation
equations.  E2c does not inherit that trust.  Recheck the finite observations
consumed below with private native facts, so the exported transport depends on
the concrete executions without admitting those reflected equations. -/

private theorem indexedVecNatHasNoIndOccTrusted :
    Lean4Lean.AddInductive.hasIndOcc
      indexedVecConstructorStats.indConsts (.const ``Nat []) = false := by
  native_decide

private theorem indexedVecAlphaHasNoIndOccTrusted :
    Lean4Lean.AddInductive.hasIndOcc
      indexedVecConstructorStats.indConsts
        indexedVecConstructorAlpha = false := by
  native_decide

private theorem indexedVecTailHasIndOccTrusted :
    Lean4Lean.AddInductive.hasIndOcc
      indexedVecConstructorStats.indConsts
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr) = true := by
  native_decide

private theorem indexedVecTailAppIsValidTrusted :
    Lean4Lean.AddInductive.isValidIndApp?
      indexedVecConstructorStats
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr) = some 0 := by
  native_decide

/-! ## Exact production WHNF observation -/

def ixConsTailWhnfOutcome :=
  (RecM.whnf ixConsTailDomain).run checkerMethods ixConsTailDomainState

def ixConsTailWhnfAfter : TcState .anon :=
  match ixConsTailWhnfOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def ixConsTailWhnfResult : KExpr .anon :=
  match ixConsTailWhnfOutcome with
  | .ok result _ => result
  | .error _ _ => default

def ixConsTailWhnfSucceeded : Bool :=
  match ixConsTailWhnfOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem ixConsTailWhnfSucceededNative :
    ixConsTailWhnfSucceeded = true := by
  native_decide

theorem ixConsTailWhnfOutcomeRun :
    (RecM.whnf ixConsTailDomain).run checkerMethods ixConsTailDomainState =
      .ok ixConsTailWhnfResult ixConsTailWhnfAfter := by
  have success := ixConsTailWhnfSucceededNative
  unfold ixConsTailWhnfSucceeded at success
  unfold ixConsTailWhnfResult ixConsTailWhnfAfter
  generalize houtcome : ixConsTailWhnfOutcome = outcome at success ⊢
  cases outcome <;> simp_all [ixConsTailWhnfOutcome]

/-- The projected WHNF result is checked structurally against the retained
Lean candidate. This deliberately does not turn address-based `KExpr` Boolean
equality into structural equality. -/
private theorem ixConsTailWhnfResultCandidateCheckNative :
    CandidateSyntax.check nameOf (pairedFVarMatches alphaNPair) [`u]
      ixConsTailWhnfResult
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr) = true := by
  native_decide

theorem ixConsTailWhnfResultCandidateSyntax :
    CandidateSyntaxRel nameOf
      (fun ixId leanId => pairedFVarMatches alphaNPair ixId leanId = true)
      (fun ixLevel leanLevel =>
        CandidateSyntax.levelMatches [`u] ixLevel leanLevel = true)
      ixConsTailWhnfResult
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr) :=
  CandidateSyntax.rel_of_check ixConsTailWhnfResultCandidateCheckNative

/-! ## Root occurrence correspondence -/

theorem ixConsNatDomainRootFree :
    exprMentionsAnyAddr ixConsNatDomain #[familyId.addr] = false := by
  rw [CandidateSyntaxRel.mentionsAnyAddr_eq_hasIndOcc candidateBlockSyntax
    natDomainCandidateSyntax]
  exact indexedVecNatHasNoIndOccTrusted

theorem ixConsHeadDomainRootFree :
    exprMentionsAnyAddr ixConsHeadDomain #[familyId.addr] = false := by
  rw [CandidateSyntaxRel.mentionsAnyAddr_eq_hasIndOcc candidateBlockSyntax
    headDomainCandidateSyntax]
  exact indexedVecAlphaHasNoIndOccTrusted

theorem ixConsTailDomainMentionsRoot :
    exprMentionsAnyAddr ixConsTailDomain #[familyId.addr] = true := by
  rw [CandidateSyntaxRel.mentionsAnyAddr_eq_hasIndOcc candidateBlockSyntax
    tailDomainCandidateSyntax]
  exact indexedVecTailHasIndOccTrusted

/-! ## Exact Lean4Lean WHNF observations -/

private theorem indexedVecNatCandidateWhnfNative :
    ExactLeanSyntax.exceptExprCheck
      (Lean4Lean.TypeChecker.M.run ctorEnv
        .safe indexedVecConstructorContext.lctx [`u]
        ({} : Lean4Lean.FuelConfig)
        (Lean4Lean.TypeChecker.whnf (.const ``Nat [])))
      (.const ``Nat []) = true := by
  native_decide

theorem indexedVecNatCandidateWhnf :
    Lean4Lean.AddInductive.CandidateWhnfStep.Valid
      ⟨indexedVecConstructorContext, (.const ``Nat []),
        (.const ``Nat [])⟩ := by
  unfold Lean4Lean.AddInductive.CandidateWhnfStep.Valid
  exact ExactLeanSyntax.exceptExpr_eq_ok_of_check
    indexedVecNatCandidateWhnfNative

private theorem indexedVecAlphaCandidateWhnfNative :
    ExactLeanSyntax.exceptExprCheck
      (Lean4Lean.TypeChecker.M.run ctorEnv
        .safe indexedVecConstructorNContext.lctx [`u]
        ({} : Lean4Lean.FuelConfig)
        (Lean4Lean.TypeChecker.whnf indexedVecConstructorAlpha))
      indexedVecConstructorAlpha = true := by
  native_decide

theorem indexedVecAlphaCandidateWhnf :
    Lean4Lean.AddInductive.CandidateWhnfStep.Valid
      ⟨indexedVecConstructorNContext, indexedVecConstructorAlpha,
        indexedVecConstructorAlpha⟩ := by
  unfold Lean4Lean.AddInductive.CandidateWhnfStep.Valid
  exact ExactLeanSyntax.exceptExpr_eq_ok_of_check
    indexedVecAlphaCandidateWhnfNative

private theorem indexedVecTailCandidateWhnfNative :
    ExactLeanSyntax.exceptExprCheck
      (Lean4Lean.TypeChecker.M.run ctorEnv
        .safe indexedVecConstructorHeadContext.lctx [`u]
        ({} : Lean4Lean.FuelConfig)
        (Lean4Lean.TypeChecker.whnf
          (ctorIndexedVecApp indexedVecConstructorAlpha
            indexedVecConstructorNExpr)))
      (ctorIndexedVecApp indexedVecConstructorAlpha
        indexedVecConstructorNExpr) = true := by
  native_decide

theorem indexedVecTailCandidateWhnf :
    Lean4Lean.AddInductive.CandidateWhnfStep.Valid
      ⟨indexedVecConstructorHeadContext,
        ctorIndexedVecApp indexedVecConstructorAlpha indexedVecConstructorNExpr,
        ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr⟩ := by
  unfold Lean4Lean.AddInductive.CandidateWhnfStep.Valid
  exact ExactLeanSyntax.exceptExpr_eq_ok_of_check
    indexedVecTailCandidateWhnfNative

/-! ## Concrete operation relations -/

/-- Sources of the three production positivity calls in the `cons`
constructor.  Each constructor fixes both the actual Ix binder state and the
corresponding Lean4Lean validation context. -/
inductive IndexedPositivitySourceRel :
    TcState .anon → Lean4Lean.AddInductive.Context →
      KExpr .anon → Lean.Expr → Prop
  | nat : IndexedPositivitySourceRel ixConsNatDomainState
      indexedVecConstructorContext ixConsNatDomain (.const ``Nat [])
  | head : IndexedPositivitySourceRel ixConsHeadDomainState
      indexedVecConstructorNContext ixConsHeadDomain indexedVecConstructorAlpha
  | tail : IndexedPositivitySourceRel ixConsTailDomainState
      indexedVecConstructorHeadContext ixConsTailDomain
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr)

/-- The only non-root-free result reached by this concrete fixture.  Its Ix
syntax is the projected production WHNF result, related structurally rather
than equated by its content address. -/
inductive IndexedPositivityResultRel :
    TcState .anon → Lean4Lean.AddInductive.Context →
      KExpr .anon → Lean.Expr → Prop
  | tail {ixResult : KExpr .anon}
      (candidate : CandidateSyntaxRel nameOf
        (fun ixId leanId => pairedFVarMatches alphaNPair ixId leanId = true)
        (fun ixLevel leanLevel =>
          CandidateSyntax.levelMatches [`u] ixLevel leanLevel = true)
        ixResult
          (ctorIndexedVecApp indexedVecConstructorAlpha
            indexedVecConstructorNExpr)) :
      IndexedPositivityResultRel ixConsTailWhnfAfter
        indexedVecConstructorHeadContext ixResult
          (ctorIndexedVecApp indexedVecConstructorAlpha
            indexedVecConstructorNExpr)

theorem indexedPositivitySourceMentions
    (relation : IndexedPositivitySourceRel ixState leanContext ixExpr
      leanExpr) :
    exprMentionsAnyAddr ixExpr #[familyId.addr] =
      Lean4Lean.AddInductive.hasIndOcc
        indexedVecConstructorStats.indConsts leanExpr := by
  cases relation with
  | nat =>
      exact CandidateSyntaxRel.mentionsAnyAddr_eq_hasIndOcc
        candidateBlockSyntax natDomainCandidateSyntax
  | head =>
      exact CandidateSyntaxRel.mentionsAnyAddr_eq_hasIndOcc
        candidateBlockSyntax headDomainCandidateSyntax
  | tail =>
      exact CandidateSyntaxRel.mentionsAnyAddr_eq_hasIndOcc
        candidateBlockSyntax tailDomainCandidateSyntax

private theorem indexedPositivityRootFree
    {ixState : TcState .anon} {leanContext : Lean4Lean.AddInductive.Context}
    {ixSource : KExpr .anon} {leanSource : Lean.Expr}
    (relation : IndexedPositivitySourceRel ixState leanContext ixSource
      leanSource)
    (free : exprMentionsAnyAddr ixSource #[familyId.addr] = false) :
    ∃ leanResult,
      Lean4Lean.AddInductive.CandidateWhnfStep.Valid
        ⟨leanContext, leanSource, leanResult⟩ ∧
      Lean4Lean.AddInductive.hasIndOcc
        indexedVecConstructorStats.indConsts leanResult = false := by
  cases relation with
  | nat =>
      exact ⟨.const ``Nat [], indexedVecNatCandidateWhnf,
        indexedVecNatHasNoIndOccTrusted⟩
  | head =>
      exact ⟨indexedVecConstructorAlpha, indexedVecAlphaCandidateWhnf,
        indexedVecAlphaHasNoIndOccTrusted⟩
  | tail =>
      rw [ixConsTailDomainMentionsRoot] at free
      contradiction

private theorem indexedPositivityWhnf
    {ixBefore ixAfter : TcState .anon}
    {leanContext : Lean4Lean.AddInductive.Context}
    {ixSource ixResult : KExpr .anon} {leanSource : Lean.Expr}
    (relation : IndexedPositivitySourceRel ixBefore leanContext ixSource
      leanSource)
    (mentioned : exprMentionsAnyAddr ixSource #[familyId.addr] = true)
    (run : (RecM.whnf ixSource).run checkerMethods ixBefore =
      .ok ixResult ixAfter) :
    ∃ leanResult,
      Lean4Lean.AddInductive.CandidateWhnfStep.Valid
        ⟨leanContext, leanSource, leanResult⟩ ∧
      IndexedPositivityResultRel ixAfter leanContext ixResult leanResult := by
  cases relation with
  | nat =>
      rw [ixConsNatDomainRootFree] at mentioned
      contradiction
  | head =>
      rw [ixConsHeadDomainRootFree] at mentioned
      contradiction
  | tail =>
      rw [ixConsTailWhnfOutcomeRun] at run
      cases run
      exact ⟨ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr,
        indexedVecTailCandidateWhnf,
        .tail ixConsTailWhnfResultCandidateSyntax⟩

private theorem indexedPositivityForall
    {ixState : TcState .anon} {leanContext : Lean4Lean.AddInductive.Context}
    {ixName : Mode.anon.F Name} {ixBinder : Mode.anon.F Lean.BinderInfo}
    {ixDomain ixBody : KExpr .anon} {ixInfo : ExprInfo .anon}
    {leanExpr : Lean.Expr}
    (relation : IndexedPositivityResultRel ixState leanContext
      (.all ixName ixBinder ixDomain ixBody ixInfo) leanExpr) :
    ∃ leanName leanBinder leanDomain leanBody,
      leanExpr = .forallE leanName leanDomain leanBody leanBinder ∧
      IndexedPositivitySourceRel ixState leanContext ixDomain leanDomain ∧
      ∀ {ixOpen : KExpr .anon} {ixFVar : FVarId}
          {ixAfterOpen : TcState .anon},
        TcM.openBinderAnon ixDomain ixBody ixState =
          .ok (ixOpen, ixFVar) ixAfterOpen →
        IndexedPositivitySourceRel ixAfterOpen
          (leanContext.pushLocalDecl leanName leanBinder
            (Lean4Lean.AddInductive.consumeTypeAnnotations leanDomain))
          ixOpen (leanBody.instantiate1 leanContext.freshExpr) := by
  cases relation with
  | tail candidate => cases candidate

private theorem indexedPositivityDirect
    {ixState : TcState .anon} {leanContext : Lean4Lean.AddInductive.Context}
    {ixResult : KExpr .anon} {leanResult : Lean.Expr}
    {id : KId .anon} {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)} {groups : Array (PositivityGroup .anon)}
    {final : TcState .anon}
    (relation : IndexedPositivityResultRel ixState leanContext ixResult
      leanResult)
    (_spine : ixResult.collectSpine = (.const id us info, args))
    (_active : #[familyId.addr].contains id.addr = true)
    (_valid : ValidPositiveRecursiveApplication id us args groups
      #[familyId.addr] checkerMethods ixState final) :
    ∃ targetIdx,
      Lean4Lean.AddInductive.hasIndOcc
          indexedVecConstructorStats.indConsts leanResult = true ∧
        leanResult.isForall = false ∧
        Lean4Lean.AddInductive.isValidIndApp?
          indexedVecConstructorStats leanResult = some targetIdx := by
  cases relation with
  | tail _ =>
      exact ⟨0, indexedVecTailHasIndOccTrusted, rfl,
        indexedVecTailAppIsValidTrusted⟩

/-- Complete concrete flat-positivity transport for the three production
`IndexedVec.cons` field domains.  Its WHNF field consumes the projected Ix
execution, while direct Lean validity comes from exact candidate syntax; no
Theory-level DefEq result is used as a substitute for `isValidIndApp?`. -/
theorem indexedVecFlatPositivityTransport :
    FlatPositivityTraceTransport indexedVecConstructorStats
      #[familyId.addr] checkerMethods IndexedPositivitySourceRel
        IndexedPositivityResultRel where
  rootFree := indexedPositivityRootFree
  whnf := indexedPositivityWhnf
  mentions := indexedPositivitySourceMentions
  forallE := indexedPositivityForall
  direct := indexedPositivityDirect

/-! ## Production flat-positivity traces -/

/-- Exact production positivity run for the recursive tail field. -/
def ixConsTailPositivityOutcome :=
  (RecM.checkPositivityDomainFuel 1 ixConsTailDomain
    indexedVecPositivityGroups #[familyId.addr]).run checkerMethods
      ixConsTailDomainState

def ixConsTailPositivityAfter : TcState .anon :=
  match ixConsTailPositivityOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def ixConsTailPositivitySucceeded : Bool :=
  match ixConsTailPositivityOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem ixConsTailPositivitySucceededNative :
    ixConsTailPositivitySucceeded = true := by
  native_decide

theorem ixConsTailPositivityRun :
    (RecM.checkPositivityDomainFuel 1 ixConsTailDomain
      indexedVecPositivityGroups #[familyId.addr]).run checkerMethods
        ixConsTailDomainState = .ok () ixConsTailPositivityAfter := by
  have success := ixConsTailPositivitySucceededNative
  unfold ixConsTailPositivitySucceeded at success
  unfold ixConsTailPositivityAfter
  generalize houtcome : ixConsTailPositivityOutcome = outcome at success ⊢
  cases outcome <;> simp_all [ixConsTailPositivityOutcome]

/-! The following projections inspect only the constructor of the exact WHNF
spine head.  In particular, they do not compare `KExpr`s through their
address-based `BEq` instance. -/

def ixConsTailWhnfSpineHead : KExpr .anon :=
  ixConsTailWhnfResult.collectSpine.1

def ixConsTailWhnfSpineArgs : Array (KExpr .anon) :=
  ixConsTailWhnfResult.collectSpine.2

def ixConsTailWhnfSpineId : KId .anon :=
  match ixConsTailWhnfSpineHead with
  | .const id _ _ => id
  | _ => default

def ixConsTailWhnfSpineUniverses : Array (KUniv .anon) :=
  match ixConsTailWhnfSpineHead with
  | .const _ universes _ => universes
  | _ => default

def ixConsTailWhnfSpineInfo : ExprInfo .anon :=
  match ixConsTailWhnfSpineHead with
  | .const _ _ info => info
  | head => head.info

def ixConsTailWhnfSpineIsConst : Bool :=
  match ixConsTailWhnfSpineHead with
  | .const .. => true
  | _ => false

private theorem ixConsTailWhnfSpineIsConstNative :
    ixConsTailWhnfSpineIsConst = true := by
  native_decide

theorem ixConsTailWhnfSpine :
    ixConsTailWhnfResult.collectSpine =
      (.const ixConsTailWhnfSpineId ixConsTailWhnfSpineUniverses
        ixConsTailWhnfSpineInfo, ixConsTailWhnfSpineArgs) := by
  have success := ixConsTailWhnfSpineIsConstNative
  generalize hspine : ixConsTailWhnfResult.collectSpine = spine at success ⊢
  rcases spine with ⟨head, args⟩
  cases head <;> simp_all [ixConsTailWhnfSpineIsConst,
    ixConsTailWhnfSpineHead, ixConsTailWhnfSpineArgs,
    ixConsTailWhnfSpineId, ixConsTailWhnfSpineUniverses,
    ixConsTailWhnfSpineInfo]

theorem ixConsTailWhnfNotForall :
    PositivityTerminalForm ixConsTailWhnfResult := by
  have spine := ixConsTailWhnfSpine
  generalize hresult : ixConsTailWhnfResult = result at spine ⊢
  cases result <;>
    simp_all [PositivityTerminalForm, KExpr.collectSpine,
      KExpr.collectSpine.go]

private theorem ixConsTailWhnfSpineActiveNative :
    indexedVecRootPositivityGroup.addrs.contains
      ixConsTailWhnfSpineId.addr = true := by
  native_decide

private theorem ixConsTailDirectPositivityRun :
    (RecM.checkPositiveRecursiveApplication ixConsTailWhnfSpineId
      ixConsTailWhnfSpineUniverses ixConsTailWhnfSpineArgs
      indexedVecPositivityGroups
        indexedVecRootPositivityGroup.addrs).run checkerMethods
          ixConsTailWhnfAfter = .ok () ixConsTailPositivityAfter :=
  RecM.checkPositivityDomainFuel_direct rfl
    (by simpa [indexedVecRootPositivityGroup] using
      ixConsTailDomainMentionsRoot)
    ixConsTailWhnfOutcomeRun ixConsTailWhnfSpine
    ixConsTailWhnfSpineActiveNative ixConsTailPositivityRun

/-- The direct tail branch has the same execution at every positive field
fuel.  Only forall and nested recursion consume the predecessor fuel. -/
theorem ixConsTailPositivityRunAt (fuel : Nat) :
    (RecM.checkPositivityDomainFuel (fuel + 1) ixConsTailDomain
      indexedVecPositivityGroups #[familyId.addr]).run checkerMethods
        ixConsTailDomainState = .ok () ixConsTailPositivityAfter :=
  RecM.checkPositivityDomainFuel_direct_run
    (rootGroup := indexedVecRootPositivityGroup) rfl
    (by simpa [indexedVecRootPositivityGroup] using
      ixConsTailDomainMentionsRoot)
    ixConsTailWhnfOutcomeRun ixConsTailWhnfSpine
    ixConsTailWhnfSpineActiveNative ixConsTailDirectPositivityRun

theorem indexedVecNatFlatPositivityTraceAt (fuel : Nat) :
    FlatPositivityDomainTrace indexedVecPositivityGroups #[familyId.addr]
      checkerMethods (fuel + 1) ixConsNatDomain ixConsNatDomainState
        ixConsNatDomainState := by
  exact .rootFree (fuel := fuel) (rootGroup := indexedVecRootPositivityGroup)
    rfl ixConsNatDomainRootFree

theorem indexedVecHeadFlatPositivityTraceAt (fuel : Nat) :
    FlatPositivityDomainTrace indexedVecPositivityGroups #[familyId.addr]
      checkerMethods (fuel + 1) ixConsHeadDomain ixConsHeadDomainState
        ixConsHeadDomainState := by
  exact .rootFree (fuel := fuel) (rootGroup := indexedVecRootPositivityGroup)
    rfl ixConsHeadDomainRootFree

theorem indexedVecTailFlatPositivityTraceAt (fuel : Nat) :
    FlatPositivityDomainTrace indexedVecPositivityGroups #[familyId.addr]
      checkerMethods (fuel + 1) ixConsTailDomain ixConsTailDomainState
        ixConsTailPositivityAfter := by
  refine FlatPositivityDomainTrace.application
    (fuel := fuel) (rootGroup := indexedVecRootPositivityGroup)
    (source := ixConsTailDomain) (w := ixConsTailWhnfResult)
    (id := ixConsTailWhnfSpineId)
    (us := ixConsTailWhnfSpineUniverses)
    (info := ixConsTailWhnfSpineInfo)
    (args := ixConsTailWhnfSpineArgs)
    (initial := ixConsTailDomainState) (afterWhnf := ixConsTailWhnfAfter)
    (final := ixConsTailPositivityAfter)
    (root := rfl)
    (mentioned := by
      simpa [indexedVecRootPositivityGroup] using
        ixConsTailDomainMentionsRoot)
    (whnf := ixConsTailWhnfOutcomeRun)
    (notForall := ixConsTailWhnfNotForall)
    (spine := ixConsTailWhnfSpine)
    (active := ixConsTailWhnfSpineActiveNative)
    (valid := RecM.checkPositivityDomainFuel_direct_valid rfl
      (by simpa [indexedVecRootPositivityGroup] using
        ixConsTailDomainMentionsRoot)
      ixConsTailWhnfOutcomeRun ixConsTailWhnfSpine
      ixConsTailWhnfSpineActiveNative (ixConsTailPositivityRunAt fuel))

theorem indexedVecNatFlatPositivityTrace :
    FlatPositivityDomainTrace indexedVecPositivityGroups #[familyId.addr]
      checkerMethods 1 ixConsNatDomain ixConsNatDomainState
        ixConsNatDomainState :=
  indexedVecNatFlatPositivityTraceAt 0

theorem indexedVecHeadFlatPositivityTrace :
    FlatPositivityDomainTrace indexedVecPositivityGroups #[familyId.addr]
      checkerMethods 1 ixConsHeadDomain ixConsHeadDomainState
        ixConsHeadDomainState :=
  indexedVecHeadFlatPositivityTraceAt 0

theorem indexedVecTailFlatPositivityTrace :
    FlatPositivityDomainTrace indexedVecPositivityGroups #[familyId.addr]
      checkerMethods 1 ixConsTailDomain ixConsTailDomainState
        ixConsTailPositivityAfter :=
  indexedVecTailFlatPositivityTraceAt 0

/-! ## Lean4Lean constructor-positivity artifacts -/

theorem indexedVecNatConstructorPositivityTraceAt (fuel : Nat) :
    Nonempty (Lean4Lean.AddInductive.ConstructorPositivityTrace
      indexedVecConstructorStats indexedVecKernelCons.name 1
      indexedVecConstructorContext (.const ``Nat []) (fuel + 1)) :=
  FlatPositivityTraceTransport.constructorPositivityTrace
    indexedVecFlatPositivityTransport
      (indexedVecNatFlatPositivityTraceAt fuel) rfl .nat

theorem indexedVecHeadConstructorPositivityTraceAt (fuel : Nat) :
    Nonempty (Lean4Lean.AddInductive.ConstructorPositivityTrace
      indexedVecConstructorStats indexedVecKernelCons.name 2
      indexedVecConstructorNContext indexedVecConstructorAlpha (fuel + 1)) :=
  FlatPositivityTraceTransport.constructorPositivityTrace
    indexedVecFlatPositivityTransport
      (indexedVecHeadFlatPositivityTraceAt fuel) rfl .head

theorem indexedVecTailConstructorPositivityTraceAt (fuel : Nat) :
    Nonempty (Lean4Lean.AddInductive.ConstructorPositivityTrace
      indexedVecConstructorStats indexedVecKernelCons.name 3
      indexedVecConstructorHeadContext
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr) (fuel + 1)) :=
  FlatPositivityTraceTransport.constructorPositivityTrace
    indexedVecFlatPositivityTransport
      (indexedVecTailFlatPositivityTraceAt fuel) rfl .tail

theorem indexedVecNatConstructorPositivityTrace :
    Nonempty (Lean4Lean.AddInductive.ConstructorPositivityTrace
      indexedVecConstructorStats indexedVecKernelCons.name 1
      indexedVecConstructorContext (.const ``Nat []) 1) :=
  indexedVecNatConstructorPositivityTraceAt 0

theorem indexedVecHeadConstructorPositivityTrace :
    Nonempty (Lean4Lean.AddInductive.ConstructorPositivityTrace
      indexedVecConstructorStats indexedVecKernelCons.name 2
      indexedVecConstructorNContext indexedVecConstructorAlpha 1) :=
  indexedVecHeadConstructorPositivityTraceAt 0

theorem indexedVecTailConstructorPositivityTrace :
    Nonempty (Lean4Lean.AddInductive.ConstructorPositivityTrace
      indexedVecConstructorStats indexedVecKernelCons.name 3
      indexedVecConstructorHeadContext
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr) 1) :=
  indexedVecTailConstructorPositivityTraceAt 0

/-! ## Production-selected operation transport

The preceding fixtures retain the original standalone replay from
`checkerInitial`.  The definitions below deliberately form a second boundary:
their states and expressions are the ones projected from the actual
`checkInductiveBlock` execution in `IndexedProductionPositivity`.  Keeping the
two boundaries separate until the constructor-validation consumer has moved
prevents a convenient replay from being mistaken for production linkage.
-/

/-- The shared-parameter fvar selected by production parameter ingress.

The fallback keeps the definition total.  Each candidate-syntax check below
also proves that the selected expression really is the expected fvar, so no
claim relies on the fallback branch. -/
def familyConsParameterFVarId : FVarId :=
  match (familyConsParameterFVars[0]? : Option (KExpr .anon)) with
  | some (KExpr.fvar id _ _) => id
  | _ => default

/-- Fvar pairing at the first ordinary constructor field. -/
def familyConsAlphaPair : List (FVarId × Lean.FVarId) :=
  [(familyConsParameterFVarId, indexedVecConstructorAlphaId)]

/-- Fvar pairing after the production checker has opened the Nat index. -/
def familyConsAlphaNPair : List (FVarId × Lean.FVarId) :=
  [(familyConsParameterFVarId, indexedVecConstructorAlphaId),
    (familyConsNatFVarId, indexedVecConstructorNId)]

private theorem familyConsNatDomainCandidateCheckNative :
    CandidateSyntax.check nameOf (pairedFVarMatches familyConsAlphaPair) [`u]
      familyConsNatDomain (.const ``Nat []) = true := by
  native_decide

private theorem familyConsHeadDomainCandidateCheckNative :
    CandidateSyntax.check nameOf (pairedFVarMatches familyConsAlphaNPair) [`u]
      familyConsHeadDomain indexedVecConstructorAlpha = true := by
  native_decide

private theorem familyConsTailDomainCandidateCheckNative :
    CandidateSyntax.check nameOf (pairedFVarMatches familyConsAlphaNPair) [`u]
      familyConsTailDomain
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr) = true := by
  native_decide

private theorem familyConsTailWhnfCandidateCheckNative :
    CandidateSyntax.check nameOf (pairedFVarMatches familyConsAlphaNPair) [`u]
      familyConsTailDomainWhnfResult
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr) = true := by
  native_decide

theorem familyConsNatDomainCandidateSyntax :
    CandidateSyntaxRel nameOf
      (fun ixId leanId =>
        pairedFVarMatches familyConsAlphaPair ixId leanId = true)
      (fun ixLevel leanLevel =>
        CandidateSyntax.levelMatches [`u] ixLevel leanLevel = true)
      familyConsNatDomain (.const ``Nat []) :=
  CandidateSyntax.rel_of_check familyConsNatDomainCandidateCheckNative

theorem familyConsHeadDomainCandidateSyntax :
    CandidateSyntaxRel nameOf
      (fun ixId leanId =>
        pairedFVarMatches familyConsAlphaNPair ixId leanId = true)
      (fun ixLevel leanLevel =>
        CandidateSyntax.levelMatches [`u] ixLevel leanLevel = true)
      familyConsHeadDomain indexedVecConstructorAlpha :=
  CandidateSyntax.rel_of_check familyConsHeadDomainCandidateCheckNative

theorem familyConsTailDomainCandidateSyntax :
    CandidateSyntaxRel nameOf
      (fun ixId leanId =>
        pairedFVarMatches familyConsAlphaNPair ixId leanId = true)
      (fun ixLevel leanLevel =>
        CandidateSyntax.levelMatches [`u] ixLevel leanLevel = true)
      familyConsTailDomain
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr) :=
  CandidateSyntax.rel_of_check familyConsTailDomainCandidateCheckNative

theorem familyConsTailWhnfCandidateSyntax :
    CandidateSyntaxRel nameOf
      (fun ixId leanId =>
        pairedFVarMatches familyConsAlphaNPair ixId leanId = true)
      (fun ixLevel leanLevel =>
        CandidateSyntax.levelMatches [`u] ixLevel leanLevel = true)
      familyConsTailDomainWhnfResult
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr) :=
  CandidateSyntax.rel_of_check familyConsTailWhnfCandidateCheckNative

/-- Sources are indexed by the exact states reached by the real family-block
checker, rather than by a replay from `checkerInitial`. -/
inductive ProductionIndexedPositivitySourceRel :
    TcState .anon → Lean4Lean.AddInductive.Context →
      KExpr .anon → Lean.Expr → Prop
  | nat : ProductionIndexedPositivitySourceRel familyConsNatDomainState
      indexedVecConstructorContext familyConsNatDomain (.const ``Nat [])
  | head : ProductionIndexedPositivitySourceRel familyConsHeadDomainState
      indexedVecConstructorNContext familyConsHeadDomain
        indexedVecConstructorAlpha
  | tail : ProductionIndexedPositivitySourceRel familyConsTailDomainState
      indexedVecConstructorHeadContext familyConsTailDomain
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr)

/-- The mentioned production source has exactly one WHNF result shape in this
fixture: the recursive `IndexedVec α n` application. -/
inductive ProductionIndexedPositivityResultRel :
    TcState .anon → Lean4Lean.AddInductive.Context →
      KExpr .anon → Lean.Expr → Prop
  | tail {ixResult : KExpr .anon}
      (candidate : CandidateSyntaxRel nameOf
        (fun ixId leanId =>
          pairedFVarMatches familyConsAlphaNPair ixId leanId = true)
        (fun ixLevel leanLevel =>
          CandidateSyntax.levelMatches [`u] ixLevel leanLevel = true)
        ixResult
          (ctorIndexedVecApp indexedVecConstructorAlpha
            indexedVecConstructorNExpr)) :
      ProductionIndexedPositivityResultRel familyConsTailDomainWhnfAfter
        indexedVecConstructorHeadContext ixResult
          (ctorIndexedVecApp indexedVecConstructorAlpha
            indexedVecConstructorNExpr)

theorem productionIndexedPositivitySourceMentions
    (relation : ProductionIndexedPositivitySourceRel ixState leanContext
      ixExpr leanExpr) :
    exprMentionsAnyAddr ixExpr #[familyId.addr] =
      Lean4Lean.AddInductive.hasIndOcc
        indexedVecConstructorStats.indConsts leanExpr := by
  cases relation with
  | nat =>
      exact CandidateSyntaxRel.mentionsAnyAddr_eq_hasIndOcc
        candidateBlockSyntax familyConsNatDomainCandidateSyntax
  | head =>
      exact CandidateSyntaxRel.mentionsAnyAddr_eq_hasIndOcc
        candidateBlockSyntax familyConsHeadDomainCandidateSyntax
  | tail =>
      exact CandidateSyntaxRel.mentionsAnyAddr_eq_hasIndOcc
        candidateBlockSyntax familyConsTailDomainCandidateSyntax

private theorem productionIndexedPositivityRootFree
    {ixState : TcState .anon} {leanContext : Lean4Lean.AddInductive.Context}
    {ixSource : KExpr .anon} {leanSource : Lean.Expr}
    (relation : ProductionIndexedPositivitySourceRel ixState leanContext
      ixSource leanSource)
    (free : exprMentionsAnyAddr ixSource #[familyId.addr] = false) :
    ∃ leanResult,
      Lean4Lean.AddInductive.CandidateWhnfStep.Valid
        ⟨leanContext, leanSource, leanResult⟩ ∧
      Lean4Lean.AddInductive.hasIndOcc
        indexedVecConstructorStats.indConsts leanResult = false := by
  cases relation with
  | nat =>
      exact ⟨.const ``Nat [], indexedVecNatCandidateWhnf,
        indexedVecNatHasNoIndOccTrusted⟩
  | head =>
      exact ⟨indexedVecConstructorAlpha, indexedVecAlphaCandidateWhnf,
        indexedVecAlphaHasNoIndOccTrusted⟩
  | tail =>
      rw [familyConsTailDomainMentionsRoot] at free
      contradiction

private theorem productionIndexedPositivityWhnf
    {ixBefore ixAfter : TcState .anon}
    {leanContext : Lean4Lean.AddInductive.Context}
    {ixSource ixResult : KExpr .anon} {leanSource : Lean.Expr}
    (relation : ProductionIndexedPositivitySourceRel ixBefore leanContext
      ixSource leanSource)
    (mentioned : exprMentionsAnyAddr ixSource #[familyId.addr] = true)
    (run : (RecM.whnf ixSource).run checkerMethods ixBefore =
      .ok ixResult ixAfter) :
    ∃ leanResult,
      Lean4Lean.AddInductive.CandidateWhnfStep.Valid
        ⟨leanContext, leanSource, leanResult⟩ ∧
      ProductionIndexedPositivityResultRel ixAfter leanContext ixResult
        leanResult := by
  cases relation with
  | nat =>
      rw [familyConsNatDomainRootFree] at mentioned
      contradiction
  | head =>
      rw [familyConsHeadDomainRootFree] at mentioned
      contradiction
  | tail =>
      rw [familyConsTailDomainWhnfRun] at run
      cases run
      exact ⟨ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr,
        indexedVecTailCandidateWhnf,
        .tail familyConsTailWhnfCandidateSyntax⟩

private theorem productionIndexedPositivityForall
    {ixState : TcState .anon} {leanContext : Lean4Lean.AddInductive.Context}
    {ixName : Mode.anon.F Name} {ixBinder : Mode.anon.F Lean.BinderInfo}
    {ixDomain ixBody : KExpr .anon} {ixInfo : ExprInfo .anon}
    {leanExpr : Lean.Expr}
    (relation : ProductionIndexedPositivityResultRel ixState leanContext
      (.all ixName ixBinder ixDomain ixBody ixInfo) leanExpr) :
    ∃ leanName leanBinder leanDomain leanBody,
      leanExpr = .forallE leanName leanDomain leanBody leanBinder ∧
      ProductionIndexedPositivitySourceRel ixState leanContext ixDomain
        leanDomain ∧
      ∀ {ixOpen : KExpr .anon} {ixFVar : FVarId}
          {ixAfterOpen : TcState .anon},
        TcM.openBinderAnon ixDomain ixBody ixState =
          .ok (ixOpen, ixFVar) ixAfterOpen →
        ProductionIndexedPositivitySourceRel ixAfterOpen
          (leanContext.pushLocalDecl leanName leanBinder
            (Lean4Lean.AddInductive.consumeTypeAnnotations leanDomain))
          ixOpen (leanBody.instantiate1 leanContext.freshExpr) := by
  cases relation with
  | tail candidate => cases candidate

private theorem productionIndexedPositivityDirect
    {ixState : TcState .anon} {leanContext : Lean4Lean.AddInductive.Context}
    {ixResult : KExpr .anon} {leanResult : Lean.Expr}
    {id : KId .anon} {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)} {groups : Array (PositivityGroup .anon)}
    {final : TcState .anon}
    (relation : ProductionIndexedPositivityResultRel ixState leanContext
      ixResult leanResult)
    (_spine : ixResult.collectSpine = (.const id us info, args))
    (_active : #[familyId.addr].contains id.addr = true)
    (_valid : ValidPositiveRecursiveApplication id us args groups
      #[familyId.addr] checkerMethods ixState final) :
    ∃ targetIdx,
      Lean4Lean.AddInductive.hasIndOcc
          indexedVecConstructorStats.indConsts leanResult = true ∧
        leanResult.isForall = false ∧
        Lean4Lean.AddInductive.isValidIndApp?
          indexedVecConstructorStats leanResult = some targetIdx := by
  cases relation with
  | tail _ =>
      exact ⟨0, indexedVecTailHasIndOccTrusted, rfl,
        indexedVecTailAppIsValidTrusted⟩

/-- Operation-level transport instantiated at the states and fvars selected by
the real `IndexedVec.cons` production execution. -/
theorem indexedVecProductionFlatPositivityTransport :
    FlatPositivityTraceTransport indexedVecConstructorStats
      #[familyId.addr] checkerMethods ProductionIndexedPositivitySourceRel
        ProductionIndexedPositivityResultRel where
  rootFree := productionIndexedPositivityRootFree
  whnf := productionIndexedPositivityWhnf
  mentions := productionIndexedPositivitySourceMentions
  forallE := productionIndexedPositivityForall
  direct := productionIndexedPositivityDirect

/-! ## Production trace transport at the candidate checker's fuel

Ix enters constructor positivity with `maxWhnfFuel`, while Lean4Lean's retained
candidate context has its own inductive fuel.  Fuel cannot be changed for an
arbitrary recursive trace.  The following lemmas first inspect the traces
projected from the real production run and only reindex the two branch forms
whose evidence is independent of the outer fuel: root-free and direct target.
-/

theorem indexedVecProductionNatFlatPositivityTraceAt (fuel : Nat) :
    FlatPositivityDomainTrace familyConsPositivityGroups #[familyId.addr]
      checkerMethods (fuel + 1) familyConsNatDomain familyConsNatDomainState
        familyConsNatDomainState := by
  have trace := indexedVecConsProductionFieldProjection.nat
  cases trace with
  | rootFree root free =>
      exact .rootFree (fuel := fuel)
        (rootGroup := familyConsRootPositivityGroup) rfl
          familyConsNatDomainRootFree
  | «forall» root mentioned whnf domainFree opening tail restored =>
      rw [show familyConsPositivityGroups[0]? =
        some familyConsRootPositivityGroup by rfl] at root
      cases root
      have free :
          exprMentionsAnyAddr familyConsNatDomain
            familyConsRootPositivityGroup.addrs = false := by
        simpa [familyConsRootPositivityGroup] using
          familyConsNatDomainRootFree
      rw [free] at mentioned
      contradiction
  | application root mentioned whnf notForall spine active valid =>
      rw [show familyConsPositivityGroups[0]? =
        some familyConsRootPositivityGroup by rfl] at root
      cases root
      have free :
          exprMentionsAnyAddr familyConsNatDomain
            familyConsRootPositivityGroup.addrs = false := by
        simpa [familyConsRootPositivityGroup] using
          familyConsNatDomainRootFree
      rw [free] at mentioned
      contradiction

theorem indexedVecProductionHeadFlatPositivityTraceAt (fuel : Nat) :
    FlatPositivityDomainTrace familyConsPositivityGroups #[familyId.addr]
      checkerMethods (fuel + 1) familyConsHeadDomain
        familyConsHeadDomainState familyConsHeadDomainState := by
  have trace := indexedVecConsProductionFieldProjection.head
  cases trace with
  | rootFree root free =>
      exact .rootFree (fuel := fuel)
        (rootGroup := familyConsRootPositivityGroup) rfl
          familyConsHeadDomainRootFree
  | «forall» root mentioned whnf domainFree opening tail restored =>
      rw [show familyConsPositivityGroups[0]? =
        some familyConsRootPositivityGroup by rfl] at root
      cases root
      have free :
          exprMentionsAnyAddr familyConsHeadDomain
            familyConsRootPositivityGroup.addrs = false := by
        simpa [familyConsRootPositivityGroup] using
          familyConsHeadDomainRootFree
      rw [free] at mentioned
      contradiction
  | application root mentioned whnf notForall spine active valid =>
      rw [show familyConsPositivityGroups[0]? =
        some familyConsRootPositivityGroup by rfl] at root
      cases root
      have free :
          exprMentionsAnyAddr familyConsHeadDomain
            familyConsRootPositivityGroup.addrs = false := by
        simpa [familyConsRootPositivityGroup] using
          familyConsHeadDomainRootFree
      rw [free] at mentioned
      contradiction

theorem indexedVecProductionTailFlatPositivityTraceAt (fuel : Nat) :
    FlatPositivityDomainTrace familyConsPositivityGroups #[familyId.addr]
      checkerMethods (fuel + 1) familyConsTailDomain
        familyConsTailDomainState familyConsTailDomainAfter := by
  have trace := indexedVecConsProductionFieldProjection.tail
  generalize hfinal : familyConsTailDomainAfter = final at trace
  cases trace with
  | rootFree root free =>
      rw [show familyConsPositivityGroups[0]? =
        some familyConsRootPositivityGroup by rfl] at root
      cases root
      have mentioned :
          exprMentionsAnyAddr familyConsTailDomain
            familyConsRootPositivityGroup.addrs = true := by
        simpa [familyConsRootPositivityGroup] using
          familyConsTailDomainMentionsRoot
      rw [mentioned] at free
      contradiction
  | «forall» root mentioned whnf domainFree opening tail restored =>
      rw [familyConsTailDomainWhnfRun] at whnf
      injection whnf with resultEq stateEq
      have terminal := familyConsTailDomainWhnfNotForall
      rw [resultEq] at terminal
      exact terminal.elim
  | application root mentioned whnf notForall spine active valid =>
      cases hfinal
      exact .application (fuel := fuel) root mentioned whnf notForall spine
        active valid

theorem indexedVecProductionNatConstructorPositivityTraceAt (fuel : Nat) :
    Nonempty (Lean4Lean.AddInductive.ConstructorPositivityTrace
      indexedVecConstructorStats indexedVecKernelCons.name 1
      indexedVecConstructorContext (.const ``Nat []) (fuel + 1)) :=
  FlatPositivityTraceTransport.constructorPositivityTrace
    indexedVecProductionFlatPositivityTransport
      (indexedVecProductionNatFlatPositivityTraceAt fuel) rfl
        ProductionIndexedPositivitySourceRel.nat

theorem indexedVecProductionHeadConstructorPositivityTraceAt (fuel : Nat) :
    Nonempty (Lean4Lean.AddInductive.ConstructorPositivityTrace
      indexedVecConstructorStats indexedVecKernelCons.name 2
      indexedVecConstructorNContext indexedVecConstructorAlpha (fuel + 1)) :=
  FlatPositivityTraceTransport.constructorPositivityTrace
    indexedVecProductionFlatPositivityTransport
      (indexedVecProductionHeadFlatPositivityTraceAt fuel) rfl
        ProductionIndexedPositivitySourceRel.head

theorem indexedVecProductionTailConstructorPositivityTraceAt (fuel : Nat) :
    Nonempty (Lean4Lean.AddInductive.ConstructorPositivityTrace
      indexedVecConstructorStats indexedVecKernelCons.name 3
      indexedVecConstructorHeadContext
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr) (fuel + 1)) :=
  FlatPositivityTraceTransport.constructorPositivityTrace
    indexedVecProductionFlatPositivityTransport
      (indexedVecProductionTailFlatPositivityTraceAt fuel) rfl
        ProductionIndexedPositivitySourceRel.tail

end Ix.Tc.IndexedRecursiveFixture
