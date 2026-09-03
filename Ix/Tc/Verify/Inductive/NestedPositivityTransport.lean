import Ix.Tc.Verify.Inductive.NestedCandidateSyntax

/-!
# Transporting the concrete nested positivity branch

This module instantiates `FlattenedPositivityTraceTransport` for the outer
`Tree.node : Box Tree → Tree` field.  Ix validates the pre-flattening
`Box Tree` application by recursively traversing `Box.wrap`; Lean4Lean
validates the post-flattening generated auxiliary as a direct member of the
two-family mutual block.

The result relation is intentionally restricted to this exact WHNF node.  Its
nested field recovers the canonical production auxiliary request from the
complete branch trace and then consumes the audited cross-representation
target certificate from `NestedCandidateSyntax`.
-/

namespace Ix.Tc.NestedRecursiveFixture

/-! ## Exact candidate WHNF -/

private theorem leanAuxiliaryCandidateWhnfNative :
    ExactLeanSyntax.exceptExprCheck
      (Lean4Lean.TypeChecker.M.run leanFlatConstructorContext.env
        leanFlatConstructorContext.safety leanFlatConstructorContext.lctx
        leanFlatConstructorContext.lparams leanFlatConstructorContext.fuel
        (Lean4Lean.TypeChecker.whnf leanAuxiliaryExpr))
      leanAuxiliaryExpr = true := by
  native_decide

theorem leanAuxiliaryCandidateWhnf :
    Lean4Lean.AddInductive.CandidateWhnfStep.Valid
      ⟨leanFlatConstructorContext, leanAuxiliaryExpr,
        leanAuxiliaryExpr⟩ := by
  unfold Lean4Lean.AddInductive.CandidateWhnfStep.Valid
  exact ExactLeanSyntax.exceptExpr_eq_ok_of_check
    leanAuxiliaryCandidateWhnfNative

private theorem nestedDomainMentionsRootNative :
    exprMentionsAnyAddr nestedDomain #[treeId.addr] = true := by
  native_decide

private theorem nestedExternalInactiveNative :
    #[treeId.addr].contains boxId.addr = false := by
  native_decide

private theorem nestedResultSpineNative :
    nestedDomain.collectSpine =
      (.const boxId #[] (KExpr.mkConst boxId #[] ()).info, #[treeExpr]) := by
  rfl

/-! ## Exact operation relations -/

inductive NestedOuterPositivitySourceRel :
    TcState .anon → Lean4Lean.AddInductive.Context →
      KExpr .anon → Lean.Expr → Prop
  | domain : NestedOuterPositivitySourceRel checkerInitial
      leanFlatConstructorContext nestedDomain leanAuxiliaryExpr

/-- The Ix WHNF node still spells the external application.  The Lean node
is the fresh auxiliary produced for that exact application.  The explicit
shape equality makes impossible result forms eliminable without assuming an
injective address/content correspondence. -/
inductive NestedOuterPositivityResultRel :
    TcState .anon → Lean4Lean.AddInductive.Context →
      KExpr .anon → Lean.Expr → Prop
  | domain {ixResult : KExpr .anon}
      (shape : ixResult = nestedDomain) :
      NestedOuterPositivityResultRel nestedWhnfAfter
        leanFlatConstructorContext ixResult leanAuxiliaryExpr

private theorem nestedOuterRootFree
    {ixState : TcState .anon}
    {leanContext : Lean4Lean.AddInductive.Context}
    {ixSource : KExpr .anon} {leanSource : Lean.Expr}
    (relation : NestedOuterPositivitySourceRel ixState leanContext ixSource
      leanSource)
    (free : exprMentionsAnyAddr ixSource #[treeId.addr] = false) :
    ∃ leanResult,
      Lean4Lean.AddInductive.CandidateWhnfStep.Valid
        ⟨leanContext, leanSource, leanResult⟩ ∧
      Lean4Lean.AddInductive.hasIndOcc leanFlatStats.indConsts leanResult =
        false := by
  cases relation
  rw [nestedDomainMentionsRootNative] at free
  contradiction

private theorem nestedOuterWhnf
    {ixBefore ixAfter : TcState .anon}
    {leanContext : Lean4Lean.AddInductive.Context}
    {ixSource ixResult : KExpr .anon} {leanSource : Lean.Expr}
    (relation : NestedOuterPositivitySourceRel ixBefore leanContext ixSource
      leanSource)
    (_mentioned : exprMentionsAnyAddr ixSource #[treeId.addr] = true)
    (run : (RecM.whnf ixSource).run checkerMethods ixBefore =
      .ok ixResult ixAfter) :
    ∃ leanResult,
      Lean4Lean.AddInductive.CandidateWhnfStep.Valid
        ⟨leanContext, leanSource, leanResult⟩ ∧
      NestedOuterPositivityResultRel ixAfter leanContext ixResult
        leanResult := by
  cases relation
  rw [nestedWhnfRun] at run
  cases run
  exact ⟨leanAuxiliaryExpr, leanAuxiliaryCandidateWhnf,
    .domain nestedWhnfResult_eq⟩

private theorem nestedOuterMentions
    (relation : NestedOuterPositivitySourceRel ixState leanContext ixExpr
      leanExpr) :
    exprMentionsAnyAddr ixExpr #[treeId.addr] =
      Lean4Lean.AddInductive.hasIndOcc leanFlatStats.indConsts leanExpr := by
  cases relation
  rw [nestedDomainMentionsRootNative, leanAuxiliaryOccurs]

private theorem nestedOuterForall
    {ixState : TcState .anon}
    {leanContext : Lean4Lean.AddInductive.Context}
    {ixName : Mode.anon.F Name} {ixBinder : Mode.anon.F Lean.BinderInfo}
    {ixDomain ixBody : KExpr .anon} {ixInfo : ExprInfo .anon}
    {leanExpr : Lean.Expr}
    (relation : NestedOuterPositivityResultRel ixState leanContext
      (.all ixName ixBinder ixDomain ixBody ixInfo) leanExpr) :
    ∃ leanName leanBinder leanDomain leanBody,
      leanExpr = .forallE leanName leanDomain leanBody leanBinder ∧
      NestedOuterPositivitySourceRel ixState leanContext ixDomain
        leanDomain ∧
      ∀ {ixOpen : KExpr .anon} {ixFVar : FVarId}
          {ixAfterOpen : TcState .anon},
        TcM.openBinderAnon ixDomain ixBody ixState =
          .ok (ixOpen, ixFVar) ixAfterOpen →
        NestedOuterPositivitySourceRel ixAfterOpen
          (leanContext.pushLocalDecl leanName leanBinder
            (Lean4Lean.AddInductive.consumeTypeAnnotations leanDomain))
          ixOpen (leanBody.instantiate1 leanContext.freshExpr) := by
  cases relation with
  | domain shape => cases shape

/-- Any complete nested trace at the fixed `Box Tree` WHNF node produces the
same canonical request, independently of fuel, active-stack suffix, or final
cache state.  This is the bridge used by the transport's nested branch rather
than silently substituting the fixture's separately named trace proof. -/
theorem nestedTraceProducesCanonicalRequest
    (trace : CompleteNestedPositivityApplicationTrace fuel boxId #[]
      #[treeExpr] traceGroups #[treeId.addr] traceActive checkerMethods
        nestedWhnfAfter traceFinal) :
    positivityRequest.ProducedBy fuel boxId #[] #[treeExpr] traceGroups
      #[treeId.addr] traceActive checkerMethods nestedWhnfAfter traceFinal := by
  rcases trace.producedRequest with ⟨request, produced⟩
  rcases produced with
    ⟨requestId, requestUniverses, requestArguments, concrete, afterLookup,
      lookup, header, argumentsSize, universesSize, branch⟩
  rw [requestId, boxLookupRun] at lookup
  cases lookup
  rw [boxLookupConcrete_eq] at header
  have canonicalHeader := boxConcreteHeader
  have requestHeader :
      request.nParams = 1 ∧ request.nIndices = 0 ∧ request.levels = 0 ∧
        request.block = boxBlockId ∧ request.ctors = #[wrapId] := by
    generalize hconcrete : boxConcrete = loaded at header canonicalHeader
    cases loaded <;>
      simp_all [KConst.NestedPositiveHeader]
  have requestEq : request = positivityRequest := by
    cases request
    simp_all [positivityRequest]
  cases requestEq
  have canonicalLookup :
      TcM.getConst boxId nestedWhnfAfter =
        .ok boxConcrete boxLookupAfter := by
    rw [boxLookupRun, boxLookupConcrete_eq]
  exact ⟨requestId, requestUniverses, requestArguments, boxConcrete,
    boxLookupAfter, by simpa [positivityRequest] using canonicalLookup, header,
    argumentsSize, universesSize, branch⟩

private theorem nestedOuterDirect
    {ixState : TcState .anon}
    {leanContext : Lean4Lean.AddInductive.Context}
    {ixResult : KExpr .anon} {leanResult : Lean.Expr}
    {id : KId .anon} {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)}
    {traceGroups : Array (PositivityGroup .anon)}
    {final : TcState .anon}
    (relation : NestedOuterPositivityResultRel ixState leanContext ixResult
      leanResult)
    (spine : ixResult.collectSpine = (.const id us info, args))
    (active : #[treeId.addr].contains id.addr = true)
    (_valid : ValidPositiveRecursiveApplication id us args traceGroups
      #[treeId.addr] checkerMethods ixState final) :
    ∃ targetIdx,
      Lean4Lean.AddInductive.hasIndOcc leanFlatStats.indConsts leanResult =
          true ∧
        leanResult.isForall = false ∧
        Lean4Lean.AddInductive.isValidIndApp? leanFlatStats leanResult =
          some targetIdx := by
  cases relation with
  | domain shape =>
      rw [shape, nestedResultSpineNative] at spine
      cases spine
      rw [nestedExternalInactiveNative] at active
      contradiction

private theorem nestedOuterNested
    {fuel : Nat} {ixState : TcState .anon}
    {leanContext : Lean4Lean.AddInductive.Context}
    {ixResult : KExpr .anon} {leanResult : Lean.Expr}
    {id : KId .anon} {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)}
    {traceGroups : Array (PositivityGroup .anon)}
    {traceActive : Array Address} {final : TcState .anon}
    (relation : NestedOuterPositivityResultRel ixState leanContext ixResult
      leanResult)
    (spine : ixResult.collectSpine = (.const id us info, args))
    (_inactive : #[treeId.addr].contains id.addr = false)
    (trace : CompleteNestedPositivityApplicationTrace fuel id us args
      traceGroups #[treeId.addr] traceActive checkerMethods ixState final) :
    ∃ targetIdx,
      Lean4Lean.AddInductive.hasIndOcc leanFlatStats.indConsts leanResult =
          true ∧
        leanResult.isForall = false ∧
        Lean4Lean.AddInductive.isValidIndApp? leanFlatStats leanResult =
          some targetIdx := by
  cases relation with
  | domain shape =>
      rw [shape, nestedResultSpineNative] at spine
      cases spine
      have produced := nestedTraceProducesCanonicalRequest trace
      have target := nestedAuxiliaryCandidateTarget
      exact ⟨1, target.occurs, rfl, target.valid⟩

/-- Complete operation-shaped transport for the outer nested field.  The
`nested` field is discharged from the exact producer request/flat target
certificate; it is not a preconstructed Lean4Lean trace. -/
theorem nestedOuterPositivityTransport :
    FlattenedPositivityTraceTransport leanFlatStats #[treeId.addr]
      checkerMethods NestedOuterPositivitySourceRel
        NestedOuterPositivityResultRel where
  rootFree := nestedOuterRootFree
  whnf := nestedOuterWhnf
  mentions := nestedOuterMentions
  forallE := nestedOuterForall
  direct := nestedOuterDirect
  nested := nestedOuterNested

/-! ## Retained outer positivity trace -/

def nestedOuterProductionTrace : PositivityDomainTrace groups
    #[treeId.addr] checkerMethods positivityFuel nestedDomain checkerInitial
      positivityAfter :=
  RecM.checkPositivityDomainFuel_success checkerMethods positivityRun

/-- The actual nested production execution constructs the exact retained
Lean4Lean positivity trace for the flattened outer constructor field. -/
theorem nestedOuterConstructorPositivityTrace :
    Nonempty (Lean4Lean.AddInductive.ConstructorPositivityTrace leanFlatStats
      leanFlatNode.name 0 leanFlatConstructorContext leanAuxiliaryExpr
        positivityFuel) := by
  exact FlattenedPositivityTraceTransport.constructorPositivityTrace
    nestedOuterPositivityTransport nestedOuterProductionTrace (by rfl)
      .domain

end Ix.Tc.NestedRecursiveFixture
