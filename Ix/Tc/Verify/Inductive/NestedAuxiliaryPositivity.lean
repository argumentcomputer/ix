import Ix.Tc.Verify.Inductive.NestedPositivityTransport

/-!
# Positivity of a generated nested auxiliary

The outer `Tree.node` field is checked by Ix as the nested application
`Box Tree`, while Lean4Lean rewrites that application to a generated flat
family.  This module follows the other half of that transformation: the
production nested traversal copies `Box.wrap`, strips its `Box` parameter,
substitutes `Tree`, and checks the resulting `Tree` field.  The retained
execution is transported to the direct recursive field of Lean4Lean's copied
auxiliary constructor.
-/

namespace Ix.Tc.NestedRecursiveFixture

local instance auxiliaryAddressDecidableEq : DecidableEq Address :=
  AnonStructural.addressDecidableEq

local instance auxiliaryKIdDecidableEq : DecidableEq (KId .anon) :=
  AnonStructural.idDecidableEq

local instance auxiliaryKExprDecidableEq : DecidableEq (KExpr .anon) :=
  AnonStructural.exprDecidableEq

local instance auxiliaryKConstDecidableEq : DecidableEq (KConst .anon) :=
  AnonStructural.constDecidableEq

private def nestedConstructorType (concrete : KConst .anon) : KExpr .anon :=
  match concrete with
  | .ctor (ty := loadedTy) .. => loadedTy
  | _ => default

private theorem nestedConstructorHeader_type_eq
    {concrete : KConst .anon} {ctorTy : KExpr .anon}
    (header : concrete.NestedConstructorHeader ctorTy) :
    nestedConstructorType concrete = ctorTy := by
  unfold KConst.NestedConstructorHeader at header
  cases concrete with
  | defn => change False at header; contradiction
  | recr => change False at header; contradiction
  | axio => change False at header; contradiction
  | quot => change False at header; contradiction
  | indc => change False at header; contradiction
  | ctor => simpa [nestedConstructorType] using header

/-! ## Exact production preparation of the copied constructor -/

private def auxiliaryDiscoveryOutcome :=
  (RecM.discoverBlockInductives boxBlockId).run checkerMethods boxLookupAfter

private def auxiliaryDiscovered : Array (KId .anon) :=
  match auxiliaryDiscoveryOutcome with
  | .ok ids _ => ids
  | .error _ _ => #[]

private def auxiliaryDiscoveryAfter : TcState .anon :=
  match auxiliaryDiscoveryOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem auxiliaryDiscoverySucceededNative :
    (match auxiliaryDiscoveryOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

private theorem auxiliaryDiscoveryRun :
    (RecM.discoverBlockInductives boxBlockId).run checkerMethods boxLookupAfter =
      .ok auxiliaryDiscovered auxiliaryDiscoveryAfter := by
  have success := auxiliaryDiscoverySucceededNative
  unfold auxiliaryDiscovered auxiliaryDiscoveryAfter
  generalize houtcome : auxiliaryDiscoveryOutcome = outcome at success ⊢
  cases outcome <;> simp_all [auxiliaryDiscoveryOutcome]

private def auxiliaryWrapLookupOutcome :=
  TcM.getConst wrapId auxiliaryDiscoveryAfter

private def auxiliaryWrapConcrete : KConst .anon :=
  match auxiliaryWrapLookupOutcome with
  | .ok concrete _ => concrete
  | .error _ _ => default

private def auxiliaryWrapLookupAfter : TcState .anon :=
  match auxiliaryWrapLookupOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem auxiliaryWrapLookupSucceededNative :
    (match auxiliaryWrapLookupOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

private theorem auxiliaryWrapLookupRun :
    TcM.getConst wrapId auxiliaryDiscoveryAfter =
      .ok auxiliaryWrapConcrete auxiliaryWrapLookupAfter := by
  have success := auxiliaryWrapLookupSucceededNative
  unfold auxiliaryWrapConcrete auxiliaryWrapLookupAfter
  generalize houtcome : auxiliaryWrapLookupOutcome = outcome at success ⊢
  cases outcome <;> simp_all [auxiliaryWrapLookupOutcome]

private def auxiliaryWrapType : KExpr .anon :=
  nestedConstructorType auxiliaryWrapConcrete

private def auxiliaryInstantiationOutcome :=
  TcM.instantiateUnivParams auxiliaryWrapType #[] auxiliaryWrapLookupAfter

private def auxiliaryInstantiated : KExpr .anon :=
  match auxiliaryInstantiationOutcome with
  | .ok ty _ => ty
  | .error _ _ => default

private def auxiliaryInstantiationAfter : TcState .anon :=
  match auxiliaryInstantiationOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem auxiliaryInstantiationSucceededNative :
    (match auxiliaryInstantiationOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

private theorem auxiliaryInstantiationRun :
    TcM.instantiateUnivParams auxiliaryWrapType #[] auxiliaryWrapLookupAfter =
      .ok auxiliaryInstantiated auxiliaryInstantiationAfter := by
  have success := auxiliaryInstantiationSucceededNative
  unfold auxiliaryInstantiated auxiliaryInstantiationAfter
  generalize houtcome : auxiliaryInstantiationOutcome = outcome at success ⊢
  cases outcome <;> simp_all [auxiliaryInstantiationOutcome]

private def auxiliaryStrippingOutcome :=
  (RecM.stripNestedCtorParameters auxiliaryInstantiated 1).run checkerMethods
    auxiliaryInstantiationAfter

private def auxiliaryStripped : KExpr .anon :=
  match auxiliaryStrippingOutcome with
  | .ok ty _ => ty
  | .error _ _ => default

private def auxiliaryStrippingAfter : TcState .anon :=
  match auxiliaryStrippingOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem auxiliaryStrippingSucceededNative :
    (match auxiliaryStrippingOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

private theorem auxiliaryStrippingRun :
    (RecM.stripNestedCtorParameters auxiliaryInstantiated 1).run checkerMethods
        auxiliaryInstantiationAfter =
      .ok auxiliaryStripped auxiliaryStrippingAfter := by
  have success := auxiliaryStrippingSucceededNative
  unfold auxiliaryStripped auxiliaryStrippingAfter
  generalize houtcome : auxiliaryStrippingOutcome = outcome at success ⊢
  cases outcome <;> simp_all [auxiliaryStrippingOutcome]

private def auxiliarySubstitutionOutcome :=
  TcM.runIntern (simulSubst auxiliaryStripped #[treeExpr].reverse 0)
    auxiliaryStrippingAfter

private def auxiliarySubstituted : KExpr .anon :=
  match auxiliarySubstitutionOutcome with
  | .ok ty _ => ty
  | .error _ _ => default

private def auxiliarySubstitutionAfter : TcState .anon :=
  match auxiliarySubstitutionOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem auxiliarySubstitutionSucceededNative :
    (match auxiliarySubstitutionOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

private theorem auxiliarySubstitutionRun :
    TcM.runIntern (simulSubst auxiliaryStripped #[treeExpr].reverse 0)
        auxiliaryStrippingAfter =
      .ok auxiliarySubstituted auxiliarySubstitutionAfter := by
  have success := auxiliarySubstitutionSucceededNative
  unfold auxiliarySubstituted auxiliarySubstitutionAfter
  generalize houtcome : auxiliarySubstitutionOutcome = outcome at success ⊢
  cases outcome <;> simp_all [auxiliarySubstitutionOutcome]

private def auxiliaryFieldWhnfOutcome :=
  (RecM.whnf auxiliarySubstituted).run checkerMethods
    auxiliarySubstitutionAfter

private def auxiliaryFieldWhnfResult : KExpr .anon :=
  match auxiliaryFieldWhnfOutcome with
  | .ok result _ => result
  | .error _ _ => default

private def auxiliaryFieldWhnfAfter : TcState .anon :=
  match auxiliaryFieldWhnfOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem auxiliaryFieldWhnfSucceededNative :
    (match auxiliaryFieldWhnfOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

private theorem auxiliaryFieldWhnfRun :
    (RecM.whnf auxiliarySubstituted).run checkerMethods
        auxiliarySubstitutionAfter =
      .ok auxiliaryFieldWhnfResult auxiliaryFieldWhnfAfter := by
  have success := auxiliaryFieldWhnfSucceededNative
  unfold auxiliaryFieldWhnfResult auxiliaryFieldWhnfAfter
  generalize houtcome : auxiliaryFieldWhnfOutcome = outcome at success ⊢
  cases outcome <;> simp_all [auxiliaryFieldWhnfOutcome]

private def auxiliaryFieldName : Mode.anon.F Name :=
  match auxiliaryFieldWhnfResult with
  | .all name .. => name
  | _ => ()

private def auxiliaryFieldBinder : Mode.anon.F Lean.BinderInfo :=
  match auxiliaryFieldWhnfResult with
  | .all _ binder .. => binder
  | _ => ()

private def auxiliaryFieldBody : KExpr .anon :=
  match auxiliaryFieldWhnfResult with
  | .all _ _ _ body _ => body
  | _ => default

private def auxiliaryFieldInfo : ExprInfo .anon :=
  match auxiliaryFieldWhnfResult with
  | .all _ _ _ _ info => info
  | _ => treeExpr.info

private theorem auxiliaryFieldWhnfShapeNative :
    auxiliaryFieldWhnfResult =
      .all auxiliaryFieldName auxiliaryFieldBinder treeExpr
        auxiliaryFieldBody auxiliaryFieldInfo := by
  native_decide

/-! The recursive field itself starts from the state produced by the
constructor-telescope WHNF above. -/

private def auxiliaryDomainWhnfOutcome :=
  (RecM.whnf treeExpr).run checkerMethods auxiliaryFieldWhnfAfter

private def auxiliaryDomainWhnfResult : KExpr .anon :=
  match auxiliaryDomainWhnfOutcome with
  | .ok result _ => result
  | .error _ _ => default

private def auxiliaryDomainWhnfAfter : TcState .anon :=
  match auxiliaryDomainWhnfOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem auxiliaryDomainWhnfSucceededNative :
    (match auxiliaryDomainWhnfOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

private theorem auxiliaryDomainWhnfRun :
    (RecM.whnf treeExpr).run checkerMethods auxiliaryFieldWhnfAfter =
      .ok auxiliaryDomainWhnfResult auxiliaryDomainWhnfAfter := by
  have success := auxiliaryDomainWhnfSucceededNative
  unfold auxiliaryDomainWhnfResult auxiliaryDomainWhnfAfter
  generalize houtcome : auxiliaryDomainWhnfOutcome = outcome at success ⊢
  cases outcome <;> simp_all [auxiliaryDomainWhnfOutcome]

private theorem auxiliaryDomainWhnfResultNative :
    auxiliaryDomainWhnfResult = treeExpr := by
  native_decide

private theorem auxiliaryTreeMentionsRootNative :
    exprMentionsAnyAddr treeExpr #[treeId.addr] = true := by
  native_decide

private theorem auxiliaryTreeActiveNative :
    #[treeId.addr].contains treeId.addr = true := by
  native_decide

private theorem auxiliaryDomainWhnfSpine :
    auxiliaryDomainWhnfResult.collectSpine =
      (.const treeId #[] treeExpr.info, #[]) := by
  rw [auxiliaryDomainWhnfResultNative]
  rfl

private theorem auxiliaryDomainWhnfNotForallNative :
    (match auxiliaryDomainWhnfResult with
      | .all .. => false
      | _ => true) = true := by
  native_decide

private theorem auxiliaryDomainWhnfNotForall :
    PositivityTerminalForm auxiliaryDomainWhnfResult := by
  have terminal := auxiliaryDomainWhnfNotForallNative
  generalize hresult : auxiliaryDomainWhnfResult = result at terminal ⊢
  cases result <;> simp_all [PositivityTerminalForm]

private theorem auxiliaryParameterArgsNative :
    positivityRequest.arguments.extract 0
      (min positivityRequest.nParams positivityRequest.arguments.size) =
        #[treeExpr] := by
  native_decide

/-! ## Retained inner production trace -/

set_option maxRecDepth 100000 in
/-- The successful fresh-specialization branch contains the copied
`Box.wrap` field check, at the exact decremented fuel used by production.
This theorem is extracted from `positivityRequestFreshExpansion`; it is not a
second, independently executed positivity fixture. -/
theorem nestedAuxiliaryFieldProductionTrace :
    ∃ innerGroups innerActive final,
      innerGroups[0]?.map (·.addrs) = some #[treeId.addr] ∧
      FlatPositivityDomainTrace innerGroups innerActive checkerMethods
        (positivityFuel - 3) treeExpr auxiliaryFieldWhnfAfter final := by
  rcases positivityRequestFreshExpansion with
    ⟨concrete, afterLookup, lookup, _header, fresh⟩
  change TcM.getConst boxId nestedWhnfAfter =
    .ok concrete afterLookup at lookup
  rw [boxLookupRun] at lookup
  cases lookup
  rcases fresh with
    ⟨extBlockInductives, afterDiscovery, discovery, constructors⟩
  change (RecM.discoverBlockInductives boxBlockId).run checkerMethods
    boxLookupAfter = .ok extBlockInductives afterDiscovery at discovery
  rw [auxiliaryDiscoveryRun] at discovery
  cases discovery
  rw [auxiliaryParameterArgsNative] at constructors
  simp only [positivityRequest] at constructors
  cases constructors with
  | cons head tail =>
      cases tail
      rcases head with
        ⟨innerFuel, ctorConcrete, ctorTy, afterCtorLookup, fuelEq,
          ctorLookup, ctorHeader, fields⟩
      have innerFuelEq : innerFuel = positivityFuel - 2 := by
        simp [positivityFuel] at fuelEq ⊢
        omega
      subst innerFuel
      rw [auxiliaryWrapLookupRun] at ctorLookup
      cases ctorLookup
      have ctorTyEq : ctorTy = auxiliaryWrapType := by
        exact (nestedConstructorHeader_type_eq ctorHeader).symm
      subst ctorTy
      cases fields with
      | complete instantiation stripping stripTrace substitution fieldLoop
          fieldTrace =>
          rw [auxiliaryInstantiationRun] at instantiation
          cases instantiation
          rw [auxiliaryStrippingRun] at stripping
          cases stripping
          rw [auxiliarySubstitutionRun] at substitution
          cases substitution
          cases fieldTrace with
          | terminal whnfRun notForall =>
              rw [auxiliaryFieldWhnfRun] at whnfRun
              injection whnfRun with resultEq _stateEq
              have wEq := resultEq.symm.trans
                auxiliaryFieldWhnfShapeNative
              cases wEq
              exact notForall.elim
          | @«forall» fuel ty name bi dom body openBody info fv initial
              afterWhnf afterDomain afterOpen afterRecursive final whnfRun
              domainRun opening nestedTail restored =>
              rw [auxiliaryFieldWhnfRun] at whnfRun
              injection whnfRun with resultEq _stateEq
              have allEq := auxiliaryFieldWhnfShapeNative.symm.trans resultEq
              cases allEq
              rw [← _stateEq] at domainRun
              let innerGroups := groups.push
                { addrs := auxiliaryDiscovered.map (·.addr)
                  params := #[treeExpr]
                  concreteUs := some #[] }
              let innerActive :=
                #[treeId.addr] ++ auxiliaryDiscovered.map (·.addr)
              have valid : ValidPositiveRecursiveApplication treeId #[] #[]
                  innerGroups #[treeId.addr] checkerMethods
                    auxiliaryDomainWhnfAfter afterDomain := by
                apply RecM.checkPositivityDomainFuel_direct_valid
                  (fuel := positivityFuel - 4)
                  (dom := treeExpr) (w := auxiliaryDomainWhnfResult)
                  (activeAddrs := innerActive) (rootGroup := rootGroup)
                  (info := treeExpr.info)
                · simp [innerGroups, groups]
                · simpa [rootGroup] using auxiliaryTreeMentionsRootNative
                · exact auxiliaryDomainWhnfRun
                · exact auxiliaryDomainWhnfSpine
                · simp [rootGroup]
                · simpa [innerGroups, innerActive, positivityFuel] using
                    domainRun
              refine ⟨innerGroups, innerActive, afterDomain, ?_, ?_⟩
              · simp [innerGroups, groups, rootGroup]
              · simpa [positivityFuel] using
                  (FlatPositivityDomainTrace.application
                    (fuel := positivityFuel - 4)
                    (source := treeExpr) (w := auxiliaryDomainWhnfResult)
                    (id := treeId) (us := #[]) (info := treeExpr.info)
                    (args := #[]) (rootGroup := rootGroup)
                    (initial := auxiliaryFieldWhnfAfter)
                    (afterWhnf := auxiliaryDomainWhnfAfter)
                    (final := afterDomain)
                    (groups := innerGroups) (activeAddrs := innerActive)
                    (methods := checkerMethods)
                    (by simp [innerGroups, groups])
                    (by simpa [rootGroup] using
                      auxiliaryTreeMentionsRootNative)
                    auxiliaryDomainWhnfRun auxiliaryDomainWhnfNotForall
                    auxiliaryDomainWhnfSpine
                    (by simp [rootGroup])
                    valid)

/-! ## Transport of the copied recursive field -/

private theorem leanTreeCandidateWhnfNative :
    ExactLeanSyntax.exceptExprCheck
      (Lean4Lean.TypeChecker.M.run leanFlatConstructorContext.env
        leanFlatConstructorContext.safety leanFlatConstructorContext.lctx
        leanFlatConstructorContext.lparams leanFlatConstructorContext.fuel
        (Lean4Lean.TypeChecker.whnf leanTreeExpr))
      leanTreeExpr = true := by
  native_decide

theorem leanTreeCandidateWhnf :
    Lean4Lean.AddInductive.CandidateWhnfStep.Valid
      ⟨leanFlatConstructorContext, leanTreeExpr, leanTreeExpr⟩ := by
  unfold Lean4Lean.AddInductive.CandidateWhnfStep.Valid
  exact ExactLeanSyntax.exceptExpr_eq_ok_of_check
    leanTreeCandidateWhnfNative

/-- The one source operation reached inside the copied `Box.wrap`
constructor.  Its state is the state selected by production after reducing
the copied constructor telescope, rather than a separately initialized
fixture state. -/
inductive NestedAuxiliaryPositivitySourceRel :
    TcState .anon → Lean4Lean.AddInductive.Context →
      KExpr .anon → Lean.Expr → Prop
  | domain : NestedAuxiliaryPositivitySourceRel auxiliaryFieldWhnfAfter
      leanFlatConstructorContext treeExpr leanTreeExpr

/-- Exact post-WHNF syntax relation for the recursive `Tree` field. -/
inductive NestedAuxiliaryPositivityResultRel :
    TcState .anon → Lean4Lean.AddInductive.Context →
      KExpr .anon → Lean.Expr → Prop
  | domain {ixResult : KExpr .anon}
      (candidate : CandidateSyntaxRel nestedCandidateNameOf
        (fun ixId leanId => nestedClosedFVarMatches ixId leanId = true)
        (fun ixLevel leanLevel =>
          CandidateSyntax.levelMatches [] ixLevel leanLevel = true)
        ixResult leanTreeExpr) :
      NestedAuxiliaryPositivityResultRel auxiliaryDomainWhnfAfter
        leanFlatConstructorContext ixResult leanTreeExpr

private theorem nestedAuxiliaryRootFree
    {ixState : TcState .anon}
    {leanContext : Lean4Lean.AddInductive.Context}
    {ixSource : KExpr .anon} {leanSource : Lean.Expr}
    (relation : NestedAuxiliaryPositivitySourceRel ixState leanContext
      ixSource leanSource)
    (free : exprMentionsAnyAddr ixSource #[treeId.addr] = false) :
    ∃ leanResult,
      Lean4Lean.AddInductive.CandidateWhnfStep.Valid
        ⟨leanContext, leanSource, leanResult⟩ ∧
      Lean4Lean.AddInductive.hasIndOcc leanFlatStats.indConsts leanResult =
        false := by
  cases relation
  rw [auxiliaryTreeMentionsRootNative] at free
  contradiction

set_option maxRecDepth 100000 in
private theorem nestedAuxiliaryWhnf
    {ixBefore ixAfter : TcState .anon}
    {leanContext : Lean4Lean.AddInductive.Context}
    {ixSource ixResult : KExpr .anon} {leanSource : Lean.Expr}
    (relation : NestedAuxiliaryPositivitySourceRel ixBefore leanContext
      ixSource leanSource)
    (_mentioned : exprMentionsAnyAddr ixSource #[treeId.addr] = true)
    (run : (RecM.whnf ixSource).run checkerMethods ixBefore =
      .ok ixResult ixAfter) :
    ∃ leanResult,
      Lean4Lean.AddInductive.CandidateWhnfStep.Valid
        ⟨leanContext, leanSource, leanResult⟩ ∧
      NestedAuxiliaryPositivityResultRel ixAfter leanContext ixResult
        leanResult := by
  cases relation
  rw [auxiliaryDomainWhnfRun] at run
  cases run
  refine ⟨leanTreeExpr, leanTreeCandidateWhnf, .domain ?_⟩
  rw [auxiliaryDomainWhnfResultNative]
  exact treeCandidateSyntax

private theorem nestedAuxiliaryMentions
    (relation : NestedAuxiliaryPositivitySourceRel ixState leanContext ixExpr
      leanExpr) :
    exprMentionsAnyAddr ixExpr #[treeId.addr] =
      Lean4Lean.AddInductive.hasIndOcc leanFlatStats.indConsts leanExpr := by
  cases relation
  rw [auxiliaryTreeMentionsRootNative, leanTreeOccurs]

private theorem nestedAuxiliaryForall
    {ixState : TcState .anon}
    {leanContext : Lean4Lean.AddInductive.Context}
    {ixName : Mode.anon.F Name} {ixBinder : Mode.anon.F Lean.BinderInfo}
    {ixDomain ixBody : KExpr .anon} {ixInfo : ExprInfo .anon}
    {leanExpr : Lean.Expr}
    (relation : NestedAuxiliaryPositivityResultRel ixState leanContext
      (.all ixName ixBinder ixDomain ixBody ixInfo) leanExpr) :
    ∃ leanName leanBinder leanDomain leanBody,
      leanExpr = .forallE leanName leanDomain leanBody leanBinder ∧
      NestedAuxiliaryPositivitySourceRel ixState leanContext ixDomain
        leanDomain ∧
      ∀ {ixOpen : KExpr .anon} {ixFVar : FVarId}
          {ixAfterOpen : TcState .anon},
        TcM.openBinderAnon ixDomain ixBody ixState =
          .ok (ixOpen, ixFVar) ixAfterOpen →
        NestedAuxiliaryPositivitySourceRel ixAfterOpen
          (leanContext.pushLocalDecl leanName leanBinder
            (Lean4Lean.AddInductive.consumeTypeAnnotations leanDomain))
          ixOpen (leanBody.instantiate1 leanContext.freshExpr) := by
  cases relation with
  | domain candidate => cases candidate

private theorem nestedAuxiliaryDirect
    {ixState : TcState .anon}
    {leanContext : Lean4Lean.AddInductive.Context}
    {ixResult : KExpr .anon} {leanResult : Lean.Expr}
    {id : KId .anon} {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)}
    {traceGroups : Array (PositivityGroup .anon)}
    {final : TcState .anon}
    (relation : NestedAuxiliaryPositivityResultRel ixState leanContext
      ixResult leanResult)
    (_spine : ixResult.collectSpine = (.const id us info, args))
    (_active : #[treeId.addr].contains id.addr = true)
    (_valid : ValidPositiveRecursiveApplication id us args traceGroups
      #[treeId.addr] checkerMethods ixState final) :
    ∃ targetIdx,
      Lean4Lean.AddInductive.hasIndOcc leanFlatStats.indConsts leanResult =
          true ∧
        leanResult.isForall = false ∧
        Lean4Lean.AddInductive.isValidIndApp? leanFlatStats leanResult =
          some targetIdx := by
  cases relation
  exact ⟨0, leanTreeOccurs, rfl, leanTreeTarget⟩

/-- Operation-shaped cross-kernel transport for the recursive field of the
generated auxiliary constructor. -/
theorem nestedAuxiliaryPositivityTransport :
    FlatPositivityTraceTransport leanFlatStats #[treeId.addr]
      checkerMethods NestedAuxiliaryPositivitySourceRel
        NestedAuxiliaryPositivityResultRel where
  rootFree := nestedAuxiliaryRootFree
  whnf := nestedAuxiliaryWhnf
  mentions := nestedAuxiliaryMentions
  forallE := nestedAuxiliaryForall
  direct := nestedAuxiliaryDirect

set_option maxRecDepth 100000 in
/-- Reindex the retained copied-field execution at any positive field fuel.
This is sound only after inspecting the production-derived trace and proving
that its concrete branch is the direct application branch: unlike forall and
nested recursion, that branch does not consume its predecessor fuel. -/
theorem nestedAuxiliaryFieldProductionTraceAt (fuel : Nat) :
    ∃ innerGroups innerActive final,
      innerGroups[0]?.map (·.addrs) = some #[treeId.addr] ∧
      FlatPositivityDomainTrace innerGroups innerActive checkerMethods
        (fuel + 1) treeExpr auxiliaryFieldWhnfAfter final := by
  rcases nestedAuxiliaryFieldProductionTrace with
    ⟨innerGroups, innerActive, final, rootMatches, trace⟩
  cases trace with
  | rootFree root free =>
      rw [root] at rootMatches
      simp only [Option.map_some, Option.some.injEq] at rootMatches
      rw [rootMatches, auxiliaryTreeMentionsRootNative] at free
      contradiction
  | «forall» root mentioned whnf domainFree opening tail restored =>
      rw [auxiliaryDomainWhnfRun] at whnf
      injection whnf with resultEq _stateEq
      have terminal := auxiliaryDomainWhnfNotForall
      rw [resultEq] at terminal
      exact terminal.elim
  | application root mentioned whnf notForall spine active valid =>
      exact ⟨innerGroups, innerActive, _, rootMatches,
        .application (fuel := fuel) root mentioned whnf notForall spine
          active valid⟩

/-- The production-derived direct field trace transported at any positive
Lean4Lean positivity fuel. -/
theorem nestedAuxiliaryConstructorPositivityTraceAt (fuel : Nat) :
    Nonempty (Lean4Lean.AddInductive.ConstructorPositivityTrace leanFlatStats
      leanFlatWrap.name 0 leanFlatConstructorContext leanTreeExpr
        (fuel + 1)) := by
  rcases nestedAuxiliaryFieldProductionTraceAt fuel with
    ⟨innerGroups, innerActive, final, root, trace⟩
  exact FlatPositivityTraceTransport.constructorPositivityTrace
    nestedAuxiliaryPositivityTransport trace root .domain

/-- The inner call retained from production's nested traversal constructs the
exact Lean4Lean positivity trace for the copied auxiliary field. -/
theorem nestedAuxiliaryConstructorPositivityTrace :
    Nonempty (Lean4Lean.AddInductive.ConstructorPositivityTrace leanFlatStats
      leanFlatWrap.name 0 leanFlatConstructorContext leanTreeExpr
        (positivityFuel - 3)) := by
  rcases nestedAuxiliaryFieldProductionTrace with
    ⟨innerGroups, innerActive, final, root, trace⟩
  exact FlatPositivityTraceTransport.constructorPositivityTrace
    nestedAuxiliaryPositivityTransport trace root .domain

end Ix.Tc.NestedRecursiveFixture
