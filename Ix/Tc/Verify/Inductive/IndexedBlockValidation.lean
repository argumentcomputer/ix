import Ix.Tc.Verify.Inductive.ConstructorValidationTraversal
import Ix.Tc.Verify.Inductive.IndexedRecursiveAcceptance
import Ix.Tc.Verify.Ingress.AnonStructural

/-!
# IndexedVec production block-validation trace

The standalone positivity fixture is useful for operation-level transport, but
it is not by itself evidence that production block checking selected that
constructor or positivity branch.  This module classifies the already-proved
`familyKernelRun`, retaining the exact classification, member reset, loaded
header, constructor order, and safety-gated positivity executions reached by
that one block run.
-/

namespace Ix.Tc.IndexedRecursiveFixture

local instance blockValidationIdDecidableEq : DecidableEq (KId .anon) :=
  AnonStructural.idDecidableEq

local instance blockValidationConstDecidableEq : DecidableEq (KConst .anon) :=
  AnonStructural.constDecidableEq

/-- Exact first phase of the production family run. -/
def familyClassificationOutcome :=
  (RecM.classifyInductiveBlockMembers familyBlockId familyMembers.toList #[]
    #[]).run checkerMethods natKernelAfter

def familyClassificationAfter : TcState .anon :=
  match familyClassificationOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private def familyClassificationMatches : Bool :=
  match familyClassificationOutcome with
  | .ok (indIds, ctorIds) _ =>
      decide (indIds = #[familyId] ∧ ctorIds = #[nilId, consId])
  | .error _ _ => false

private theorem familyClassificationMatchesNative :
    familyClassificationMatches = true := by
  native_decide

/-- Classification of the untouched family members returns exactly the one
family header and the two source-ordered constructors. -/
theorem familyClassificationRun :
    (RecM.classifyInductiveBlockMembers familyBlockId familyMembers.toList #[]
      #[]).run checkerMethods natKernelAfter =
        .ok (#[familyId], #[nilId, consId]) familyClassificationAfter := by
  have success := familyClassificationMatchesNative
  unfold familyClassificationMatches at success
  unfold familyClassificationAfter
  generalize houtcome : familyClassificationOutcome = outcome at success ⊢
  cases outcome with
  | error err failed => simp at success
  | ok classified after =>
      rcases classified with ⟨indIds, ctorIds⟩
      simp only at success
      have hmatches :
          indIds = #[familyId] ∧ ctorIds = #[nilId, consId] :=
        of_decide_eq_true success
      rcases hmatches with ⟨rfl, rfl⟩
      simpa only [familyClassificationOutcome] using houtcome

/-- Deterministic reset immediately before the classified family member. -/
def familyMemberResetAfter : TcState .anon :=
  match TcM.reset familyClassificationAfter with
  | .ok _ after => after
  | .error _ failed => failed

theorem familyMemberResetRun :
    TcM.reset familyClassificationAfter = .ok () familyMemberResetAfter := by
  unfold familyMemberResetAfter TcM.reset
  rfl

private theorem familyMemberLoadedNative :
    familyMemberResetAfter.env.get? familyId = some familyConcrete := by
  native_decide

/-- The member lookup is a fast physical hit and therefore preserves the
post-reset state. -/
theorem familyMemberTryLookupRun :
    TcM.tryGetConst familyId familyMemberResetAfter =
      .ok (some familyConcrete) familyMemberResetAfter := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _
    familyMemberResetAfter = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) familyMemberResetAfter =
    .ok familyMemberResetAfter familyMemberResetAfter from rfl]
  simp only
  rw [familyMemberLoadedNative]
  rfl

theorem familyMemberLookupRun :
    TcM.getConst familyId familyMemberResetAfter =
      .ok familyConcrete familyMemberResetAfter := by
  unfold TcM.getConst
  change EStateM.bind (TcM.tryGetConst familyId) _ familyMemberResetAfter = _
  unfold EStateM.bind
  rw [familyMemberTryLookupRun]
  rfl

private theorem familyConcreteHeaderNative :
    familyConcrete =
      .indc () () 1 1 1 false familyBlockId 0 familyConcrete.ty
        #[nilId, consId] () := by
  native_decide

/-- Exact anonymous header installed by family ingress. -/
theorem familyConcreteHeader :
    familyConcrete =
      .indc () () 1 1 1 false familyBlockId 0 familyConcrete.ty
        #[nilId, consId] () :=
  familyConcreteHeaderNative

def familyDiscoveryOutcome :=
  (RecM.discoverBlockInductives familyBlockId).run checkerMethods
    familyMemberResetAfter

def familyDiscoveryAfter : TcState .anon :=
  match familyDiscoveryOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private def familyDiscoveryMatches : Bool :=
  match familyDiscoveryOutcome with
  | .ok ids _ => decide (ids = #[familyId])
  | .error _ _ => false

private theorem familyDiscoveryMatchesNative :
    familyDiscoveryMatches = true := by
  native_decide

/-- The certified family block has exactly one inductive peer. -/
theorem familyDiscoveryRun :
    (RecM.discoverBlockInductives familyBlockId).run checkerMethods
      familyMemberResetAfter = .ok #[familyId] familyDiscoveryAfter := by
  have success := familyDiscoveryMatchesNative
  unfold familyDiscoveryMatches at success
  unfold familyDiscoveryAfter
  generalize houtcome : familyDiscoveryOutcome = outcome at success ⊢
  cases outcome with
  | error err failed => simp at success
  | ok ids after =>
      simp only at success
      have hids : ids = #[familyId] := of_decide_eq_true success
      subst ids
      simpa only [familyDiscoveryOutcome] using houtcome

/-! ## Exact resolved-family prefix

The block trace below already retains these phases abstractly.  The concrete
outcomes here give that trace canonical state names, so the source-ordered
constructor traversal can be aligned with the physical environment without
re-running the `cons` positivity body. -/

def familyArityOutcome :=
  (RecM.checkedMetadataSum "inductive params + indices" #[1, 1]).run
    checkerMethods familyDiscoveryAfter

def familyArityResult : UInt64 :=
  match familyArityOutcome with
  | .ok arity _ => arity
  | .error _ _ => 0

def familyArityAfter : TcState .anon :=
  match familyArityOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem familyAritySucceededNative :
    (match familyArityOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem familyArityRun :
    (RecM.checkedMetadataSum "inductive params + indices" #[1, 1]).run
      checkerMethods familyDiscoveryAfter =
        .ok familyArityResult familyArityAfter := by
  have success := familyAritySucceededNative
  unfold familyArityResult familyArityAfter
  generalize houtcome : familyArityOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyArityOutcome]

def familyResultLevelOutcome :=
  (RecM.getResultSortLevel familyConcrete.ty familyArityResult.toNat).run
    checkerMethods familyArityAfter

def familyResultLevel : KUniv .anon :=
  match familyResultLevelOutcome with
  | .ok level _ => level
  | .error _ _ => default

def familyResultLevelAfter : TcState .anon :=
  match familyResultLevelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem familyResultLevelSucceededNative :
    (match familyResultLevelOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem familyResultLevelRun :
    (RecM.getResultSortLevel familyConcrete.ty familyArityResult.toNat).run
      checkerMethods familyArityAfter =
        .ok familyResultLevel familyResultLevelAfter := by
  have success := familyResultLevelSucceededNative
  unfold familyResultLevel familyResultLevelAfter
  generalize houtcome : familyResultLevelOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyResultLevelOutcome]

def familyPeerAgreementOutcome :=
  (RecM.checkInductivePeerAgreement familyId familyBlockId 1 1 false
    familyConcrete.ty familyResultLevel #[familyId]).run checkerMethods
      familyResultLevelAfter

def familyPeerAgreementAfter : TcState .anon :=
  match familyPeerAgreementOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem familyPeerAgreementSucceededNative :
    (match familyPeerAgreementOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem familyPeerAgreementRun :
    (RecM.checkInductivePeerAgreement familyId familyBlockId 1 1 false
      familyConcrete.ty familyResultLevel #[familyId]).run checkerMethods
        familyResultLevelAfter = .ok () familyPeerAgreementAfter := by
  have success := familyPeerAgreementSucceededNative
  unfold familyPeerAgreementAfter
  generalize houtcome : familyPeerAgreementOutcome = outcome at success ⊢
  cases outcome with
  | error err failed => simp at success
  | ok value after =>
      cases value
      simpa only [familyPeerAgreementOutcome] using houtcome

def familyNilValidationOutcome :=
  (RecM.checkInductiveConstructor nilId familyId 0 1 1 1 false
    familyConcrete.ty familyResultLevel #[familyId.addr]).run checkerMethods
      familyPeerAgreementAfter

def familyNilValidationAfter : TcState .anon :=
  match familyNilValidationOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem familyNilValidationSucceededNative :
    (match familyNilValidationOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem familyNilValidationRun :
    (RecM.checkInductiveConstructor nilId familyId 0 1 1 1 false
      familyConcrete.ty familyResultLevel #[familyId.addr]).run checkerMethods
        familyPeerAgreementAfter = .ok () familyNilValidationAfter := by
  have success := familyNilValidationSucceededNative
  unfold familyNilValidationAfter
  generalize houtcome : familyNilValidationOutcome = outcome at success ⊢
  cases outcome with
  | error err failed => simp at success
  | ok value after =>
      cases value
      simpa only [familyNilValidationOutcome] using houtcome

/-- Exhaustive trace extracted from the real successful `IndexedVec` family
block run.  No validation subcall is replayed independently. -/
theorem indexedVecFamilyBlockValidationTrace :
    InductiveBlockValidationTrace familyBlockId familyMembers checkerMethods
      natKernelAfter familyKernelAfter := by
  apply RecM.checkInductiveBlockImpl_success checkerMethods
  simpa only [RecM.checkInductiveBlock] using familyKernelRun

/-- The generic block trace specialized to its exact concrete classification
result. -/
theorem indexedVecFamilyBlockValidationTraceExact :
    ∃ afterInductives,
      InductiveMembersValidationTrace checkerMethods [familyId]
          familyClassificationAfter afterInductives ∧
        (RecM.checkInductiveConstructorMembers [nilId, consId]).run
          checkerMethods afterInductives = .ok () familyKernelAfter := by
  cases indexedVecFamilyBlockValidationTrace with
  | success classification inductives constructors =>
      rw [familyClassificationRun] at classification
      cases classification
      exact ⟨_, inductives, constructors⟩

/-- The one classified inductive pass selects the physical `IndexedVec`
header after exactly the reset retained by the block trace. -/
theorem indexedVecFamilyMemberValidationTrace :
    ∃ afterMember,
      InductiveMemberValidationTrace familyId checkerMethods
        familyMemberResetAfter afterMember := by
  obtain ⟨afterInductives, inductives, constructors⟩ :=
    indexedVecFamilyBlockValidationTraceExact
  cases inductives with
  | cons reset head tail =>
      rw [familyMemberResetRun] at reset
      cases reset
      exact ⟨_, head⟩

/-- The loaded member trace normalized to the exact ingressed family header. -/
theorem indexedVecFamilyResolvedValidationTrace :
    ∃ afterMember,
      ResolvedInductiveMemberValidationTrace familyId 1 1 1
        #[nilId, consId] familyBlockId false familyConcrete.ty checkerMethods
          familyMemberResetAfter afterMember := by
  obtain ⟨afterMember, member⟩ := indexedVecFamilyMemberValidationTrace
  cases member with
  | success lookup resolved =>
      rw [familyMemberLookupRun] at lookup
      rw [familyConcreteHeader] at lookup
      cases lookup
      exact ⟨_, resolved⟩

/-- Constructor traversal selected inside the resolved family trace.  The
singleton discovery result fixes the positivity root array to the physical
`IndexedVec` family address. -/
theorem indexedVecFamilyConstructorsValidationTrace :
    ∃ (indLevel : KUniv .anon) (initial final : TcState .anon),
      InductiveConstructorsValidationTrace familyId 1 1 1 false
        familyConcrete.ty indLevel #[familyId.addr] checkerMethods
          [nilId, consId] 0 initial final := by
  obtain ⟨afterMember, resolved⟩ :=
    indexedVecFamilyResolvedValidationTrace
  cases resolved with
  | success discovery arity level peers constructors recursors =>
      rw [familyDiscoveryRun] at discovery
      cases discovery
      rename_i indArity indLevel afterArity afterLevel afterPeers
        afterConstructors
      refine ⟨indLevel, afterPeers, afterConstructors, ?_⟩
      simpa using constructors

/-- The same source-ordered constructor traversal with every resolved-family
prefix state identified by its exact production execution. -/
theorem indexedVecFamilyConstructorsValidationTraceExact :
    ∃ final : TcState .anon,
      InductiveConstructorsValidationTrace familyId 1 1 1 false
        familyConcrete.ty familyResultLevel #[familyId.addr] checkerMethods
          [nilId, consId] 0 familyPeerAgreementAfter final := by
  obtain ⟨afterMember, resolved⟩ :=
    indexedVecFamilyResolvedValidationTrace
  cases resolved with
  | success discovery arity level peers constructors recursors =>
      rw [familyDiscoveryRun] at discovery
      cases discovery
      rw [familyArityRun] at arity
      cases arity
      rw [familyResultLevelRun] at level
      cases level
      rw [familyPeerAgreementRun] at peers
      cases peers
      exact ⟨_, by simpa using constructors⟩

/-- The source-order traversal reaches `IndexedVec.cons` at canonical
constructor index one. -/
theorem indexedVecConsProductionValidationTrace :
    ∃ (indLevel : KUniv .anon) (initial final : TcState .anon),
      InductiveConstructorValidationTrace consId familyId 1 1 1 1 false
        familyConcrete.ty indLevel #[familyId.addr] checkerMethods initial
          final := by
  obtain ⟨indLevel, initial, final, constructors⟩ :=
    indexedVecFamilyConstructorsValidationTrace
  cases constructors with
  | cons nilValidation tail =>
      cases tail with
      | cons consValidation terminal =>
          exact ⟨indLevel, _, _, consValidation⟩

/-- The `cons` validation starts at the unique state reached after the exact
`nil` call in the production constructor loop. -/
theorem indexedVecConsProductionValidationTraceExact :
    ∃ final : TcState .anon,
      InductiveConstructorValidationTrace consId familyId 1 1 1 1 false
        familyConcrete.ty familyResultLevel #[familyId.addr] checkerMethods
          familyNilValidationAfter final := by
  obtain ⟨final, constructors⟩ :=
    indexedVecFamilyConstructorsValidationTraceExact
  cases constructors with
  | cons nilValidation tail =>
      have nilRun := InductiveConstructorValidationTrace.run nilValidation
      rw [familyNilValidationRun] at nilRun
      cases nilRun
      cases tail with
      | cons consValidation terminal =>
          exact ⟨_, consValidation⟩

private theorem familyNilAfterConsLoadedNative :
    familyNilValidationAfter.env.get? consId = some consConcrete := by
  native_decide

/-- The production-selected `cons` state still contains the exact ingressed
constructor; the preceding family phases and `nil` validation only update
checker-local caches and scopes. -/
theorem familyNilAfterConsTryLookupRun :
    TcM.tryGetConst consId familyNilValidationAfter =
      .ok (some consConcrete) familyNilValidationAfter := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _
    familyNilValidationAfter = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) familyNilValidationAfter =
    .ok familyNilValidationAfter familyNilValidationAfter from rfl]
  simp only
  rw [familyNilAfterConsLoadedNative]
  rfl

theorem familyNilAfterConsLookupRun :
    TcM.getConst consId familyNilValidationAfter =
      .ok consConcrete familyNilValidationAfter := by
  unfold TcM.getConst
  change EStateM.bind (TcM.tryGetConst consId) _ familyNilValidationAfter = _
  unfold EStateM.bind
  rw [familyNilAfterConsTryLookupRun]
  rfl

private theorem consConcreteHeaderNative :
    consConcrete =
      .ctor () () false 1 familyId 1 1 3 consConcrete.ty := by
  native_decide

/-- Exact physical constructor header selected at source index one. -/
theorem consConcreteHeader :
    consConcrete =
      .ctor () () false 1 familyId 1 1 3 consConcrete.ty :=
  consConcreteHeaderNative

theorem familyNilAfterConsHeaderLookupRun :
    TcM.getConst consId familyNilValidationAfter =
      .ok (.ctor () () false 1 familyId 1 1 3 consConcrete.ty)
        familyNilValidationAfter := by
  rw [← consConcreteHeader]
  exact familyNilAfterConsLookupRun

/-- The positivity evidence below is the safe gate nested inside the exact
`cons` validation selected by `familyKernelRun`.  The surrounding metadata,
parameter, universe, and return-type equations retain the state chain and
prevent an independently replayed positivity call from satisfying the
statement. -/
theorem indexedVecConsProductionPositivityTrace :
    ∃ (indLevel : KUniv .anon) (ctorTy : KExpr .anon) (ctorFields : Nat)
        (initial afterMetadata afterParameters afterPositivity afterUniverses
          final : TcState .anon),
      (RecM.checkCtorMetadataAgainstParent consId familyId 1 1 1 false).run
          checkerMethods initial = .ok (ctorTy, ctorFields) afterMetadata ∧
        (RecM.checkParamAgreement familyConcrete.ty ctorTy 1).run
          checkerMethods afterMetadata = .ok () afterParameters ∧
        (RecM.checkPositivity ctorTy 1 #[familyId.addr]).run checkerMethods
          afterParameters = .ok () afterPositivity ∧
        ConstructorPositivityTrace ctorTy 1 #[familyId.addr] checkerMethods
          afterParameters afterPositivity ∧
        (RecM.checkFieldUniverses ctorTy 1 indLevel).run checkerMethods
          afterPositivity = .ok () afterUniverses ∧
        (RecM.checkCtorReturnType ctorTy 1 1 ctorFields familyId.addr 1
          #[familyId.addr]).run checkerMethods afterUniverses = .ok () final := by
  obtain ⟨indLevel, initial, final, validation⟩ :=
    indexedVecConsProductionValidationTrace
  cases validation with
  | success metadata parameters positivity universes returnType =>
      cases positivity with
      | safe run trace =>
          exact ⟨indLevel, _, _, _, _, _, _, _, _, metadata, parameters, run,
            trace, universes, returnType⟩

end Ix.Tc.IndexedRecursiveFixture
