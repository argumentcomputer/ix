import Ix.Tc.Verify.Inductive.GeneratedRecursorCheckerFixture
import Ix.Tc.Verify.Inductive.GeneratedRecursorMemberCheck
import Ix.Tc.Verify.Inductive.IndexedBlockValidation
import Ix.Tc.Verify.Inductive.ResultSortTelescope
import Ix.Tc.Verify.RecursiveMethods.ScopedInference
import Ix.Tc.Verify.ScopedSuffix.ClosedContext

/-!
# Production recursor-member preparation fixture

This module runs the newly exposed production prelude on the certified
`IndexedVec.rec` declaration.  It proves that the prelude freezes the original
stored declaration, resolves the certified family block and major, validates
the non-K target, and hands the exact canonical installed cache batch to the
already verified comparison tail.

The scoped tail theorem starts at the post-prelude state.  A second theorem
composes the production prelude from its initial state while retaining four
separate operation-level preservation obligations; no whole-prelude oracle is
introduced.
-/

namespace Ix.Tc.IndexedRecursiveFixture

open GeneratedRecursorSemantics
open IndexedRecursiveCertificateFixture
open Lean4Lean
open Lean4Lean.InductiveReplayFixtures

local instance generatedMemberAddressDecidableEq : DecidableEq Address :=
  AnonStructural.addressDecidableEq

local instance generatedMemberKIdDecidableEq : DecidableEq (KId .anon) :=
  AnonStructural.idDecidableEq

local instance generatedMemberKUnivDecidableEq : DecidableEq (KUniv .anon) :=
  AnonStructural.decidableEqOfRoundtrip AnonStructural.Univ.ofKernel
    AnonStructural.Univ.toKernel AnonStructural.Univ.roundtrip

local instance generatedMemberKExprDecidableEq : DecidableEq (KExpr .anon) :=
  AnonStructural.exprDecidableEq

local instance generatedMemberKConstDecidableEq : DecidableEq (KConst .anon) :=
  AnonStructural.constDecidableEq

local instance generatedMemberVConstantDecidableEq :
    DecidableEq Lean4Lean.VConstant := by
  intro left right
  cases left
  cases right
  simp only [Lean4Lean.VConstant.mk.injEq]
  infer_instance

local instance generatedMemberRecRuleDecidableEq :
    DecidableEq (RecRule .anon) :=
  AnonStructural.decidableEqOfRoundtrip AnonStructural.RecRule.ofKernel
    AnonStructural.RecRule.toKernel AnonStructural.RecRule.roundtrip

local instance generatedMemberRecursorDecidableEq :
    DecidableEq (GeneratedRecursor .anon) := by
  intro left right
  cases left
  cases right
  simp only [GeneratedRecursor.mk.injEq]
  infer_instance

local instance generatedMemberEqKeyDecidableEq : DecidableEq EqKey := by
  intro left right
  cases left
  cases right
  simp only [EqKey.mk.injEq]
  infer_instance

deriving instance DecidableEq for PrimAddrs

local instance generatedMemberLocalDeclDecidableEq :
    DecidableEq (LocalDecl .anon) := by
  intro left right
  cases left <;> cases right <;> simp_all <;> infer_instance

local instance generatedMemberPreparationDecidableEq :
    DecidableEq (RecM.PreparedRecursorMemberCheck .anon) := by
  intro left right
  cases left
  cases right
  simp only [RecM.PreparedRecursorMemberCheck.mk.injEq]
  infer_instance

local instance generatedMemberSnapshotDecidableEq :
    DecidableEq (RecM.RecursorMemberDeclarationSnapshot .anon) := by
  intro left right
  cases left
  cases right
  simp only [RecM.RecursorMemberDeclarationSnapshot.mk.injEq]
  infer_instance

/-! ## Exact production preparation -/

/-- Production-realistic entry state for recursor-member checking.  The
family block has already been accepted, so the coordinated checker publishes
the corresponding successful verdict before a stored recursor consults it. -/
def familyMemberInitial : TcState .anon :=
  familyKernelAfter.withBlockCheckResult familyBlockId (.ok ())

private theorem familyMemberInitialClosedFieldsNative :
    familyMemberInitial.ctx = #[] ∧
      familyMemberInitial.letVals = #[] ∧
      familyMemberInitial.numLetBindings = 0 ∧
      familyMemberInitial.lctx.decls = #[] ∧
      familyMemberInitial.lctx.index.toList = [] ∧
      familyMemberInitial.lazyFault = none := by
  native_decide

/-- The reached recursor-member ingress is a genuinely closed production
state.  Local-context well-formedness is proved extensionally from the empty
lookup range, without equating hash-map bucket representations. -/
theorem familyMemberInitial_closed : ClosedContextState familyMemberInitial := by
  rcases familyMemberInitialClosedFieldsNative with
    ⟨ctx, letVals, numLets, declarations, indexEntries, lazyFault⟩
  refine ⟨ctx, letVals, numLets, declarations, ?_, lazyFault⟩
  constructor
  intro fvar index lookup
  have member :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr lookup
  rw [indexEntries] at member
  simp at member

/-- Closed singleton-suffix model at the exact universe arity generated for
`IndexedVec.rec`. -/
def familyMemberModel :
    ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld :=
  ClosedContextDigest.model RawProjRel.none familyAcceptedWorld
    transaction.certificate.generation.recursor.uvars

theorem familyMemberModel_uvars :
    transaction.certificate.generation.recursor.uvars =
      familyMemberModel.keys.uvars :=
  rfl

private theorem familyNatZeroLookup :
    familyAcceptedWorld.venv.constants ``Nat.zero =
      some ⟨0, VExpr.nat⟩ := by
  native_decide

private theorem familyNatSuccLookup :
    familyAcceptedWorld.venv.constants ``Nat.succ =
      some ⟨0, .forallE VExpr.nat VExpr.nat⟩ := by
  native_decide

private theorem familyCharOfNatAbsent :
    familyAcceptedWorld.venv.constants ``Char.ofNat = none := by
  native_decide

/-- Nat literals are well typed in the accepted family world at the exact
recursor universe arity.  The proof uses only the two constructors installed
by the preceding certified Nat transaction. -/
theorem familyMemberNatLit_type (value : Nat) :
    familyAcceptedWorld.venv.HasType familyMemberModel.keys.uvars []
      (VExpr.natLit value) VExpr.nat := by
  induction value with
  | zero =>
      simpa [VExpr.natLit, VExpr.natZero, VExpr.nat, VExpr.instL] using
        (Lean4Lean.VEnv.HasType.const
          (env := familyAcceptedWorld.venv)
          (U := familyMemberModel.keys.uvars) (Γ := [])
          (ci := ⟨0, VExpr.nat⟩) (ls := []) familyNatZeroLookup
          (by simp) rfl)
  | succ value ih =>
      have successor : familyAcceptedWorld.venv.HasType
          familyMemberModel.keys.uvars [] (.const ``Nat.succ [])
          (.forallE VExpr.nat VExpr.nat) := by
        exact Lean4Lean.VEnv.HasType.const familyNatSuccLookup
          (by simp) rfl
      simpa [VExpr.natLit, VExpr.natSucc, VExpr.nat, VExpr.inst,
        VExpr.instL] using
        Lean4Lean.VEnv.HasType.app successor ih

/-- The complete literal/projection theory needed by the finite generated-
artifact comparison schedule.  String literals are impossible because the
accepted Nat/IndexedVec world contains no `Char.ofNat`. -/
def familyMemberWhnfTheory : WhnfTheory RawProjRel.none familyAcceptedWorld
    familyMemberModel.keys.uvars where
  literalWF := by
    intro literal contains
    cases literal with
    | natVal value => exact ⟨_, familyMemberNatLit_type value⟩
    | strVal value =>
        change familyAcceptedWorld.venv.contains ``Char.ofNat ∧
          familyAcceptedWorld.venv.contains ``String.ofList at contains
        rcases contains.1 with ⟨constant, lookup⟩
        rw [familyCharOfNatAbsent] at lookup
        contradiction
  projections := RawProjRel.none_ok familyAcceptedWorld.venv
    familyMemberModel.keys.uvars

theorem familyMemberModel_initialInScope :
    familyMemberModel.StateInScope familyMemberInitial :=
  ClosedContextDigest.model_stateInScope familyMemberInitial_closed

/-- Publishing the accepted family verdict is semantically and
suffix-digest neutral. -/
theorem familyMemberInitial_preservesScoped
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport}
    (initialInvariant :
      ScopedWhnfStateInv model layer semantics support [] familyKernelAfter) :
    ScopedWhnfStateInv model layer semantics support [] familyMemberInitial :=
  ScopedWhnfStateInv.withBlockCheckSuccess familyBlockAccepted
    initialInvariant

/-- Stable compatibility form for nonrecursive generated batches.  For this
recursive fixture the `TrustedReferences` premise cannot be instantiated:
the installed `cons` rule names `IndexedVec.rec`, which has not yet crossed
the recursor-block admission boundary.  The active theorem below is the
constructive E2c path. -/
theorem familyInstalledRecursorsProvenance
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {support : RunSupport}
    (trustedReferences : RecM.TrustedReferences familyAcceptedWorld support)
    (initialInvariant : ScopedWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support [] familyMemberInitial) :
    CacheProvenance
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      (CacheAuthority.stable familyAcceptedWorld) support
      (.recursor familyBlockId familyInstalledRecursors) := by
  have familyTrusted : familyAcceptedWorld.trusted familyId :=
    familyAtomicAdmission.memberTrusted (by simp [familyMembers_eq])
  have supported :
      (CacheEntry.recursor familyBlockId familyInstalledRecursors).SupportedBy
        support := by
    intro generated hgenerated
    have hintern :=
      familyInstalledRecursorsInternSupported generated hgenerated
    refine ⟨?_, ?_⟩
    · apply initialInvariant.1.1.internSupport.expr
      simpa [familyMemberInitial, TcState.withBlockCheckResult] using hintern.1
    · intro rule hrule
      apply initialInvariant.1.1.internSupport.expr
      simpa [familyMemberInitial, TcState.withBlockCheckResult] using
        hintern.2 rule hrule
  have generatedAuthorized : ∀ generated ∈ familyInstalledRecursors,
      ∃ id : KId .anon,
        ((CacheAuthority.stable familyAcceptedWorld).world.trusted id ∨
          (CacheAuthority.stable familyAcceptedWorld).active id) ∧
          id.addr = generated.indAddr := by
    intro generated hgenerated
    exact ⟨familyId, .inl familyTrusted,
      (familyInstalledRecursorsInductiveAddress generated hgenerated).symm⟩
  refine ⟨supported, ?_, ?_⟩
  · intro id href
    apply Or.inl
    rcases href with ⟨generated, hgenerated, hheader | htype | hrules⟩
    · have haddr : id.addr = familyId.addr :=
        hheader.trans
          (familyInstalledRecursorsInductiveAddress generated hgenerated)
      have hid : id = familyId := KId.anon_eq_of_addr_eq haddr
      subst id
      exact familyTrusted
    · exact trustedReferences (supported generated hgenerated).1 htype
    · obtain ⟨rule, hrule, href⟩ := hrules
      exact trustedReferences
        ((supported generated hgenerated).2 rule hrule) href
  · change StructuralInductiveCacheValid CacheSemantics.blockErrorsOnly
      (CacheAuthority.stable familyAcceptedWorld) support
        (.recursor familyBlockId familyInstalledRecursors)
    exact ⟨CacheAuthority.authorizesBlock_of_accepted familyBlockAccepted,
      generatedAuthorized⟩

/-- The exact recursive batch has provenance under the recursor block's
temporary coordinated authority.  Family ownership remains stable; only a
direct reference selected from an executable type or rule may consume the
active-member disjunct. -/
theorem familyInstalledRecursorsActiveProvenance
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {support : RunSupport}
    (authorizedReferences : RecM.AuthorizedReferences
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      support)
    (initialInvariant : ScopedActiveWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support recursorMembers [] familyMemberInitial) :
    CacheProvenance
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      support (.recursor familyBlockId familyInstalledRecursors) := by
  have familyTrusted : familyAcceptedWorld.trusted familyId :=
    familyAtomicAdmission.memberTrusted (by simp [familyMembers_eq])
  have supported :
      (CacheEntry.recursor familyBlockId familyInstalledRecursors).SupportedBy
        support := by
    intro generated hgenerated
    have hintern :=
      familyInstalledRecursorsInternSupported generated hgenerated
    refine ⟨?_, ?_⟩
    · apply initialInvariant.active.internSupport.expr
      simpa [familyMemberInitial, TcState.withBlockCheckResult] using hintern.1
    · intro rule hrule
      apply initialInvariant.active.internSupport.expr
      simpa [familyMemberInitial, TcState.withBlockCheckResult] using
        hintern.2 rule hrule
  have generatedAuthorized : ∀ generated ∈ familyInstalledRecursors,
      ∃ id : KId .anon,
        (familyAcceptedWorld.trusted id ∨ id ∈ recursorMembers) ∧
          id.addr = generated.indAddr := by
    intro generated hgenerated
    exact ⟨familyId, .inl familyTrusted,
      (familyInstalledRecursorsInductiveAddress generated hgenerated).symm⟩
  refine ⟨supported, ?_, ?_⟩
  · intro id href
    rcases href with ⟨generated, hgenerated, hheader | htype | hrules⟩
    · apply Or.inl
      have haddr : id.addr = familyId.addr :=
        hheader.trans
          (familyInstalledRecursorsInductiveAddress generated hgenerated)
      have hid : id = familyId := KId.anon_eq_of_addr_eq haddr
      change familyAcceptedWorld.trusted id
      simpa only [hid] using familyTrusted
    · rcases authorizedReferences (supported generated hgenerated).1 htype with
        htrusted | hactive
      · exact .inl htrusted
      · exact .inr ⟨trivial, hactive⟩
    · obtain ⟨rule, hrule, href⟩ := hrules
      rcases authorizedReferences
          ((supported generated hgenerated).2 rule hrule) href with
        htrusted | hactive
      · exact .inl htrusted
      · exact .inr ⟨trivial, hactive⟩
  · change StructuralInductiveCacheValid CacheSemantics.blockErrorsOnly
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      support (.recursor familyBlockId familyInstalledRecursors)
    refine ⟨CacheAuthority.AuthorizesBlock.mono
      CacheAuthority.stable_le_coordinatedBlock
      (CacheAuthority.authorizesBlock_of_accepted familyBlockAccepted), ?_⟩
    exact generatedAuthorized

/-- Once the concrete batch provenance is fixed at the ingress boundary, the
transactional commit preserves the scoped invariant from any state reached by
rule construction.  In particular, callback-written cache contents cannot
become an additional premise of the commit proof. -/
theorem familyGeneratedRuleCommit_scoped_wf
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {support : RunSupport}
    (trustedReferences : RecM.TrustedReferences familyAcceptedWorld support)
    (initialInvariant : ScopedWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support [] familyMemberInitial)
    (before : TcState .anon) :
    TcM.WF (ScopedWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support []) before
      ((RecM.commitGeneratedRecursorRulesAt familyBlockId
        familyGeneratedSnapshot familyGeneratedWithRules).run
          checkerMethods)
      (fun _ _ => True) := by
  apply RecM.commitGeneratedRecursorRulesAt_scoped_wf
  simpa only [familyInstalledRecursors] using
    familyInstalledRecursorsProvenance trustedReferences initialInvariant

/-- Transactional commit under exact recursor-block authority.  This is the
non-vacuous recursive counterpart of `familyGeneratedRuleCommit_scoped_wf`. -/
theorem familyGeneratedRuleCommit_activeScoped_wf
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {support : RunSupport}
    (authorizedReferences : RecM.AuthorizedReferences
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      support)
    (initialInvariant : ScopedActiveWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support recursorMembers [] familyMemberInitial)
    (before : TcState .anon) :
    TcM.WF (ScopedActiveWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support recursorMembers []) before
      ((RecM.commitGeneratedRecursorRulesAt familyBlockId
        familyGeneratedSnapshot familyGeneratedWithRules).run
          checkerMethods)
      (fun _ _ => True) := by
  apply RecM.commitGeneratedRecursorRulesAt_activeScoped_wf
  simpa only [familyInstalledRecursors] using
    familyInstalledRecursorsActiveProvenance authorizedReferences
      initialInvariant

/-! ### Finite rule-population intern delta -/

/-- The concrete core run from the actual recursor-member state.  This state
differs from the earlier rule fixture only by the already-published family
block verdict, which the population core leaves untouched. -/
def familyMemberRulePopulationOutcome :=
  (RecM.populateRecursorRulesFromBlockCore familyBlockId recursorBlockId
      familyGeneratedSnapshot).run checkerMethods familyMemberInitial

def familyMemberRulePopulationAfter : TcState .anon :=
  match familyMemberRulePopulationOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyMemberRulePopulationMatches : Bool :=
  match familyMemberRulePopulationOutcome with
  | .ok generated _ => decide (generated = familyGeneratedWithRules)
  | .error _ _ => false

private theorem familyMemberRulePopulationMatchesNative :
    familyMemberRulePopulationMatches = true := by
  native_decide

/-- The actual population core returns the canonical local rule batch from
the exact member-check state. -/
theorem familyMemberRulePopulationRun :
    (RecM.populateRecursorRulesFromBlockCore familyBlockId recursorBlockId
        familyGeneratedSnapshot).run checkerMethods familyMemberInitial =
      .ok familyGeneratedWithRules familyMemberRulePopulationAfter := by
  have hmatches := familyMemberRulePopulationMatchesNative
  unfold familyMemberRulePopulationMatches at hmatches
  unfold familyMemberRulePopulationAfter
  generalize houtcome : familyMemberRulePopulationOutcome = outcome at hmatches ⊢
  cases outcome with
  | error error failed => contradiction
  | ok generated after =>
      have generatedEq : generated = familyGeneratedWithRules :=
        of_decide_eq_true hmatches
      subst generated
      simpa [familyMemberRulePopulationOutcome] using houtcome

/-- The finite expression range added by canonical rule construction.  The
predicate is constructively finite by `InternTable.newExpr_finite`; it does
not include any expression already supported at population ingress. -/
def FamilyMemberPopulationNewExpr (expression : KExpr .anon) : Prop :=
  familyMemberInitial.env.intern.NewExpr
    familyMemberRulePopulationAfter.env.intern expression

theorem familyMemberPopulationNewExpr_finite :
    FiniteSupport FamilyMemberPopulationNewExpr :=
  InternTable.newExpr_finite _ _

/-- Exact finite expression/universe footprint for the concrete recursor
member run.  It contains the complete ingress intern range and precisely the
new expressions introduced while populating recursive rules.  Rule population
does not introduce universes, so the universe component remains the ingress
range rather than being widened by an opaque closure. -/
def familyMemberSupport : RunSupport where
  expr expression :=
    familyMemberInitial.env.intern.ExprSupport expression ∨
      FamilyMemberPopulationNewExpr expression
  exprFinite :=
    (InternTable.exprSupport_finite familyMemberInitial.env.intern).union
      familyMemberPopulationNewExpr_finite
  univ u := familyMemberInitial.env.intern.UnivSupport u
  univFinite := InternTable.univSupport_finite familyMemberInitial.env.intern

/-- Exact declaration ids that may occur in the finite expression footprint of
the concrete member check.  The recursor itself is intentionally listed here:
it is authorized only by the active-member side of coordinated block
authority, never by stable trust in `familyAcceptedWorld`. -/
private def FamilyMemberReferenceId (id : KId .anon) : Prop :=
  id = natId ∨ id = zeroId ∨ id = succId ∨
    id = familyId ∨ id = nilId ∨ id = consId ∨ id = recursorId

private instance familyMemberReferenceIdDecidable (id : KId .anon) :
    Decidable (FamilyMemberReferenceId id) := by
  unfold FamilyMemberReferenceId
  infer_instance

/-- Executable reference census for one concrete intern table. -/
private def familyMemberReferencesCovered (intern : InternTable .anon) : Bool :=
  intern.exprs.toList.all fun entry =>
    entry.2.referenceIds.all fun id => decide (FamilyMemberReferenceId id)

private theorem familyMemberInitialReferencesCovered :
    familyMemberReferencesCovered familyMemberInitial.env.intern = true := by
  native_decide

private theorem familyMemberPopulationReferencesCovered :
    familyMemberReferencesCovered
      familyMemberRulePopulationAfter.env.intern = true := by
  native_decide

private theorem familyMemberReferencesCovered_id
    {intern : InternTable .anon}
    (covered : familyMemberReferencesCovered intern = true)
    {address : Address} {source : KExpr .anon} {id : KId .anon}
    (lookup : intern.exprs[address]? = some source)
    (reference : source.References id) :
    FamilyMemberReferenceId id := by
  unfold familyMemberReferencesCovered at covered
  rw [List.all_eq_true] at covered
  have expressionCovered := covered (address, source)
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr lookup)
  rw [List.all_eq_true] at expressionCovered
  exact of_decide_eq_true <| expressionCovered id
    (KExpr.mem_referenceIds.mpr reference)

/-- Every member of the already-admitted ambient Nat block remains trusted
after the IndexedVec family transaction. -/
theorem familyMemberNatBlockTrusted
    {id : KId .anon} (member : id ∈ natFamilyLink.members) :
    familyAcceptedWorld.trusted id := by
  apply familyAtomicAdmission.promotion.le.trusted
  change id ∈ natFamilyLink.members ∨ natBaseWorld.trusted id
  exact .inl member

private theorem familyMemberReferenceId_authorized
    {id : KId .anon} (reference : FamilyMemberReferenceId id) :
    familyAcceptedWorld.trusted id ∨ id ∈ recursorMembers := by
  rcases reference with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (familyMemberNatBlockTrusted (by native_decide))
  · exact .inl (familyMemberNatBlockTrusted (by native_decide))
  · exact .inl (familyMemberNatBlockTrusted (by native_decide))
  · exact .inl (familyAtomicAdmission.memberTrusted
      (by simp [familyMembers_eq]))
  · exact .inl (familyAtomicAdmission.memberTrusted
      (by simp [familyMembers_eq]))
  · exact .inl (familyAtomicAdmission.memberTrusted
      (by simp [familyMembers_eq]))
  · exact .inr (by simp [recursorMembers_eq])

/-- Every direct reference reachable from the exact member-check footprint is
authorized by the semantic world or by the single active recursor member.
The finite native facts above inspect only concrete intern-table data; this
theorem reconstructs the ordinary proposition consumed by structural cache
provenance. -/
theorem familyMemberAuthorizedReferences : RecM.AuthorizedReferences
    (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
    familyMemberSupport := by
  intro source id supported reference
  change familyAcceptedWorld.trusted id ∨ id ∈ recursorMembers
  apply familyMemberReferenceId_authorized
  change familyMemberInitial.env.intern.ExprSupport source ∨
    FamilyMemberPopulationNewExpr source at supported
  rcases supported with ⟨address, lookup⟩ | ⟨address, lookup, _⟩
  · exact familyMemberReferencesCovered_id
      familyMemberInitialReferencesCovered lookup reference
  · exact familyMemberReferencesCovered_id
      familyMemberPopulationReferencesCovered lookup reference

private def familyMemberInitialConstsCovered : Bool :=
  familyMemberInitial.env.consts.toList.all fun entry =>
    decide (familyAcceptedWorld.catalog entry.1 = some entry.2)

private def familyMemberInitialBlocksCovered : Bool :=
  familyMemberInitial.env.blocks.toList.all fun entry =>
    decide (familyAcceptedWorld.blocks entry.1 = some entry.2)

private def familyMemberInitialUnivKeys : Bool :=
  familyMemberInitial.env.intern.univs.toList.all fun entry =>
    decide (entry.2.addr = entry.1)

private def familyMemberInitialExprKeys : Bool :=
  familyMemberInitial.env.intern.exprs.toList.all fun entry =>
    decide (entry.2.internKey = entry.1)

private theorem familyMemberInitialConstsCoveredNative :
    familyMemberInitialConstsCovered = true := by
  native_decide

private theorem familyMemberInitialBlocksCoveredNative :
    familyMemberInitialBlocksCovered = true := by
  native_decide

private theorem familyMemberInitialUnivKeysNative :
    familyMemberInitialUnivKeys = true := by
  native_decide

private theorem familyMemberInitialExprKeysNative :
    familyMemberInitialExprKeys = true := by
  native_decide

/-- The warm checker state contains only exact entries from the immutable
seven-declaration catalog. -/
theorem familyMemberInitial_loaded :
    LoadedAgrees familyAcceptedWorld.catalog familyMemberInitial.env := by
  intro id concrete lookup
  have covered := familyMemberInitialConstsCoveredNative
  unfold familyMemberInitialConstsCovered at covered
  rw [List.all_eq_true] at covered
  apply of_decide_eq_true
  apply covered (id, concrete)
  apply Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr
  simpa [KEnv.get?] using lookup

/-- The three eagerly ingressed physical blocks agree with the immutable block
catalog after family admission. -/
theorem familyMemberInitial_loadedBlocks :
    LoadedBlocksAgrees familyAcceptedWorld.blocks familyMemberInitial.env := by
  intro block members lookup
  have covered := familyMemberInitialBlocksCoveredNative
  unfold familyMemberInitialBlocksCovered at covered
  rw [List.all_eq_true] at covered
  exact of_decide_eq_true <| covered (block, members)
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr lookup)

/-- Hash-consing key coherence for the complete warm ingress/checker table. -/
theorem familyMemberInitial_internWF : familyMemberInitial.env.intern.WF := by
  apply InternTable.WF.of_toList
  · intro address univ member
    have covered := familyMemberInitialUnivKeysNative
    unfold familyMemberInitialUnivKeys at covered
    rw [List.all_eq_true] at covered
    exact of_decide_eq_true (covered (address, univ) member)
  · intro address expression member
    have covered := familyMemberInitialExprKeysNative
    unfold familyMemberInitialExprKeys at covered
    rw [List.all_eq_true] at covered
    exact of_decide_eq_true (covered (address, expression) member)

private theorem familyMemberInitialEquivParentEmpty :
    familyMemberInitial.equivManager.parent = #[] := by
  native_decide

private theorem familyMemberInitialEquivLabelsEmpty :
    familyMemberInitial.equivManager.nodeToKey = #[] := by
  native_decide

private theorem familyMemberInitialEquivEntriesEmpty :
    familyMemberInitial.equivManager.keyToNode.toList = [] := by
  native_decide

/-- Successful DefEq calls made while checking the dependency blocks leave no
union-find nodes in the reached member-check state. -/
theorem familyMemberInitial_equivalences
    {relation : EqKey → EqKey → Prop} :
    EquivManager.WF relation familyMemberInitial.equivManager := by
  refine ⟨?_, ?_⟩
  · simpa [familyMemberInitialEquivParentEmpty,
      familyMemberInitialEquivLabelsEmpty, EquivManager.empty] using
      (EquivManager.WF.empty (R := relation)).parents
  · intro key node lookup
    have member :=
      Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr lookup
    rw [familyMemberInitialEquivEntriesEmpty] at member
    simp at member

/-- Empty runtime stacks reconstruct the empty Lean4Lean local context even
though the environment and its semantic caches are warm. -/
theorem familyMemberInitial_context :
    CtxRecon familyAcceptedWorld.venv familyMemberModel.keys.uvars
      familyAcceptedWorld.nameOf RawProjRel.none familyMemberInitial [] := by
  rcases familyMemberInitialClosedFieldsNative with
    ⟨ctx, letVals, numLets, declarations, indexEntries, _⟩
  refine {
    size_eq := by rw [ctx, letVals]; rfl
    recon := by rw [ctx, letVals, declarations]; exact .nil
    lwf := familyMemberInitial_closed.lctxWF
    incr := by rw [declarations]; exact .nil
    fresh := by rw [declarations]; exact fun declaration member => nomatch member
    lets := by rw [numLets]; rfl }

/-- The reached production state retains the canonical anonymous primitive
address table installed by `TcState.ofEnvAnon`. -/
private theorem familyMemberInitialPrimitivesNative :
    familyMemberInitial.prims.CanonicalAnon := by
  unfold Primitives.CanonicalAnon
  native_decide

theorem familyMemberInitial_primitives :
    familyMemberInitial.prims.CanonicalAnon := by
  exact familyMemberInitialPrimitivesNative

/-- Catalog, eager-loading, and hash-consing coherence for the warm state,
independent of its semantic cache provenance. -/
theorem familyMemberInitial_stateWF :
    TcStateWF RawProjRel.none familyMemberInitial familyAcceptedWorld where
  trustedCatalog := familyAtomicAdmission.trustedCatalog
  loaded := familyMemberInitial_loaded
  intern := familyMemberInitial_internWF

/-- The concrete footprint covers the complete member-check ingress table. -/
theorem familyMemberSupport_coversInitial :
    familyMemberSupport.CoversIntern familyMemberInitial.env.intern where
  expr _ support := Or.inl support
  univ _ support := support

/-- Every genuinely new rule-population expression is admitted explicitly by
the concrete footprint. -/
theorem familyMemberSupport_new
    {expression : KExpr .anon}
    (support : FamilyMemberPopulationNewExpr expression) :
    familyMemberSupport expression :=
  Or.inr support

/-- The concrete active invariant cannot encounter lazy ingress because its
closed suffix-model domain requires the production hook to be absent. -/
theorem familyMemberModel_lazyFaultPreserves
    {layer : WhnfLayer} :
    TcM.LazyFaultPreserves
      (ScopedActiveWhnfStateInv familyMemberModel layer
        (kernelCacheSemanticsWithInductives familyMemberModel.keys
          RawProjRel.none)
        familyMemberSupport recursorMembers []) :=
  TcM.LazyFaultPreserves.of_none fun invariant =>
    ClosedContextDigest.model_noLazy invariant.inScope

/-- Every exact frozen-artifact comparison made by the concrete checker tail
lies in the member run's finite expression footprint. -/
theorem familyArtifactCalls_withinMemberSupport :
    familyArtifactCalls.Within familyMemberSupport where
  whnf call := False.elim call
  whnfCore call := False.elim call
  whnfMode call := False.elim call
  whnfCoreFlags call := False.elim call
  infer call := False.elim call
  isDefEq := by
    intro left right call
    change
      (left = familyInstalledRecursors[0]!.ty ∧
          right = recursorConcrete.ty) ∨
        ∃ index, index < familyInstalledRecursors[0]!.rules.size ∧
          left = familyInstalledRecursors[0]!.rules[index]!.rhs ∧
          right = recursorRules[index]!.rhs at call
    have installed := familyInstalledRecursorAtZeroInternSupported
    rcases call with ⟨rfl, rfl⟩ | ⟨index, bound, rfl, rfl⟩
    · have supported : familyMemberSupport familyInstalledRecursors[0]!.ty :=
        Or.inl (by
          simpa [familyMemberInitial, TcState.withBlockCheckResult] using
            installed.1)
      exact ⟨supported, by
        rw [← familyInstalledRecursorType_eq]
        exact supported⟩
    · have ruleMem : familyInstalledRecursors[0]!.rules[index]! ∈
          familyInstalledRecursors[0]!.rules := by
        rw [getElem!_pos familyInstalledRecursors[0]!.rules index bound]
        exact Array.getElem_mem bound
      have supported : familyMemberSupport
          familyInstalledRecursors[0]!.rules[index]!.rhs :=
        Or.inl (by
          simpa [familyMemberInitial, TcState.withBlockCheckResult] using
            installed.2 _ ruleMem)
      refine ⟨supported, ?_⟩
      rw [← familyInstalledRecursorRules_eq]
      exact supported

/-- The exact finite successor-method contract used by all type and rule
comparisons in the concrete member check.  The production state runs in the
accelerated layer; its anon primitive table is proved canonical separately by
the initial active invariant. -/
def familyMemberArtifactSuccessor :
    Methods.ActiveScopedWFAtOn familyMemberModel .accelerated
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      familyMemberSupport recursorMembers familyArtifactCalls
        (Methods.next checkerMethods) :=
  familyArtifactMethodsActiveScopedWFAtOn familyMemberWhnfTheory
    familyArtifactCalls_withinMemberSupport

/-- Executable finite-map inclusion.  Unlike map equality, this is insensitive
to the physical bucket layout left behind by insert/erase pairs. -/
private def hashMapCovered {key value : Type} [BEq key] [Hashable key]
    [DecidableEq value] (before after : Std.HashMap key value) : Bool :=
  after.toList.all fun entry => decide (before[entry.1]? = some entry.2)

private theorem hashMapCovered_get? {key value : Type}
    [BEq key] [Hashable key] [LawfulBEq key] [DecidableEq value]
    {before after : Std.HashMap key value}
    (hcovered : hashMapCovered before after = true)
    {query : key} {result : value} (hget : after[query]? = some result) :
    before[query]? = some result := by
  unfold hashMapCovered at hcovered
  rw [List.all_eq_true] at hcovered
  exact of_decide_eq_true <| hcovered (query, result)
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hget)

private def hashSetCovered {key : Type} [BEq key] [Hashable key]
    (before after : Std.HashSet key) : Bool :=
  after.toList.all before.contains

private theorem hashSetCovered_contains {key : Type}
    [BEq key] [Hashable key] [LawfulBEq key]
    {before after : Std.HashSet key}
    (hcovered : hashSetCovered before after = true)
    {query : key} (hcontains : after.contains query = true) :
    before.contains query = true := by
  unfold hashSetCovered at hcovered
  rw [List.all_eq_true] at hcovered
  exact hcovered query <| Std.HashSet.mem_toList.mpr <|
    Std.HashSet.mem_iff_contains.mpr hcontains

/-- The fixture's coordinated-block cache contains successful verdicts only.
Keeping this checker result-specific avoids requiring executable equality for
the diagnostic-rich `TcError` payload. -/
private def successfulBlockResultsCovered
    (before after : Std.HashMap (KId .anon) (Except (TcError .anon) Unit)) :
    Bool :=
  after.toList.all fun entry =>
    match entry.2, before[entry.1]? with
    | .ok (), some (.ok ()) => true
    | _, _ => false

private theorem successfulBlockResultsCovered_get?
    {before after : Std.HashMap (KId .anon) (Except (TcError .anon) Unit)}
    (hcovered : successfulBlockResultsCovered before after = true)
    {block : KId .anon} {result : Except (TcError .anon) Unit}
    (hget : after[block]? = some result) : before[block]? = some result := by
  unfold successfulBlockResultsCovered at hcovered
  rw [List.all_eq_true] at hcovered
  have hentry := hcovered (block, result)
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hget)
  cases result with
  | error error => contradiction
  | ok success =>
      cases success
      cases hbefore : before[block]? with
      | none => simp [hbefore] at hentry
      | some result =>
          cases result with
          | error error => simp [hbefore] at hentry
          | ok success =>
              cases success
              rfl

/-- Every physical post-population semantic-cache entry occurs in the ingress
cache.  The single reflected certificate enumerates all eighteen cache
families; no equality of hash-map representations is assumed. -/
private def familyMemberRulePopulationCacheChecks : List Bool :=
  let before := familyMemberInitial.env
  let after := familyMemberRulePopulationAfter.env
  [ hashMapCovered before.whnfCache after.whnfCache
  , hashMapCovered before.whnfNoDeltaCache after.whnfNoDeltaCache
  , hashMapCovered before.whnfNoDeltaCheapCache after.whnfNoDeltaCheapCache
  , hashMapCovered before.whnfCoreCache after.whnfCoreCache
  , hashMapCovered before.whnfCoreCheapCache after.whnfCoreCheapCache
  , hashMapCovered before.inferCache after.inferCache
  , hashMapCovered before.inferOnlyCache after.inferOnlyCache
  , hashMapCovered before.defEqCache after.defEqCache
  , hashMapCovered before.defEqCheapCache after.defEqCheapCache
  , hashSetCovered before.defEqFailure after.defEqFailure
  , hashMapCovered before.unfoldCache after.unfoldCache
  , hashSetCovered before.natSuccStuck after.natSuccStuck
  , hashMapCovered before.isPropCache after.isPropCache
  , hashMapCovered before.isRecCache after.isRecCache
  , hashMapCovered before.recursorCache after.recursorCache
  , hashMapCovered before.recMajorsCache after.recMajorsCache
  , hashSetCovered before.blockPeerAgreementCache
      after.blockPeerAgreementCache
  , successfulBlockResultsCovered before.blockCheckResults
      after.blockCheckResults ]

private theorem familyMemberRulePopulationCacheChecksNative :
    familyMemberRulePopulationCacheChecks.all id = true := by
  native_decide

private theorem familyMemberRulePopulationCacheCheck {check : Bool}
    (hmem : check ∈ familyMemberRulePopulationCacheChecks) : check = true :=
  (List.all_eq_true.mp familyMemberRulePopulationCacheChecksNative) check hmem

private theorem familyMemberRulePopulationCacheEntries
    {entry : CacheEntry}
    (hentry : familyMemberRulePopulationAfter.env.HasCacheEntry entry) :
    familyMemberInitial.env.HasCacheEntry entry := by
  cases hentry with
  | whnf hget =>
      exact .whnf <| hashMapCovered_get?
        (before := familyMemberInitial.env.whnfCache)
        (after := familyMemberRulePopulationAfter.env.whnfCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget
  | whnfNoDelta hget =>
      exact .whnfNoDelta <| hashMapCovered_get?
        (before := familyMemberInitial.env.whnfNoDeltaCache)
        (after := familyMemberRulePopulationAfter.env.whnfNoDeltaCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget
  | whnfNoDeltaCheap hget =>
      exact .whnfNoDeltaCheap <| hashMapCovered_get?
        (before := familyMemberInitial.env.whnfNoDeltaCheapCache)
        (after := familyMemberRulePopulationAfter.env.whnfNoDeltaCheapCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget
  | whnfCore hget =>
      exact .whnfCore <| hashMapCovered_get?
        (before := familyMemberInitial.env.whnfCoreCache)
        (after := familyMemberRulePopulationAfter.env.whnfCoreCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget
  | whnfCoreCheap hget =>
      exact .whnfCoreCheap <| hashMapCovered_get?
        (before := familyMemberInitial.env.whnfCoreCheapCache)
        (after := familyMemberRulePopulationAfter.env.whnfCoreCheapCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget
  | infer hget =>
      exact .infer <| hashMapCovered_get?
        (before := familyMemberInitial.env.inferCache)
        (after := familyMemberRulePopulationAfter.env.inferCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget
  | inferOnly hget =>
      exact .inferOnly <| hashMapCovered_get?
        (before := familyMemberInitial.env.inferOnlyCache)
        (after := familyMemberRulePopulationAfter.env.inferOnlyCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget
  | defEq hget =>
      exact .defEq <| hashMapCovered_get?
        (before := familyMemberInitial.env.defEqCache)
        (after := familyMemberRulePopulationAfter.env.defEqCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget
  | defEqCheap hget =>
      exact .defEqCheap <| hashMapCovered_get?
        (before := familyMemberInitial.env.defEqCheapCache)
        (after := familyMemberRulePopulationAfter.env.defEqCheapCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget
  | defEqFailure hmem =>
      exact .defEqFailure <| hashSetCovered_contains
        (before := familyMemberInitial.env.defEqFailure)
        (after := familyMemberRulePopulationAfter.env.defEqFailure)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hmem
  | unfold hget =>
      exact .unfold <| hashMapCovered_get?
        (before := familyMemberInitial.env.unfoldCache)
        (after := familyMemberRulePopulationAfter.env.unfoldCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget
  | natSuccStuck hmem =>
      exact .natSuccStuck <| hashSetCovered_contains
        (before := familyMemberInitial.env.natSuccStuck)
        (after := familyMemberRulePopulationAfter.env.natSuccStuck)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hmem
  | isProp hget =>
      exact .isProp <| hashMapCovered_get?
        (before := familyMemberInitial.env.isPropCache)
        (after := familyMemberRulePopulationAfter.env.isPropCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget
  | isRec hget =>
      exact .isRec <| hashMapCovered_get?
        (before := familyMemberInitial.env.isRecCache)
        (after := familyMemberRulePopulationAfter.env.isRecCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget
  | recursor hget =>
      exact .recursor <| hashMapCovered_get?
        (before := familyMemberInitial.env.recursorCache)
        (after := familyMemberRulePopulationAfter.env.recursorCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget
  | recMajors hget =>
      exact .recMajors <| hashMapCovered_get?
        (before := familyMemberInitial.env.recMajorsCache)
        (after := familyMemberRulePopulationAfter.env.recMajorsCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget
  | blockPeer hmem =>
      exact .blockPeer <| hashSetCovered_contains
        (before := familyMemberInitial.env.blockPeerAgreementCache)
        (after := familyMemberRulePopulationAfter.env.blockPeerAgreementCache)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hmem
  | blockResult hget =>
      exact .blockResult <| successfulBlockResultsCovered_get?
        (before := familyMemberInitial.env.blockCheckResults)
        (after := familyMemberRulePopulationAfter.env.blockCheckResults)
        (familyMemberRulePopulationCacheCheck (by
          simp [familyMemberRulePopulationCacheChecks])) hget

private def familyMemberRulePopulationUnivKeys : Bool :=
  familyMemberRulePopulationAfter.env.intern.univs.toList.all
    (fun entry => decide (entry.2.addr = entry.1))

private def familyMemberRulePopulationExprKeys : Bool :=
  familyMemberRulePopulationAfter.env.intern.exprs.toList.all
    (fun entry => decide (entry.2.internKey = entry.1))

private def familyMemberRulePopulationExtends : Bool :=
  familyMemberInitial.env.intern.exprs.toList.all fun entry =>
    decide (familyMemberRulePopulationAfter.env.intern.exprs[entry.1]? =
      some entry.2)

private theorem familyMemberRulePopulationUnivKeysNative :
    familyMemberRulePopulationUnivKeys = true := by
  native_decide

private theorem familyMemberRulePopulationExprKeysNative :
    familyMemberRulePopulationExprKeys = true := by
  native_decide

private theorem familyMemberRulePopulationExtendsNative :
    familyMemberRulePopulationExtends = true := by
  native_decide

/-- Hash-consing key coherence after the exact rule-population execution. -/
theorem familyMemberRulePopulationInternWF :
    familyMemberRulePopulationAfter.env.intern.WF := by
  apply InternTable.WF.of_toList
  · intro address univ hmem
    have hall := familyMemberRulePopulationUnivKeysNative
    unfold familyMemberRulePopulationUnivKeys at hall
    rw [List.all_eq_true] at hall
    exact of_decide_eq_true (hall (address, univ) hmem)
  · intro address expression hmem
    have hall := familyMemberRulePopulationExprKeysNative
    unfold familyMemberRulePopulationExprKeys at hall
    rw [List.all_eq_true] at hall
    exact of_decide_eq_true (hall (address, expression) hmem)

/-- Rule population retains every ingress expression binding at its original
address.  This fact is public because the concrete run-support collision proof
uses the post-population table as one common canonical range. -/
theorem familyMemberRulePopulationExprExtends :
    familyMemberInitial.env.intern.ExprExtends
      familyMemberRulePopulationAfter.env.intern := by
  apply InternTable.ExprExtends.of_toList
  intro address expression hmem
  have hall := familyMemberRulePopulationExtendsNative
  unfold familyMemberRulePopulationExtends at hall
  rw [List.all_eq_true] at hall
  exact of_decide_eq_true (hall (address, expression) hmem)

/-- Extensional state facts consumed by `InternSemanticFrame`.  The map
checks are range-inclusion statements; the remaining checks compare only
fields that the ordinary kernel invariant actually observes. -/
private def familyMemberRulePopulationSemanticChecks : List Bool :=
  let before := familyMemberInitial
  let after := familyMemberRulePopulationAfter
  [ hashMapCovered before.env.consts after.env.consts
  , hashMapCovered before.env.blocks after.env.blocks
  , hashMapCovered before.env.intern.univs after.env.intern.univs
  , hashMapCovered before.equivManager.keyToNode
      after.equivManager.keyToNode
  , decide (after.equivManager.parent = before.equivManager.parent)
  , decide (after.equivManager.nodeToKey = before.equivManager.nodeToKey)
  , decide (after.prims.addressTable = before.prims.addressTable)
  , decide (after.noAccel = before.noAccel)
  , decide (after.ctx = before.ctx)
  , decide (after.letVals = before.letVals)
  , decide (after.numLetBindings = before.numLetBindings)
  , decide (after.lctx.decls = before.lctx.decls)
  , hashMapCovered before.lctx.index after.lctx.index
  , decide (before.env.nextFVarId.toNat ≤ after.env.nextFVarId.toNat) ]

private theorem familyMemberRulePopulationSemanticChecksNative :
    familyMemberRulePopulationSemanticChecks.all id = true := by
  native_decide

private theorem familyMemberRulePopulationSemanticCheck {check : Bool}
    (hmem : check ∈ familyMemberRulePopulationSemanticChecks) : check = true :=
  (List.all_eq_true.mp familyMemberRulePopulationSemanticChecksNative) check hmem

private theorem familyMemberRulePopulationSemanticFact
    {proposition : Prop} [Decidable proposition]
    (hmem : decide proposition ∈ familyMemberRulePopulationSemanticChecks) :
    proposition :=
  of_decide_eq_true (familyMemberRulePopulationSemanticCheck hmem)

private theorem familyMemberRulePopulationConsts
    {id : KId .anon} {constant : KConst .anon}
    (hget : familyMemberRulePopulationAfter.env.get? id = some constant) :
    familyMemberInitial.env.get? id = some constant := by
  apply hashMapCovered_get?
    (before := familyMemberInitial.env.consts)
    (after := familyMemberRulePopulationAfter.env.consts)
    (familyMemberRulePopulationSemanticCheck (by
      simp [familyMemberRulePopulationSemanticChecks]))
  simpa [KEnv.get?] using hget

private theorem familyMemberRulePopulationBlocks
    {block : KId .anon} {members : Array (KId .anon)}
    (hget : familyMemberRulePopulationAfter.env.blocks[block]? =
      some members) :
    familyMemberInitial.env.blocks[block]? = some members := by
  exact hashMapCovered_get?
    (before := familyMemberInitial.env.blocks)
    (after := familyMemberRulePopulationAfter.env.blocks)
    (familyMemberRulePopulationSemanticCheck (by
      simp [familyMemberRulePopulationSemanticChecks])) hget

private theorem familyMemberRulePopulationUnivsCovered
    {univ : KUniv .anon}
    (hsupport : familyMemberRulePopulationAfter.env.intern.UnivSupport univ) :
    familyMemberInitial.env.intern.UnivSupport univ := by
  obtain ⟨address, hget⟩ := hsupport
  exact ⟨address, hashMapCovered_get?
    (before := familyMemberInitial.env.intern.univs)
    (after := familyMemberRulePopulationAfter.env.intern.univs)
    (familyMemberRulePopulationSemanticCheck (by
      simp [familyMemberRulePopulationSemanticChecks])) hget⟩

private theorem familyMemberRulePopulationEquivalences
    {relation : EqKey → EqKey → Prop}
    (hbefore : EquivManager.WF relation familyMemberInitial.equivManager) :
    EquivManager.WF relation familyMemberRulePopulationAfter.equivManager := by
  have hparent : familyMemberRulePopulationAfter.equivManager.parent =
      familyMemberInitial.equivManager.parent :=
    familyMemberRulePopulationSemanticFact (by
      simp [familyMemberRulePopulationSemanticChecks])
  have hlabels : familyMemberRulePopulationAfter.equivManager.nodeToKey =
      familyMemberInitial.equivManager.nodeToKey :=
    familyMemberRulePopulationSemanticFact (by
      simp [familyMemberRulePopulationSemanticChecks])
  refine ⟨?_, ?_⟩
  · simpa only [hparent, hlabels] using hbefore.parents
  · intro key node hget
    have hgetBefore := hashMapCovered_get?
      (before := familyMemberInitial.equivManager.keyToNode)
      (after := familyMemberRulePopulationAfter.equivManager.keyToNode)
      (familyMemberRulePopulationSemanticCheck (by
        simp [familyMemberRulePopulationSemanticChecks])) hget
    simpa only [hparent, hlabels] using hbefore.keyToNode hgetBefore

private theorem familyMemberRulePopulationLctxWF
    (hbefore : familyMemberInitial.lctx.WF) :
    familyMemberRulePopulationAfter.lctx.WF := by
  have hdecls : familyMemberRulePopulationAfter.lctx.decls =
      familyMemberInitial.lctx.decls :=
    familyMemberRulePopulationSemanticFact (by
      simp [familyMemberRulePopulationSemanticChecks])
  constructor
  intro fvar index hget
  have hgetBefore := hashMapCovered_get?
    (before := familyMemberInitial.lctx.index)
    (after := familyMemberRulePopulationAfter.lctx.index)
    (familyMemberRulePopulationSemanticCheck (by
      simp [familyMemberRulePopulationSemanticChecks])) hget
  obtain ⟨declaration, hdeclaration⟩ := hbefore.sound hgetBefore
  exact ⟨declaration, by simpa only [hdecls] using hdeclaration⟩

/-- Population grows the intern table and the fresh-id counter while framing
loaded declarations and every semantic cache extensionally.  Its temporary
local-context entries are gone from the declaration stack; the possibly
different hash-map bucket layout is validated by lookup inclusion. -/
private theorem familyMemberRulePopulationFrame :
    ScopedWhnfStateInv.InternSemanticFrame familyMemberInitial
      familyMemberRulePopulationAfter where
  consts := familyMemberRulePopulationConsts
  blocks := familyMemberRulePopulationBlocks
  cacheEntries := familyMemberRulePopulationCacheEntries
  equivalences := familyMemberRulePopulationEquivalences
  primitiveAddresses := familyMemberRulePopulationSemanticFact (by
    simp [familyMemberRulePopulationSemanticChecks])
  noAccel := familyMemberRulePopulationSemanticFact (by
    simp [familyMemberRulePopulationSemanticChecks])
  ctx := familyMemberRulePopulationSemanticFact (by
    simp [familyMemberRulePopulationSemanticChecks])
  letVals := familyMemberRulePopulationSemanticFact (by
    simp [familyMemberRulePopulationSemanticChecks])
  numLetBindings := familyMemberRulePopulationSemanticFact (by
    simp [familyMemberRulePopulationSemanticChecks])
  lctxDecls := familyMemberRulePopulationSemanticFact (by
    simp [familyMemberRulePopulationSemanticChecks])
  lctxWF := familyMemberRulePopulationLctxWF
  nextFVarId := familyMemberRulePopulationSemanticFact (by
    simp [familyMemberRulePopulationSemanticChecks])

private def familyMemberRulePopulationNoLazy : Bool :=
  match familyMemberRulePopulationAfter.lazyFault with
  | none => true
  | some _ => false

private theorem familyMemberRulePopulationNoLazyNative :
    familyMemberRulePopulationNoLazy = true := by
  native_decide

private theorem familyMemberRulePopulationLazyFault :
    familyMemberRulePopulationAfter.lazyFault = none := by
  have noLazy := familyMemberRulePopulationNoLazyNative
  unfold familyMemberRulePopulationNoLazy at noLazy
  cases lazy : familyMemberRulePopulationAfter.lazyFault with
  | none => rfl
  | some fault =>
      rw [lazy] at noLazy
      contradiction

/-- Rule population restores the empty declaration stack and does not install
a lazy-ingress hook, so both endpoints inhabit the same closed-context suffix
domain even though fresh ids and intern maps have advanced. -/
theorem familyMemberRulePopulation_closed :
    ClosedContextState familyMemberRulePopulationAfter where
  ctx := familyMemberRulePopulationFrame.ctx.trans
    familyMemberInitial_closed.ctx
  letVals := familyMemberRulePopulationFrame.letVals.trans
    familyMemberInitial_closed.letVals
  numLetBindings := familyMemberRulePopulationFrame.numLetBindings.trans
    familyMemberInitial_closed.numLetBindings
  lctxDecls := familyMemberRulePopulationFrame.lctxDecls.trans
    familyMemberInitial_closed.lctxDecls
  lctxWF := familyMemberRulePopulationFrame.lctxWF
    familyMemberInitial_closed.lctxWF
  lazyFault := familyMemberRulePopulationLazyFault

theorem familyMemberModel_populationInScope :
    familyMemberModel.StateInScope familyMemberRulePopulationAfter :=
  ClosedContextDigest.model_stateInScope familyMemberRulePopulation_closed

theorem familyMemberModel_populationScopeTransition :
    familyMemberModel.StateInScope familyMemberInitial →
      familyMemberModel.StateInScope familyMemberRulePopulationAfter :=
  fun _ => familyMemberModel_populationInScope

/-- The concrete callback-bearing population core preserves the scoped
invariant using only support for its finite new-expression delta.  No WHNF,
DefEq, or whole-core preservation premise remains. -/
theorem familyMemberRulePopulationCore_scoped_wf
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport}
    (scopeTransition : model.StateInScope familyMemberInitial →
      model.StateInScope familyMemberRulePopulationAfter)
    (newSupported : ∀ expression, FamilyMemberPopulationNewExpr expression →
      support expression) :
    TcM.WF (ScopedWhnfStateInv model layer semantics support [])
      familyMemberInitial
      ((RecM.populateRecursorRulesFromBlockCore familyBlockId recursorBlockId
        familyGeneratedSnapshot).run checkerMethods)
      (fun generated after => generated = familyGeneratedWithRules ∧
        after = familyMemberRulePopulationAfter) := by
  intro hI
  rw [familyMemberRulePopulationRun]
  have hcover : support.CoversIntern
      familyMemberRulePopulationAfter.env.intern := by
    constructor
    · intro expression hsupport
      obtain ⟨address, hafter⟩ := hsupport
      cases hbeforeLookup : familyMemberInitial.env.intern.exprs[address]? with
      | none =>
          exact newSupported expression ⟨address, hafter, hbeforeLookup⟩
      | some old =>
          have hold := familyMemberRulePopulationExprExtends hbeforeLookup
          rw [hafter] at hold
          cases hold
          exact hI.1.1.internSupport.expr expression
            ⟨address, hbeforeLookup⟩
    · intro univ hsupport
      exact hI.1.1.internSupport.univ univ
        (familyMemberRulePopulationUnivsCovered hsupport)
  exact ⟨ScopedWhnfStateInv.of_internSemanticFrame
      familyMemberRulePopulationFrame familyMemberRulePopulationInternWF
        hcover scopeTransition hI,
    rfl, rfl⟩

/-- Active-block counterpart of the finite population-core proof.  The core
itself creates no semantic cache entry, so its extensional frame transports
the coordinated authority unchanged while the intern table grows by the
same finite delta. -/
theorem familyMemberRulePopulationCore_activeScoped_wf
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport}
    (scopeTransition : model.StateInScope familyMemberInitial →
      model.StateInScope familyMemberRulePopulationAfter)
    (newSupported : ∀ expression, FamilyMemberPopulationNewExpr expression →
      support expression) :
    TcM.WF (ScopedActiveWhnfStateInv model layer semantics support
      recursorMembers []) familyMemberInitial
      ((RecM.populateRecursorRulesFromBlockCore familyBlockId recursorBlockId
        familyGeneratedSnapshot).run checkerMethods)
      (fun generated after => generated = familyGeneratedWithRules ∧
        after = familyMemberRulePopulationAfter) := by
  intro hI
  rw [familyMemberRulePopulationRun]
  have hcover : support.CoversIntern
      familyMemberRulePopulationAfter.env.intern := by
    constructor
    · intro expression hsupport
      obtain ⟨address, hafter⟩ := hsupport
      cases hbeforeLookup : familyMemberInitial.env.intern.exprs[address]? with
      | none =>
          exact newSupported expression ⟨address, hafter, hbeforeLookup⟩
      | some old =>
          have hold := familyMemberRulePopulationExprExtends hbeforeLookup
          rw [hafter] at hold
          cases hold
          exact hI.active.internSupport.expr expression
            ⟨address, hbeforeLookup⟩
    · intro univ hsupport
      exact hI.active.internSupport.univ univ
        (familyMemberRulePopulationUnivsCovered hsupport)
  exact ⟨ScopedActiveWhnfStateInv.of_internSemanticFrame
      familyMemberRulePopulationFrame familyMemberRulePopulationInternWF
        hcover scopeTransition hI,
    rfl, rfl⟩

private theorem familyMemberInitialGeneratedCache :
    familyMemberInitial.env.recursorCache[familyBlockId]? =
      some familyGeneratedSnapshot := by
  simpa [familyMemberInitial, TcState.withBlockCheckResult] using
    familyGeneratedSnapshotLookup

/-- On the concrete cache hit, the public operation is exactly the verified
population core followed by its transactional commit. -/
private theorem familyMemberRulePopulationDecomposition :
    (RecM.populateRecursorRulesFromBlock familyBlockId recursorBlockId).run
        checkerMethods familyMemberInitial =
      EStateM.bind
        ((RecM.populateRecursorRulesFromBlockCore familyBlockId recursorBlockId
          familyGeneratedSnapshot).run checkerMethods)
        (fun generatedWithRules state =>
          (RecM.commitGeneratedRecursorRulesAt familyBlockId
            familyGeneratedSnapshot generatedWithRules).run checkerMethods
              state)
        familyMemberInitial := by
  unfold RecM.populateRecursorRulesFromBlock
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _
    familyMemberInitial = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) familyMemberInitial =
    .ok familyMemberInitial familyMemberInitial from rfl]
  simp only [familyMemberInitialGeneratedCache, ReaderT.run_bind]
  rfl

/-- The complete public population transaction preserves the production
inductive-cache invariant.  Its only external obligations are the finite
expressions newly interned by rule construction, the exact suffix-domain
transition caused by fresh-id consumption, and ordinary trusted-reference
provenance for the installed batch. -/
theorem familyMemberRulePopulation_scoped_wf
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {support : RunSupport}
    (trustedReferences : RecM.TrustedReferences familyAcceptedWorld support)
    (scopeTransition : model.StateInScope familyMemberInitial →
      model.StateInScope familyMemberRulePopulationAfter)
    (newSupported : ∀ expression, FamilyMemberPopulationNewExpr expression →
      support expression)
    (initialInvariant : ScopedWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support [] familyMemberInitial) :
    TcM.WF (ScopedWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support []) familyMemberInitial
      ((RecM.populateRecursorRulesFromBlock familyBlockId
        recursorBlockId).run checkerMethods)
      (fun _ _ => True) := by
  intro hI
  rw [familyMemberRulePopulationDecomposition]
  have composed : TcM.WF (ScopedWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support []) familyMemberInitial
      (EStateM.bind
        ((RecM.populateRecursorRulesFromBlockCore familyBlockId recursorBlockId
          familyGeneratedSnapshot).run checkerMethods)
        (fun generatedWithRules =>
          (RecM.commitGeneratedRecursorRulesAt familyBlockId
            familyGeneratedSnapshot generatedWithRules).run checkerMethods))
      (fun _ _ => True) := by
    apply TcM.WF.bind
      (Q₁ := fun generated after =>
        generated = familyGeneratedWithRules ∧
          after = familyMemberRulePopulationAfter)
      (familyMemberRulePopulationCore_scoped_wf scopeTransition newSupported)
    intro generated after hpost
    ·
      rcases hpost with ⟨rfl, rfl⟩
      exact familyGeneratedRuleCommit_scoped_wf trustedReferences
        initialInvariant familyMemberRulePopulationAfter
  exact composed hI

/-- Complete non-vacuous recursive population transaction.  The finite core
frames coordinated authority and the final commit installs the self-
referential rule batch under that same authority. -/
theorem familyMemberRulePopulation_activeScoped_wf
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {support : RunSupport}
    (authorizedReferences : RecM.AuthorizedReferences
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      support)
    (scopeTransition : model.StateInScope familyMemberInitial →
      model.StateInScope familyMemberRulePopulationAfter)
    (newSupported : ∀ expression, FamilyMemberPopulationNewExpr expression →
      support expression)
    (initialInvariant : ScopedActiveWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support recursorMembers [] familyMemberInitial) :
    TcM.WF (ScopedActiveWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support recursorMembers []) familyMemberInitial
      ((RecM.populateRecursorRulesFromBlock familyBlockId
        recursorBlockId).run checkerMethods)
      (fun _ _ => True) := by
  intro hI
  rw [familyMemberRulePopulationDecomposition]
  have composed : TcM.WF (ScopedActiveWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support recursorMembers []) familyMemberInitial
      (EStateM.bind
        ((RecM.populateRecursorRulesFromBlockCore familyBlockId recursorBlockId
          familyGeneratedSnapshot).run checkerMethods)
        (fun generatedWithRules =>
          (RecM.commitGeneratedRecursorRulesAt familyBlockId
            familyGeneratedSnapshot generatedWithRules).run checkerMethods))
      (fun _ _ => True) := by
    apply TcM.WF.bind
      (Q₁ := fun generated after =>
        generated = familyGeneratedWithRules ∧
          after = familyMemberRulePopulationAfter)
      (familyMemberRulePopulationCore_activeScoped_wf scopeTransition
        newSupported)
    intro generated after hpost
    rcases hpost with ⟨rfl, rfl⟩
    exact familyGeneratedRuleCommit_activeScoped_wf authorizedReferences
      initialInvariant familyMemberRulePopulationAfter
  exact composed hI

/-- Exact stored declaration captured before any callback-bearing prelude
stage. -/
def familyExpectedMemberSnapshot :
    RecM.RecursorMemberDeclarationSnapshot .anon where
  recBlock := recursorBlockId
  ty := recursorConcrete.ty
  declaredK := false
  declaredLvls := 2
  declaredIsUnsafe := false
  params := 1
  motives := 1
  minors := 2
  indices := 1
  storedRules := recursorRules
  majorSkip := 5

def familyMemberSnapshotOutcome :=
  (RecM.snapshotRecursorMemberDeclaration recursorId).run checkerMethods
    familyMemberInitial

def familyMemberSnapshotAfter : TcState .anon :=
  match familyMemberSnapshotOutcome with
  | .ok _ after => after
  | .error _ failed => failed

/-- The major-telescope scan is retained separately from the coordinated
inductive cache check that follows it. -/
def familyMemberOwnerOutcome :=
  (RecM.getMajorInductiveId familyExpectedMemberSnapshot.ty
    familyExpectedMemberSnapshot.majorSkip).run checkerMethods
      familyMemberSnapshotAfter

def familyMemberOwnerAfter : TcState .anon :=
  match familyMemberOwnerOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyMemberMajorOutcome :=
  (RecM.validateRecursorMemberMajor familyExpectedMemberSnapshot).run
    checkerMethods familyMemberSnapshotAfter

def familyMemberMajorAfter : TcState .anon :=
  match familyMemberMajorOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyUsableBlockOutcome :=
  (RecM.findUsableGeneratedRecursorBlock familyExpectedMemberSnapshot
    familyId).run checkerMethods familyMemberMajorAfter

def familyUsableBlockAfter : TcState .anon :=
  match familyUsableBlockOutcome with
  | .ok _ after => after
  | .error _ failed => failed

/-! ### Exact major-telescope restoration -/

/-- The concrete recursive method table takes the production read-only WHNF
quick exit on every forall inspected by major discovery. -/
theorem checkerMethods_forallWhnfPure :
    RecM.ForallWhnfPure checkerMethods := by
  intro name bi dom body info state
  rfl

/-- Small, syntax-only certificate: after the stored five-binder prefix, the
next forall domain has the indexed family as its constant head. -/
def familyMemberDirectMajorShape : Bool :=
  decide (RecM.directMajorAfterForalls
    familyExpectedMemberSnapshot.majorSkip.toNat
    familyExpectedMemberSnapshot.ty = some familyId)

private theorem familyMemberDirectMajorShapeNative :
    familyMemberDirectMajorShape = true := by
  native_decide

theorem familyMemberDirectMajorShapeExact :
    RecM.directMajorAfterForalls
      familyExpectedMemberSnapshot.majorSkip.toNat
      familyExpectedMemberSnapshot.ty = some familyId := by
  exact of_decide_eq_true familyMemberDirectMajorShapeNative

/-- Finite eager lookup required by the direct-major theorem.  This decides
only the physically stored family declaration, not any checker-state
equivalence. -/
private theorem familyMemberSnapshotFamilyLoaded :
    familyMemberSnapshotAfter.env.get? familyId = some familyConcrete := by
  native_decide

/-- Boolean projections deliberately compare only returned values, never the
large mutable checker states. -/
def familyMemberSnapshotMatches : Bool :=
  match familyMemberSnapshotOutcome with
  | .error _ _ => false
  | .ok snapshot _ => decide (snapshot = familyExpectedMemberSnapshot)

def familyMemberOwnerMatches : Bool :=
  match familyMemberOwnerOutcome with
  | .error _ _ => false
  | .ok indId _ => decide (indId = familyId)

/-- Exact finite reads needed to justify the coordinated family-cache hit
after the major telescope has been restored. -/
def familyMemberOwnerReadsMatch : Bool := decide (
  familyMemberOwnerAfter.env.get? familyId = some familyConcrete ∧
  familyMemberOwnerAfter.env.getBlock? familyBlockId = some familyMembers ∧
  familyMemberOwnerAfter.env.get? nilId = some nilConcrete ∧
  familyMemberOwnerAfter.env.get? consId = some consConcrete)

def familyMemberOwnerBlockResultMatches : Bool :=
  match familyMemberOwnerAfter.env.blockCheckResults[familyBlockId]? with
  | some (.ok ()) => true
  | _ => false

def familyMemberOwnerCacheMatches : Bool :=
  familyMemberOwnerMatches &&
    (familyMemberOwnerReadsMatch && familyMemberOwnerBlockResultMatches)

private theorem familyMemberOwnerCacheMatchesNative :
    familyMemberOwnerCacheMatches = true := by
  native_decide

def familyMemberMajorMatches : Bool :=
  match familyMemberMajorOutcome with
  | .error _ _ => false
  | .ok indId _ => decide (indId = familyId)

def familyUsableBlockMatches : Bool :=
  match familyUsableBlockOutcome with
  | .error _ _ => false
  | .ok block _ => decide (block = some familyBlockId)

/-- One native computation decides only the three returned prefix values;
the state equations below retain the actual state threaded by each stage. -/
def familyMemberResolutionPrefixMatches : Bool :=
  familyMemberSnapshotMatches &&
    (familyMemberMajorMatches && familyUsableBlockMatches)

private theorem familyMemberResolutionPrefixMatchesNative :
    familyMemberResolutionPrefixMatches = true := by
  native_decide

/-- The stored recursor has the exact constructor fields consumed by the
declaration snapshot.  The member index is retained here even though the
snapshot deliberately omits it. -/
private theorem familyMemberRecursorConcreteHeader :
    recursorConcrete =
      .recr () () false false 2 1 1 1 2 recursorBlockId 0
        recursorConcrete.ty recursorRules () := by
  native_decide

private theorem familyMemberInitialRecursorLoaded :
    familyMemberInitial.env.get? recursorId = some recursorConcrete := by
  native_decide

/-- The stored metadata sum is bounded and state-independent. -/
private theorem familyMemberMajorSkipRunNeutral (state : TcState .anon) :
    (RecM.checkedMetadataSum "recursor major index" #[1, 1, 2, 1]).run
      checkerMethods state = .ok 5 state := by
  unfold RecM.checkedMetadataSum RecM.checkedNatMetadataSum
  have bound : (5 : Nat) < UInt64.size := by native_decide
  simp [bound]

/-- Freezing the eagerly loaded declaration and checking its metadata does
not mutate the concrete member-check state. -/
theorem familyMemberSnapshotRunNeutral :
    (RecM.snapshotRecursorMemberDeclaration recursorId).run checkerMethods
      familyMemberInitial =
        .ok familyExpectedMemberSnapshot familyMemberInitial := by
  have lookup : TcM.getConst recursorId familyMemberInitial =
      .ok recursorConcrete familyMemberInitial := by
    unfold TcM.getConst
    change EStateM.bind (TcM.tryGetConst recursorId) _ familyMemberInitial = _
    unfold EStateM.bind
    rw [TcM.tryGetConst_loaded_run familyMemberInitialRecursorLoaded]
    rfl
  unfold RecM.snapshotRecursorMemberDeclaration
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.getConst recursorId) _ familyMemberInitial = _
  unfold EStateM.bind
  rw [lookup, familyMemberRecursorConcreteHeader]
  simp only
  change EStateM.bind
    ((RecM.checkedMetadataSum "recursor major index" #[1, 1, 2, 1]).run
      checkerMethods) _ familyMemberInitial = _
  unfold EStateM.bind
  rw [familyMemberMajorSkipRunNeutral]
  rfl

theorem familyMemberSnapshotRun :
    (RecM.snapshotRecursorMemberDeclaration recursorId).run checkerMethods
      familyMemberInitial =
        .ok familyExpectedMemberSnapshot familyMemberSnapshotAfter := by
  have hmatches := (Bool.and_eq_true_iff.mp
    familyMemberResolutionPrefixMatchesNative).1
  unfold familyMemberSnapshotMatches at hmatches
  unfold familyMemberSnapshotAfter
  generalize houtcome : familyMemberSnapshotOutcome = outcome at hmatches ⊢
  cases outcome <;> simp_all [familyMemberSnapshotOutcome]

theorem familyMemberSnapshotAfter_eq_initial :
    familyMemberSnapshotAfter = familyMemberInitial := by
  unfold familyMemberSnapshotAfter familyMemberSnapshotOutcome
  rw [familyMemberSnapshotRunNeutral]

/-- The production major traversal over the certified recursor telescope
returns the family and restores the complete pre-traversal checker state. -/
theorem familyMemberOwnerRunNeutral :
    (RecM.getMajorInductiveId familyExpectedMemberSnapshot.ty
      familyExpectedMemberSnapshot.majorSkip).run checkerMethods
        familyMemberSnapshotAfter =
      .ok familyId familyMemberSnapshotAfter := by
  apply RecM.getMajorInductiveId_direct_exact checkerMethods_forallWhnfPure
    familyMemberDirectMajorShapeExact
  have loaded := familyMemberSnapshotFamilyLoaded
  rw [familyConcreteHeader] at loaded
  exact ⟨_, _, _, _, _, _, _, _, loaded⟩

/-- Exact major owner returned before the coordinated family check. -/
theorem familyMemberOwnerRun :
    (RecM.getMajorInductiveId familyExpectedMemberSnapshot.ty
      familyExpectedMemberSnapshot.majorSkip).run checkerMethods
        familyMemberSnapshotAfter =
      .ok familyId familyMemberOwnerAfter := by
  have howner := (Bool.and_eq_true_iff.mp
    familyMemberOwnerCacheMatchesNative).1
  unfold familyMemberOwnerMatches at howner
  unfold familyMemberOwnerAfter
  generalize houtcome : familyMemberOwnerOutcome = outcome at howner ⊢
  cases outcome <;> simp_all [familyMemberOwnerOutcome]

/-- The old outcome projection names the same exact state now established
structurally by the telescope proof. -/
theorem familyMemberOwnerAfter_eq_snapshot :
    familyMemberOwnerAfter = familyMemberSnapshotAfter := by
  unfold familyMemberOwnerAfter familyMemberOwnerOutcome
  rw [familyMemberOwnerRunNeutral]

/-- The restored telescope state retains exactly the physical family block
needed by the coordinated cache shell. -/
theorem familyMemberOwnerReads :
    familyMemberOwnerAfter.env.get? familyId = some familyConcrete ∧
    familyMemberOwnerAfter.env.getBlock? familyBlockId = some familyMembers ∧
    familyMemberOwnerAfter.env.get? nilId = some nilConcrete ∧
    familyMemberOwnerAfter.env.get? consId = some consConcrete := by
  have hrest := (Bool.and_eq_true_iff.mp
    familyMemberOwnerCacheMatchesNative).2
  have hreads := (Bool.and_eq_true_iff.mp hrest).1
  exact of_decide_eq_true hreads

/-- The family acceptance verdict is still present after the major telescope
scan; the result is pattern-decoded without requiring `DecidableEq TcError`. -/
theorem familyMemberOwnerBlockResult :
    familyMemberOwnerAfter.env.blockCheckResults[familyBlockId]? =
      some (.ok ()) := by
  have hrest := (Bool.and_eq_true_iff.mp
    familyMemberOwnerCacheMatchesNative).2
  have hresult := (Bool.and_eq_true_iff.mp hrest).2
  unfold familyMemberOwnerBlockResultMatches at hresult
  generalize hlookup :
    familyMemberOwnerAfter.env.blockCheckResults[familyBlockId]? = result
      at hresult ⊢
  cases result with
  | none => contradiction
  | some result => cases result <;> simp_all

/-- Every source-ordered physical family member has the declaration class
required before a coordinated verdict may be consumed. -/
theorem familyMemberOwnerSupported :
    ∀ member ∈ familyMembers.toList, ∃ constant,
      familyMemberOwnerAfter.env.get? member = some constant ∧
        constant.IsInductiveBlockMember := by
  intro member hmember
  rw [familyMembers_eq] at hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with rfl | rfl | rfl
  · exact ⟨familyConcrete, familyMemberOwnerReads.1,
      KConst.isInductiveBlockMember_of_inductiveMemberOf familyOwner⟩
  · exact ⟨nilConcrete, familyMemberOwnerReads.2.2.1,
      KConst.isInductiveBlockMember_of_inductiveMemberOf nilOwner⟩
  · exact ⟨consConcrete, familyMemberOwnerReads.2.2.2,
      KConst.isInductiveBlockMember_of_inductiveMemberOf consOwner⟩

/-- The major-stage inductive replay is an exact read-only hit of the verdict
published for the already accepted family. -/
theorem familyMemberInductiveCheckRun :
    (RecM.checkInductive familyId).run checkerMethods familyMemberOwnerAfter =
      .ok () familyMemberOwnerAfter := by
  have root := familyMemberOwnerReads.1
  rw [familyConcreteHeader] at root
  exact RecM.checkInductive_cached_run checkerMethods root
    familyMemberOwnerReads.2.1 familyMemberOwnerSupported
      familyMemberOwnerBlockResult

/-- Structural execution of the complete major stage: telescope discovery,
the declaration-class guard, and the coordinated cache hit. -/
theorem familyMemberMajorRunExact :
    (RecM.validateRecursorMemberMajor familyExpectedMemberSnapshot).run
      checkerMethods familyMemberSnapshotAfter =
        .ok familyId familyMemberOwnerAfter := by
  have root := familyMemberOwnerReads.1
  rw [familyConcreteHeader] at root
  have rootLookup := TcM.tryGetConst_loaded_run root
  unfold RecM.validateRecursorMemberMajor
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.getMajorInductiveId familyExpectedMemberSnapshot.ty
      familyExpectedMemberSnapshot.majorSkip).run checkerMethods) _
        familyMemberSnapshotAfter = _
  unfold EStateM.bind
  rw [familyMemberOwnerRun]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
  change EStateM.bind (TcM.tryGetConst familyId) _
    familyMemberOwnerAfter = _
  unfold EStateM.bind
  rw [rootLookup]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.checkInductive familyId).run checkerMethods) _
      familyMemberOwnerAfter = _
  unfold EStateM.bind
  rw [familyMemberInductiveCheckRun]
  rfl

/-- The complete major stage is state-neutral: after exact telescope
restoration, the declaration guard and coordinated block verdict are eager,
read-only hits. -/
theorem familyMemberMajorRunNeutral :
    (RecM.validateRecursorMemberMajor familyExpectedMemberSnapshot).run
      checkerMethods familyMemberSnapshotAfter =
        .ok familyId familyMemberSnapshotAfter := by
  simpa only [familyMemberOwnerAfter_eq_snapshot] using
    familyMemberMajorRunExact

theorem familyMemberMajorRunFromInitialNeutral :
    (RecM.validateRecursorMemberMajor familyExpectedMemberSnapshot).run
      checkerMethods familyMemberInitial =
        .ok familyId familyMemberInitial := by
  simpa only [familyMemberSnapshotAfter_eq_initial] using
    familyMemberMajorRunNeutral

/-- The outcome projection for the complete major stage therefore names the
same checker state as the declaration snapshot. -/
theorem familyMemberMajorAfter_eq_snapshot :
    familyMemberMajorAfter = familyMemberSnapshotAfter := by
  unfold familyMemberMajorAfter familyMemberMajorOutcome
  rw [familyMemberMajorRunNeutral]

theorem familyMemberMajorRun :
    (RecM.validateRecursorMemberMajor familyExpectedMemberSnapshot).run
      checkerMethods familyMemberSnapshotAfter =
        .ok familyId familyMemberMajorAfter := by
  rw [familyMemberMajorRunExact]
  unfold familyMemberMajorAfter familyMemberMajorOutcome
  rw [familyMemberMajorRunExact]

/-- The generated cache entry consulted by block resolution is a physical
finite read from the restored snapshot state. -/
private theorem familyMemberSnapshotGeneratedCache :
    familyMemberSnapshotAfter.env.recursorCache[familyBlockId]? =
      some familyGeneratedSnapshot := by
  native_decide

/-- Structural execution of the usable-block query.  The declaration is
eagerly loaded, the generated batch has the required motive slot, and the
entire query is state-neutral. -/
theorem familyUsableBlockRunNeutral :
    (RecM.findUsableGeneratedRecursorBlock familyExpectedMemberSnapshot
      familyId).run checkerMethods familyMemberMajorAfter =
        .ok (some familyBlockId) familyMemberMajorAfter := by
  apply RecM.findUsableGeneratedRecursorBlock_loaded_run checkerMethods
  · rw [familyMemberMajorAfter_eq_snapshot]
    have loaded := familyMemberSnapshotFamilyLoaded
    rw [familyConcreteHeader] at loaded
    exact loaded
  · rw [familyMemberMajorAfter_eq_snapshot]
    exact familyMemberSnapshotGeneratedCache
  · simp [familyExpectedMemberSnapshot, familyGeneratedSnapshotSize]

theorem familyUsableBlockRun :
    (RecM.findUsableGeneratedRecursorBlock familyExpectedMemberSnapshot
      familyId).run checkerMethods familyMemberMajorAfter =
        .ok (some familyBlockId) familyUsableBlockAfter := by
  rw [familyUsableBlockRunNeutral]
  unfold familyUsableBlockAfter familyUsableBlockOutcome
  rw [familyUsableBlockRunNeutral]

/-- The query's outcome projection also names the unchanged major state. -/
theorem familyUsableBlockAfter_eq_major :
    familyUsableBlockAfter = familyMemberMajorAfter := by
  unfold familyUsableBlockAfter familyUsableBlockOutcome
  rw [familyUsableBlockRunNeutral]

/-- The production resolver immediately returns the witnessed fast-path block
and retains the exact reached checker state. -/
theorem familyMemberResolutionRunNeutral :
    (RecM.resolveRecursorMemberBlock familyExpectedMemberSnapshot
      familyId).run checkerMethods familyMemberMajorAfter =
        .ok familyBlockId familyMemberMajorAfter :=
  RecM.resolveRecursorMemberBlock_cached_run familyUsableBlockRunNeutral

theorem familyMemberResolutionRunFromInitialNeutral :
    (RecM.resolveRecursorMemberBlock familyExpectedMemberSnapshot
      familyId).run checkerMethods familyMemberInitial =
        .ok familyBlockId familyMemberInitial := by
  simpa only [familyMemberMajorAfter_eq_snapshot,
    familyMemberSnapshotAfter_eq_initial] using
      familyMemberResolutionRunNeutral

/-! ### Exact constructive K-target validation -/

/-- All physical declarations consumed by the K-target census remain eager
reads in the exact post-resolution state. -/
theorem familyMemberMajorReads :
    familyMemberMajorAfter.env.get? familyId = some familyConcrete ∧
    familyMemberMajorAfter.env.getBlock? familyBlockId = some familyMembers ∧
    familyMemberMajorAfter.env.get? nilId = some nilConcrete ∧
    familyMemberMajorAfter.env.get? consId = some consConcrete := by
  rw [familyMemberMajorAfter_eq_snapshot,
    ← familyMemberOwnerAfter_eq_snapshot]
  exact familyMemberOwnerReads

/-- Exact physical header of the nullary constructor used by the finite
block census. -/
private theorem familyNilConcreteHeader :
    nilConcrete =
      .ctor () () false 1 familyId 0 1 0 nilConcrete.ty := by
  native_decide

/-- Pure syntax certificate for the two-binder family telescope. -/
private theorem familyMemberResultSortShape :
    RecM.directResultSortAfterForalls 2 familyConcrete.ty =
      some familyResultLevel := by
  native_decide

/-- Result-sort discovery for the family is exactly state-neutral from any
caller state, not merely from the earlier validation fixture's state. -/
theorem familyMemberResultSortRunNeutral (state : TcState .anon) :
    (RecM.getResultSortLevel familyConcrete.ty 2).run checkerMethods state =
      .ok familyResultLevel state :=
  RecM.getResultSortLevel_direct_exact familyMemberResultSortShape

/-- The source-ordered family census is a sequence of four eager reads: one
block lookup followed by the family and its two constructors. -/
theorem familyMemberDiscoveryRunNeutral :
    (RecM.discoverBlockInductives familyBlockId).run checkerMethods
      familyMemberMajorAfter =
        .ok #[familyId] familyMemberMajorAfter := by
  rw [RecM.discoverBlockInductives_equation, ReaderT.run_bind,
    ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetBlock familyBlockId) _
    familyMemberMajorAfter = _
  unfold EStateM.bind
  rw [TcM.tryGetBlock_loaded_run familyMemberMajorReads.2.1]
  simp [familyMembers_eq]
  change EStateM.bind (TcM.tryGetConst familyId) _
    familyMemberMajorAfter = _
  unfold EStateM.bind
  rw [TcM.tryGetConst_loaded_run familyMemberMajorReads.1]
  rw [familyConcreteHeader]
  simp only
  change EStateM.bind (TcM.tryGetConst nilId) _
    familyMemberMajorAfter = _
  unfold EStateM.bind
  rw [TcM.tryGetConst_loaded_run familyMemberMajorReads.2.2.1]
  rw [familyNilConcreteHeader]
  simp only
  change EStateM.bind (TcM.tryGetConst consId) _
    familyMemberMajorAfter = _
  unfold EStateM.bind
  rw [TcM.tryGetConst_loaded_run familyMemberMajorReads.2.2.2]
  rw [consConcreteHeader]
  rfl

/-- The certified parameter/index metadata adds to two without overflow and
does not inspect or mutate checker state. -/
private theorem familyMemberArityBoundNative :
    (2 : Nat) < UInt64.size := by
  native_decide

theorem familyMemberArityRunNeutral (state : TcState .anon) :
    (RecM.checkedMetadataSum "inductive params + indices" #[1, 1]).run
      checkerMethods state = .ok 2 state := by
  unfold RecM.checkedMetadataSum RecM.checkedNatMetadataSum
  simp [familyMemberArityBoundNative]

/-- The indexed family lives above `Prop`; this is the decisive non-K branch
after result-sort discovery. -/
private theorem familyMemberResultLevelNonzero :
    (!univEq familyResultLevel (.mkZero : KUniv .anon)) = true := by
  native_decide

private theorem familyMemberSingletonSizeNative :
    (#[familyId].size != 1) = false := by
  native_decide

/-- Exact execution of the production constructive K classifier.  The loaded
family is singleton at the inductive level, its arity is two, and its direct
result sort is nonzero, so the classifier returns before constructor-field
inspection.  Every executed stage is state-neutral. -/
theorem familyMemberComputeKTargetRunNeutral :
    (RecM.computeKTarget familyId).run checkerMethods familyMemberMajorAfter =
      .ok false familyMemberMajorAfter := by
  unfold RecM.computeKTarget
  rw [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
  change EStateM.bind (TcM.tryGetConst familyId) _
    familyMemberMajorAfter = _
  unfold EStateM.bind
  rw [TcM.tryGetConst_loaded_run familyMemberMajorReads.1]
  rw [familyConcreteHeader]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.discoverBlockInductives familyBlockId).run checkerMethods) _
      familyMemberMajorAfter = _
  unfold EStateM.bind
  rw [familyMemberDiscoveryRunNeutral]
  simp only
  rw [familyMemberSingletonSizeNative]
  simp only [Bool.false_eq_true, if_false]
  change EStateM.bind
    ((RecM.checkedMetadataSum "inductive params + indices" #[1, 1]).run
      checkerMethods) _ familyMemberMajorAfter = _
  unfold EStateM.bind
  rw [familyMemberArityRunNeutral]
  simp only
  have arityNat : UInt64.toNat (2 : UInt64) = 2 := by decide
  rw [arityNat]
  change EStateM.bind
    ((RecM.getResultSortLevel familyConcrete.ty 2).run checkerMethods) _
      familyMemberMajorAfter = _
  unfold EStateM.bind
  rw [familyMemberResultSortRunNeutral]
  simp [familyMemberResultLevelNonzero]
  rfl

/-- The stored recursor declares the same non-K bit computed above, so the
production comparison succeeds without changing state. -/
theorem familyMemberKTargetRunNeutral :
    (RecM.validateRecursorMemberKTarget familyExpectedMemberSnapshot
      familyId).run checkerMethods familyMemberMajorAfter =
        .ok false familyMemberMajorAfter := by
  unfold RecM.validateRecursorMemberKTarget
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((RecM.computeKTarget familyId).run checkerMethods) _
      familyMemberMajorAfter = _
  unfold EStateM.bind
  rw [familyMemberComputeKTargetRunNeutral]
  rfl

theorem familyMemberKTargetRunFromInitialNeutral :
    (RecM.validateRecursorMemberKTarget familyExpectedMemberSnapshot
      familyId).run checkerMethods familyMemberInitial =
        .ok false familyMemberInitial := by
  simpa only [familyMemberMajorAfter_eq_snapshot,
    familyMemberSnapshotAfter_eq_initial] using familyMemberKTargetRunNeutral

/-- Every production-reachable K-target stage for this fixture is the exact
state-neutral non-K run above. -/
theorem familyMemberKTarget_reachable_wf {I : TcState .anon → Prop} :
    ∀ snapshot afterSnapshot indId afterMajor resolvedBlock afterResolution,
      (RecM.snapshotRecursorMemberDeclaration recursorId).run checkerMethods
          familyMemberInitial = .ok snapshot afterSnapshot →
      (RecM.validateRecursorMemberMajor snapshot).run checkerMethods
          afterSnapshot = .ok indId afterMajor →
      (RecM.resolveRecursorMemberBlock snapshot indId).run checkerMethods
          afterMajor = .ok resolvedBlock afterResolution →
      TcM.WF I afterResolution
        ((RecM.validateRecursorMemberKTarget snapshot indId).run
          checkerMethods)
        (fun _ _ => True) := by
  intro snapshot afterSnapshot indId afterMajor resolvedBlock afterResolution
    snapshotRun majorRun resolutionRun
  rw [familyMemberSnapshotRun] at snapshotRun
  cases snapshotRun
  rw [familyMemberMajorRun] at majorRun
  cases majorRun
  rw [familyMemberResolutionRunNeutral] at resolutionRun
  cases resolutionRun
  intro invariant
  rw [familyMemberKTargetRunNeutral]
  exact ⟨invariant, trivial⟩

/-- Every production-reachable population stage is the exact concrete cache
hit closed above.  The preceding snapshot, major, resolution, and K-target
stages are all state-neutral, so no arbitrary-state population contract is
needed. -/
theorem familyMemberPopulation_reachable_scoped_wf
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {support : RunSupport}
    (trustedReferences : RecM.TrustedReferences familyAcceptedWorld support)
    (scopeTransition : model.StateInScope familyMemberInitial →
      model.StateInScope familyMemberRulePopulationAfter)
    (newSupported : ∀ expression, FamilyMemberPopulationNewExpr expression →
      support expression)
    (initialInvariant : ScopedWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support [] familyMemberInitial) :
    ∀ snapshot afterSnapshot indId afterMajor resolvedBlock afterResolution
        computedK afterK,
      (RecM.snapshotRecursorMemberDeclaration recursorId).run checkerMethods
          familyMemberInitial = .ok snapshot afterSnapshot →
      (RecM.validateRecursorMemberMajor snapshot).run checkerMethods
          afterSnapshot = .ok indId afterMajor →
      (RecM.resolveRecursorMemberBlock snapshot indId).run checkerMethods
          afterMajor = .ok resolvedBlock afterResolution →
      (RecM.validateRecursorMemberKTarget snapshot indId).run checkerMethods
          afterResolution = .ok computedK afterK →
      TcM.WF (ScopedWhnfStateInv model layer
        (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
        support []) afterK
        ((RecM.populateRecursorRulesFromBlock resolvedBlock
          snapshot.recBlock).run checkerMethods)
        (fun _ _ => True) := by
  intro snapshot afterSnapshot indId afterMajor resolvedBlock afterResolution
    computedK afterK snapshotRun majorRun resolutionRun kTargetRun
  rw [familyMemberSnapshotRunNeutral] at snapshotRun
  cases snapshotRun
  rw [familyMemberMajorRunFromInitialNeutral] at majorRun
  cases majorRun
  rw [familyMemberResolutionRunFromInitialNeutral] at resolutionRun
  cases resolutionRun
  rw [familyMemberKTargetRunFromInitialNeutral] at kTargetRun
  cases kTargetRun
  exact familyMemberRulePopulation_scoped_wf trustedReferences scopeTransition
    newSupported initialInvariant

/-- Reachability-indexed active population contract.  The state-neutral
snapshot/major/resolution/K prefix identifies the one concrete population
transaction without ever requiring stable trust for the recursor member. -/
theorem familyMemberPopulation_reachable_activeScoped_wf
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {support : RunSupport}
    (authorizedReferences : RecM.AuthorizedReferences
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      support)
    (scopeTransition : model.StateInScope familyMemberInitial →
      model.StateInScope familyMemberRulePopulationAfter)
    (newSupported : ∀ expression, FamilyMemberPopulationNewExpr expression →
      support expression)
    (initialInvariant : ScopedActiveWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support recursorMembers [] familyMemberInitial) :
    ∀ snapshot afterSnapshot indId afterMajor resolvedBlock afterResolution
        computedK afterK,
      (RecM.snapshotRecursorMemberDeclaration recursorId).run checkerMethods
          familyMemberInitial = .ok snapshot afterSnapshot →
      (RecM.validateRecursorMemberMajor snapshot).run checkerMethods
          afterSnapshot = .ok indId afterMajor →
      (RecM.resolveRecursorMemberBlock snapshot indId).run checkerMethods
          afterMajor = .ok resolvedBlock afterResolution →
      (RecM.validateRecursorMemberKTarget snapshot indId).run checkerMethods
          afterResolution = .ok computedK afterK →
      TcM.WF (ScopedActiveWhnfStateInv model layer
        (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
        support recursorMembers []) afterK
        ((RecM.populateRecursorRulesFromBlock resolvedBlock
          snapshot.recBlock).run checkerMethods)
        (fun _ _ => True) := by
  intro snapshot afterSnapshot indId afterMajor resolvedBlock afterResolution
    computedK afterK snapshotRun majorRun resolutionRun kTargetRun
  rw [familyMemberSnapshotRunNeutral] at snapshotRun
  cases snapshotRun
  rw [familyMemberMajorRunFromInitialNeutral] at majorRun
  cases majorRun
  rw [familyMemberResolutionRunFromInitialNeutral] at resolutionRun
  cases resolutionRun
  rw [familyMemberKTargetRunFromInitialNeutral] at kTargetRun
  cases kTargetRun
  exact familyMemberRulePopulation_activeScoped_wf authorizedReferences
    scopeTransition newSupported initialInvariant

/-- On every production-reachable snapshot/major prefix for this fixture,
block resolution takes the witnessed usable-cache hit.  Consequently the
peer-major generation fallback needs no semantic authority in the concrete
member-check proof. -/
theorem familyMemberResolution_reachable_wf
    {I : TcState .anon → Prop} (_hfault : TcM.LazyFaultPreserves I) :
    ∀ snapshot afterSnapshot indId afterMajor,
      (RecM.snapshotRecursorMemberDeclaration recursorId).run checkerMethods
          familyMemberInitial = .ok snapshot afterSnapshot →
      (RecM.validateRecursorMemberMajor snapshot).run checkerMethods
          afterSnapshot = .ok indId afterMajor →
      TcM.WF I afterMajor
        ((RecM.resolveRecursorMemberBlock snapshot indId).run checkerMethods)
        (fun _ _ => True) := by
  intro snapshot afterSnapshot indId afterMajor hsnapshot hmajor
  rw [familyMemberSnapshotRun] at hsnapshot
  cases hsnapshot
  rw [familyMemberMajorRun] at hmajor
  cases hmajor
  intro invariant
  rw [familyMemberResolutionRunNeutral]
  exact ⟨invariant, trivial⟩

/-- On every production-reachable snapshot, the major stage preserves an
arbitrary scoped suffix model because its final state is definitionally the
same reached snapshot state.  Temporary telescope states never have to inhabit
that model. -/
theorem familyMemberMajor_reachable_wf
    {I : TcState .anon → Prop} :
    ∀ snapshot afterSnapshot,
      (RecM.snapshotRecursorMemberDeclaration recursorId).run checkerMethods
          familyMemberInitial = .ok snapshot afterSnapshot →
      TcM.WF I afterSnapshot
        ((RecM.validateRecursorMemberMajor snapshot).run checkerMethods)
        (fun _ _ => True) := by
  intro snapshot afterSnapshot snapshotRun
  rw [familyMemberSnapshotRun] at snapshotRun
  cases snapshotRun
  intro invariant
  rw [familyMemberMajorRunNeutral]
  exact ⟨invariant, trivial⟩

/-- The data expected at the prelude/checker handoff for the certified
`IndexedVec.rec` declaration. -/
def familyExpectedMemberPreparation :
    RecM.PreparedRecursorMemberCheck .anon where
  recBlock := recursorBlockId
  ty := recursorConcrete.ty
  declaredK := false
  declaredLvls := 2
  declaredIsUnsafe := false
  params := 1
  motives := 1
  minors := 2
  indices := 1
  storedRules := recursorRules
  indId := familyId
  resolvedBlock := familyBlockId
  computedK := false
  generated := familyInstalledRecursors

def familyMemberPreparationOutcome :=
  (RecM.prepareRecursorMemberCheck recursorId).run checkerMethods
    familyMemberInitial

def familyMemberPreparationAfter : TcState .anon :=
  match familyMemberPreparationOutcome with
  | .ok _ after => after
  | .error _ failed => failed

/-- A proposition arranged so native evaluation decides only the returned
preparation data; the state is retained by the enclosing execution equation. -/
def familyMemberPreparationMatches : Prop :=
  match familyMemberPreparationOutcome with
  | .ok prepared _ => prepared = familyExpectedMemberPreparation
  | .error _ _ => False

local instance familyMemberPreparationMatchesDecidable :
    Decidable familyMemberPreparationMatches := by
  unfold familyMemberPreparationMatches
  cases familyMemberPreparationOutcome <;> infer_instance

private theorem familyMemberPreparationMatchesNative :
    familyMemberPreparationMatches := by
  native_decide

/-- The actual prelude reaches the exact expected data-bearing boundary. -/
theorem familyMemberPreparationRun :
    (RecM.prepareRecursorMemberCheck recursorId).run checkerMethods
      familyMemberInitial =
        .ok familyExpectedMemberPreparation familyMemberPreparationAfter := by
  have hmatches := familyMemberPreparationMatchesNative
  unfold familyMemberPreparationMatches at hmatches
  unfold familyMemberPreparationAfter
  generalize houtcome : familyMemberPreparationOutcome = outcome at hmatches ⊢
  cases outcome with
  | error error failed => contradiction
  | ok prepared after =>
      subst prepared
      simpa [familyMemberPreparationOutcome] using houtcome

/-- The successful concrete preparation run is decomposed into the exact six
named production stages, retaining every intermediate state and result. -/
theorem familyMemberPreparationTrace :
    RecursorMemberPreparationTrace recursorId checkerMethods
      familyMemberInitial familyExpectedMemberPreparation
      familyMemberPreparationAfter :=
  RecM.prepareRecursorMemberCheck_success familyMemberPreparationRun

/-! ## Actual outer member-check execution and handoff -/

def familyMemberCheckOutcome :=
  (RecM.checkRecursorMemberImpl recursorId).run checkerMethods
    familyMemberInitial

def familyMemberCheckAfter : TcState .anon :=
  match familyMemberCheckOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyMemberCheckSucceeded : Bool :=
  match familyMemberCheckOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem familyMemberCheckSucceededNative :
    familyMemberCheckSucceeded = true := by
  native_decide

theorem familyMemberCheckRun :
    (RecM.checkRecursorMemberImpl recursorId).run checkerMethods
      familyMemberInitial = .ok () familyMemberCheckAfter := by
  have success := familyMemberCheckSucceededNative
  unfold familyMemberCheckSucceeded at success
  unfold familyMemberCheckAfter
  generalize houtcome : familyMemberCheckOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyMemberCheckOutcome]

/-- The exact second phase reached by the actual outer checker is the
previously verified cache checker applied to the expected frozen data. -/
theorem familyPreparedMemberCheckRun :
    (RecM.checkPreparedRecursorMember recursorId
      familyExpectedMemberPreparation).run checkerMethods
        familyMemberPreparationAfter = .ok () familyMemberCheckAfter := by
  obtain ⟨prepared, afterPreparation, preparation, comparison⟩ :=
    RecM.checkRecursorMemberImpl_success familyMemberCheckRun
  rw [familyMemberPreparationRun] at preparation
  cases preparation
  exact comparison

/-- Production execution, exact preparation data, and exact checker handoff
packaged without any semantic callback assumption. -/
theorem familyMemberCheckExecution :
    (RecM.prepareRecursorMemberCheck recursorId).run checkerMethods
        familyMemberInitial =
          .ok familyExpectedMemberPreparation familyMemberPreparationAfter ∧
      (RecM.checkRecursorMemberImpl recursorId).run checkerMethods
        familyMemberInitial = .ok () familyMemberCheckAfter ∧
      (RecM.checkPreparedRecursorMember recursorId
        familyExpectedMemberPreparation).run checkerMethods
          familyMemberPreparationAfter = .ok () familyMemberCheckAfter :=
  ⟨familyMemberPreparationRun, familyMemberCheckRun,
    familyPreparedMemberCheckRun⟩

/-! ## Scoped semantic closure of the reached tail -/

/-- Selection from the actual post-prelude state preserves the scoped K2S
invariant under the same finite call contract as the cache-only fixture. -/
theorem familyPreparedSelectionInvariantScoped
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport}
    (uvars : transaction.certificate.generation.recursor.uvars =
      model.keys.uvars)
    (successor : Methods.ScopedWFAtOn model layer semantics support
      familyArtifactCalls (Methods.next checkerMethods))
    (initialInvariant :
      ScopedWhnfStateInv model layer semantics support []
        familyMemberPreparationAfter) :
    ∀ {index : Nat} {selected : GeneratedRecursor .anon}
        {afterSelection : TcState .anon},
      (RecM.selectGeneratedRecursorIndex recursorBlockId recursorId
          recursorConcrete.ty 1 1 2 familyId familyInstalledRecursors).run
          checkerMethods familyMemberPreparationAfter =
        .ok (some index) afterSelection →
      familyInstalledRecursors[index]? = some selected →
      ScopedWhnfStateInv model layer semantics support [] afterSelection := by
  intro index selected afterSelection selection _lookup
  exact RecM.selectGeneratedRecursorIndex_preservesScoped
    familySelectionCallPlan (familySelectionTranslationsScoped uvars)
      successor initialInvariant selection

/-- The actual outer checker reaches a semantically canonical exhaustive tail.
The sole remaining outer-composition premise is the scoped invariant at the
post-prelude state. -/
theorem familyPreparedMemberCheckCanonicalScoped
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport}
    (uvars : transaction.certificate.generation.recursor.uvars =
      model.keys.uvars)
    (successor : Methods.ScopedWFAtOn model layer semantics support
      familyArtifactCalls (Methods.next checkerMethods))
    (initialInvariant :
      ScopedWhnfStateInv model layer semantics support []
        familyMemberPreparationAfter) :
    CanonicalCacheAcceptance indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation recursorBlockId recursorId
      recursorConcrete.ty 2 false 1 1 2 1 familyId recursorRules
      familyInstalledRecursors checkerMethods
      (ScopedWhnfStateInv model layer semantics support [])
      familyMemberPreparationAfter familyMemberCheckAfter := by
  have closed := RecM.checkPreparedRecursorMember_canonicalScoped uvars
    familyPreparedMemberCheckRun familyInstalledRecursorCanonicalAt
    familyStoredArtifactTranslations familyArtifactCallPlanAt
    (familyPreparedSelectionInvariantScoped uvars successor initialInvariant)
    successor
  simpa only [familyExpectedMemberPreparation, familyAcceptedWorld_venv_eq,
    familyAcceptedWorld_nameOf_eq] using closed

/-- Move the scoped invariant premise from the frozen checker handoff back to
the state before the production prelude.  Exact telescope restoration closes
major discovery and K-target result-sort discovery, while the witnessed
usable-cache hit closes block resolution.  The concrete finite intern delta
and provenance-checked transactional commit close rule population without a
whole-operation preservation premise. -/
theorem familyMemberCheckCanonicalFromInitialScoped
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {support : RunSupport}
    (uvars : transaction.certificate.generation.recursor.uvars =
      model.keys.uvars)
    (successor : Methods.ScopedWFAtOn model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none) support
      familyArtifactCalls (Methods.next checkerMethods))
    (hfault : TcM.LazyFaultPreserves
      (ScopedWhnfStateInv model layer
        (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
        support []))
    (trustedReferences : RecM.TrustedReferences familyAcceptedWorld support)
    (scopeTransition : model.StateInScope familyMemberInitial →
      model.StateInScope familyMemberRulePopulationAfter)
    (newSupported : ∀ expression, FamilyMemberPopulationNewExpr expression →
      support expression)
    (initialInvariant :
      ScopedWhnfStateInv model layer
        (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
        support [] familyMemberInitial) :
    CanonicalCacheAcceptance indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation recursorBlockId recursorId
      recursorConcrete.ty 2 false 1 1 2 1 familyId recursorRules
      familyInstalledRecursors checkerMethods
      (ScopedWhnfStateInv model layer
        (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
        support [])
      familyMemberPreparationAfter familyMemberCheckAfter := by
  have population := familyMemberPopulation_reachable_scoped_wf
    trustedReferences scopeTransition newSupported initialInvariant
  have prelude := RecM.prepareRecursorMemberCheck_reachable_wf hfault
    recursorId checkerMethods familyMemberInitial
      familyMemberMajor_reachable_wf
      (familyMemberResolution_reachable_wf hfault)
      familyMemberKTarget_reachable_wf population
  have post := prelude initialInvariant
  rw [familyMemberPreparationRun] at post
  exact familyPreparedMemberCheckCanonicalScoped uvars successor post.1

/-! ## Non-vacuous active-block closure -/

/-- Selection from the actual post-prelude state preserves the active scoped
invariant.  The generated cache may still mention the recursor member because
the enclosing atomic block has not closed yet. -/
theorem familyPreparedSelectionInvariantActiveScoped
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport}
    (uvars : transaction.certificate.generation.recursor.uvars =
      model.keys.uvars)
    (successor : Methods.ActiveScopedWFAtOn model layer semantics support
      recursorMembers familyArtifactCalls (Methods.next checkerMethods))
    (initialInvariant : ScopedActiveWhnfStateInv model layer semantics support
      recursorMembers [] familyMemberPreparationAfter) :
    ∀ {index : Nat} {selected : GeneratedRecursor .anon}
        {afterSelection : TcState .anon},
      (RecM.selectGeneratedRecursorIndex recursorBlockId recursorId
          recursorConcrete.ty 1 1 2 familyId familyInstalledRecursors).run
          checkerMethods familyMemberPreparationAfter =
        .ok (some index) afterSelection →
      familyInstalledRecursors[index]? = some selected →
      ScopedActiveWhnfStateInv model layer semantics support recursorMembers
        [] afterSelection := by
  intro index selected afterSelection selection _lookup
  exact RecM.selectGeneratedRecursorIndex_preservesActiveScoped
    familySelectionCallPlan (familySelectionTranslationsScoped uvars)
      successor initialInvariant selection

/-- The exact prepared production tail is canonical while the recursor block
is active. -/
theorem familyPreparedMemberCheckCanonicalActiveScoped
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {support : RunSupport}
    (uvars : transaction.certificate.generation.recursor.uvars =
      model.keys.uvars)
    (successor : Methods.ActiveScopedWFAtOn model layer semantics support
      recursorMembers familyArtifactCalls (Methods.next checkerMethods))
    (initialInvariant : ScopedActiveWhnfStateInv model layer semantics support
      recursorMembers [] familyMemberPreparationAfter) :
    CanonicalCacheAcceptance indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation recursorBlockId recursorId
      recursorConcrete.ty 2 false 1 1 2 1 familyId recursorRules
      familyInstalledRecursors checkerMethods
      (ScopedActiveWhnfStateInv model layer semantics support recursorMembers
        []) familyMemberPreparationAfter familyMemberCheckAfter := by
  have closed := RecM.checkPreparedRecursorMember_canonicalActiveScoped uvars
    familyPreparedMemberCheckRun familyInstalledRecursorCanonicalAt
    familyStoredArtifactTranslations familyArtifactCallPlanAt
    (familyPreparedSelectionInvariantActiveScoped uvars successor
      initialInvariant) successor
  simpa only [familyExpectedMemberPreparation, familyAcceptedWorld_venv_eq,
    familyAcceptedWorld_nameOf_eq] using closed

/-- Complete active-authority semantic closure of the reached production
member check.  Unlike the earlier stable compatibility theorem, every premise
is inhabitable for recursive `IndexedVec`: rule references are authorized by
the exact active recursor-member array and can later be converted to stable
trust only by successful atomic admission. -/
theorem familyMemberCheckCanonicalFromInitialActiveScoped
    {model : ScopedKernelSuffixModel RawProjRel.none familyAcceptedWorld}
    {layer : WhnfLayer} {support : RunSupport}
    (uvars : transaction.certificate.generation.recursor.uvars =
      model.keys.uvars)
    (successor : Methods.ActiveScopedWFAtOn model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none) support
      recursorMembers familyArtifactCalls (Methods.next checkerMethods))
    (hfault : TcM.LazyFaultPreserves
      (ScopedActiveWhnfStateInv model layer
        (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
        support recursorMembers []))
    (authorizedReferences : RecM.AuthorizedReferences
      (CacheAuthority.coordinatedBlock familyAcceptedWorld recursorMembers)
      support)
    (scopeTransition : model.StateInScope familyMemberInitial →
      model.StateInScope familyMemberRulePopulationAfter)
    (newSupported : ∀ expression, FamilyMemberPopulationNewExpr expression →
      support expression)
    (initialInvariant : ScopedActiveWhnfStateInv model layer
      (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
      support recursorMembers [] familyMemberInitial) :
    CanonicalCacheAcceptance indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation recursorBlockId recursorId
      recursorConcrete.ty 2 false 1 1 2 1 familyId recursorRules
      familyInstalledRecursors checkerMethods
      (ScopedActiveWhnfStateInv model layer
        (kernelCacheSemanticsWithInductives model.keys RawProjRel.none)
        support recursorMembers [])
      familyMemberPreparationAfter familyMemberCheckAfter := by
  have population := familyMemberPopulation_reachable_activeScoped_wf
    authorizedReferences scopeTransition newSupported initialInvariant
  have prelude := RecM.prepareRecursorMemberCheck_reachable_wf hfault
    recursorId checkerMethods familyMemberInitial
      familyMemberMajor_reachable_wf
      (familyMemberResolution_reachable_wf hfault)
      familyMemberKTarget_reachable_wf population
  have post := prelude initialInvariant
  rw [familyMemberPreparationRun] at post
  exact familyPreparedMemberCheckCanonicalActiveScoped uvars successor post.1

end Ix.Tc.IndexedRecursiveFixture
