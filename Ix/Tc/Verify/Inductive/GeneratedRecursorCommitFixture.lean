import Ix.Tc.Verify.Inductive.GeneratedRecursorRuleFixture

/-!
# Production generated-recursor commit fixture

This module carries the canonical `IndexedVec` type and rules through the
public transactional rule-population boundary.  The public operation reruns
the complete rule builder from the immutable ingress cache snapshot, checks
that callback-visible cache state retained the exact positional metadata, and
then reconstructs the installed entry from ingress headers/types plus only the
locally returned rule array.

The final theorem exposes both the exact production run and a canonical
artifact at the installed cache position.  Thus subsequent recursor-checker
proofs do not need to trust either a callback-mutated cache type or a
callback-written rule array.
-/

namespace Ix.Tc.IndexedRecursiveFixture

open GeneratedRecursorSemantics
open IndexedRecursiveCertificateFixture
open Lean4Lean.InductiveReplayFixtures

local instance generatedCommitAddressDecidableEq : DecidableEq Address :=
  AnonStructural.addressDecidableEq

local instance generatedCommitKExprDecidableEq : DecidableEq (KExpr .anon) :=
  AnonStructural.exprDecidableEq

local instance generatedCommitRecRuleDecidableEq :
    DecidableEq (RecRule .anon) :=
  AnonStructural.decidableEqOfRoundtrip AnonStructural.RecRule.ofKernel
    AnonStructural.RecRule.toKernel AnonStructural.RecRule.roundtrip

local instance generatedCommitRecursorDecidableEq :
    DecidableEq (GeneratedRecursor .anon) := by
  intro left right
  cases left
  cases right
  simp only [GeneratedRecursor.mk.injEq]
  infer_instance

/-! ## Actual public population and commit execution -/

def familyRuleCommitOutcome :=
  (RecM.populateRecursorRulesFromBlock familyBlockId recursorBlockId).run
    checkerMethods familyKernelAfter

def familyRuleCommitAfter : TcState .anon :=
  match familyRuleCommitOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyRuleCommitSucceeded : Bool :=
  match familyRuleCommitOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem familyRuleCommitSucceededNative :
    familyRuleCommitSucceeded = true := by
  native_decide

theorem familyRuleCommitSucceeded_eq :
    familyRuleCommitSucceeded = true :=
  familyRuleCommitSucceededNative

/-- The public production operation takes its data-bearing success branch. -/
theorem familyRuleCommitRun :
    (RecM.populateRecursorRulesFromBlock familyBlockId recursorBlockId).run
      checkerMethods familyKernelAfter = .ok () familyRuleCommitAfter := by
  have success := familyRuleCommitSucceeded_eq
  unfold familyRuleCommitSucceeded at success
  unfold familyRuleCommitAfter
  generalize houtcome : familyRuleCommitOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyRuleCommitOutcome]

/-- The generated snapshot projection is data-bearing, not its empty
totalization branch. -/
theorem familyGeneratedSnapshotLookup :
    familyKernelAfter.env.recursorCache[familyBlockId]? =
      some familyGeneratedSnapshot := by
  cases lookup : familyKernelAfter.env.recursorCache[familyBlockId]? with
  | none =>
      have nonempty := familyGeneratedSnapshotSize
      simp [familyGeneratedSnapshot, lookup] at nonempty
  | some generated =>
      simp [familyGeneratedSnapshot, lookup]

/-- The public transactional boundary installs exactly the immutable ingress
headers/types zipped with the local core's returned rule arrays. -/
theorem familyRuleCommitCache :
    familyRuleCommitAfter.env.recursorCache[familyBlockId]? =
      some (familyGeneratedSnapshot.zipWith
        (fun header generated => header.withRules generated.rules)
        familyGeneratedWithRules) := by
  have boundary :=
    RecM.populateRecursorRulesFromBlock_artifacts familyBlockId
      recursorBlockId checkerMethods familyKernelAfter familyRuleCommitAfter
      familyRuleCommitRun
  rw [familyGeneratedSnapshotLookup] at boundary
  obtain ⟨generatedWithRules, afterCore, cached, coreRun, _, _, _, _,
      finalCache, _, _⟩ := boundary
  rw [familyRulePopulationRun] at coreRun
  cases coreRun
  exact finalCache

/-! ## Canonical artifact after commit -/

/-- Exact array reconstructed by the public transactional commit. -/
def familyInstalledRecursors : Array (GeneratedRecursor .anon) :=
  familyGeneratedSnapshot.zipWith
    (fun header generated => header.withRules generated.rules)
    familyGeneratedWithRules

theorem familyRuleCommitInstalledCache :
    familyRuleCommitAfter.env.recursorCache[familyBlockId]? =
      some familyInstalledRecursors := by
  simpa [familyInstalledRecursors] using familyRuleCommitCache

theorem familyInstalledRecursorsSize : familyInstalledRecursors.size = 1 := by
  simp [familyInstalledRecursors, familyGeneratedSnapshotSize,
    familyGeneratedWithRulesSize]

private theorem familyInstalledRecursorTypeInternSupported :
    familyKernelAfter.env.intern.ExprSupport
      familyInstalledRecursors[0]!.ty := by
  refine ⟨familyInstalledRecursors[0]!.ty.internKey, ?_⟩
  native_decide

private theorem familyInstalledNilRuleInternSupported :
    familyKernelAfter.env.intern.ExprSupport (concreteRuleAt 0).rhs := by
  refine ⟨(concreteRuleAt 0).rhs.internKey, ?_⟩
  native_decide

private theorem familyInstalledConsRuleInternSupported :
    familyKernelAfter.env.intern.ExprSupport (concreteRuleAt 1).rhs := by
  refine ⟨(concreteRuleAt 1).rhs.internKey, ?_⟩
  native_decide

private theorem familyInstalledRecursorRules :
    familyInstalledRecursors[0]!.rules =
      #[concreteRuleAt 0, concreteRuleAt 1] := by
  native_decide

/-- The type retained by the transactional installation is structurally the
independently ingressed canonical recursor type.  Exposing this exact equality
lets the frozen checker discharge its production address-equality fast path
without appealing to a general DefEq oracle. -/
private theorem familyInstalledRecursorTypeEqNative :
    familyInstalledRecursors[0]!.ty = recursorConcrete.ty := by
  native_decide

theorem familyInstalledRecursorType_eq :
    familyInstalledRecursors[0]!.ty = recursorConcrete.ty := by
  exact familyInstalledRecursorTypeEqNative

/-- The transactional installation retains exactly the independently
ingressed positional rule array. -/
theorem familyInstalledRecursorRules_eq :
    familyInstalledRecursors[0]!.rules = recursorRules := by
  rw [familyInstalledRecursorRules, recursorRules_literal]

private theorem familyInstalledRecursorInductiveAddress :
    familyInstalledRecursors[0]!.indAddr = familyId.addr := by
  native_decide

/-- Every executable expression installed by the concrete transaction was
already interned by the reached family-checker state.  This is the finite
bridge from the fixture artifact to an arbitrary run support covering that
state's intern table. -/
theorem familyInstalledRecursorsInternSupported :
    ∀ generated ∈ familyInstalledRecursors,
      familyKernelAfter.env.intern.ExprSupport generated.ty ∧
        ∀ rule ∈ generated.rules,
          familyKernelAfter.env.intern.ExprSupport rule.rhs := by
  intro generated hgenerated
  obtain ⟨index, hindex, hget⟩ := Array.mem_iff_getElem.mp hgenerated
  rw [familyInstalledRecursorsSize] at hindex
  have indexEq : index = 0 := by omega
  subst index
  have htype := familyInstalledRecursorTypeInternSupported
  rw [getElem!_pos familyInstalledRecursors 0 (by
    rw [familyInstalledRecursorsSize]
    decide)] at htype
  cases hget
  refine ⟨htype, ?_⟩
  intro rule hrule
  have hrules := familyInstalledRecursorRules
  rw [getElem!_pos familyInstalledRecursors 0 (by
    rw [familyInstalledRecursorsSize]
    decide)] at hrules
  rw [hrules] at hrule
  obtain ⟨ruleIndex, hRuleIndex, hRuleGet⟩ :=
    Array.mem_iff_getElem.mp hrule
  change ruleIndex < 2 at hRuleIndex
  rcases (show ruleIndex = 0 ∨ ruleIndex = 1 by omega) with rfl | rfl
  · have ruleEq : concreteRuleAt 0 = rule := by simpa using hRuleGet
    subst rule
    exact familyInstalledNilRuleInternSupported
  · have ruleEq : concreteRuleAt 1 = rule := by simpa using hRuleGet
    subst rule
    exact familyInstalledConsRuleInternSupported

/-- The unique installed recursor's executable type and every installed rule
right-hand side already occur in the family checker's concrete intern table.
This zero-index specialization avoids making later finite-support proofs
recover array membership from a totalized lookup. -/
private theorem familyInstalledRecursorAtZeroMemberNative :
    familyInstalledRecursors[0]! ∈ familyInstalledRecursors := by
  native_decide

theorem familyInstalledRecursorAtZeroInternSupported :
    familyKernelAfter.env.intern.ExprSupport
        familyInstalledRecursors[0]!.ty ∧
      ∀ rule ∈ familyInstalledRecursors[0]!.rules,
        familyKernelAfter.env.intern.ExprSupport rule.rhs := by
  apply familyInstalledRecursorsInternSupported
  exact familyInstalledRecursorAtZeroMemberNative

/-- The unique installed generated recursor belongs to the accepted family
member at the physical address recorded by its canonical header. -/
theorem familyInstalledRecursorsInductiveAddress :
    ∀ generated ∈ familyInstalledRecursors,
      generated.indAddr = familyId.addr := by
  intro generated hgenerated
  obtain ⟨index, hindex, hget⟩ := Array.mem_iff_getElem.mp hgenerated
  rw [familyInstalledRecursorsSize] at hindex
  have indexEq : index = 0 := by omega
  subst index
  have haddr := familyInstalledRecursorInductiveAddress
  rw [getElem!_pos familyInstalledRecursors 0 (by
    rw [familyInstalledRecursorsSize]
    decide)] at haddr
  simpa only [hget] using haddr

theorem familyGeneratedSnapshotNonempty :
    0 < familyGeneratedSnapshot.size := by
  rw [familyGeneratedSnapshotSize]
  decide

theorem familyGeneratedWithRulesNonempty :
    0 < familyGeneratedWithRules.size := by
  rw [familyGeneratedWithRulesSize]
  decide

/-- Concrete bridge from the family checker's generated cache entry to the
independently ingressed canonical recursor type. -/
private theorem familyGeneratedSnapshotTypeNative :
    (familyGeneratedSnapshot[0]'familyGeneratedSnapshotNonempty).ty =
      recursorConcrete.ty := by
  native_decide

theorem familyGeneratedSnapshotType_eq :
    (familyGeneratedSnapshot[0]'familyGeneratedSnapshotNonempty).ty =
      recursorConcrete.ty :=
  familyGeneratedSnapshotTypeNative

/-- The immutable type selected by the public commit is the exact
Lean4Lean-generated recursor type. -/
theorem familyGeneratedSnapshotTypeCanonical :
    CanonicalTypeS indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation
      (familyGeneratedSnapshot[0]'familyGeneratedSnapshotNonempty) := by
  unfold CanonicalTypeS
  change TrKExprS indexedVecFinalEnv
    transaction.certificate.generation.recursor.uvars nameOf RawProjRel.none
    [] (familyGeneratedSnapshot[0]'familyGeneratedSnapshotNonempty).ty
      transaction.certificate.generation.recType
  rw [familyGeneratedSnapshotType_eq]
  simpa [Lean4Lean.VInductDecl.GenerationChecked.recursor] using
    recursorTypeTyped

/-- The local completed entry's position-zero rule array is canonical. -/
theorem familyGeneratedWithRulesCanonical :
    CanonicalRulesS indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation
      (familyGeneratedWithRules[0]'familyGeneratedWithRulesNonempty).rules := by
  have canonical := familyBuildRulesCanonical
  unfold familyBuiltRules familyCompletedRecursor at canonical
  rw [getElem!_pos familyGeneratedWithRules 0
    familyGeneratedWithRulesNonempty] at canonical
  exact canonical

/-- The entry actually installed by the public transaction has the exact
canonical generated type and all positional canonical rules. -/
theorem familyRuleCommitCanonical :
    ∃ installed,
      ∃ installedBound : 0 < installed.size,
        familyRuleCommitAfter.env.recursorCache[familyBlockId]? =
            some installed ∧
          CanonicalArtifactsS indexedVecFinalEnv nameOf RawProjRel.none
            transaction.certificate.generation
            installed[0] := by
  let installed := familyInstalledRecursors
  have completedSize :
      familyGeneratedWithRules.size = familyGeneratedSnapshot.size := by
    rw [familyGeneratedWithRulesSize, familyGeneratedSnapshotSize]
  have installedSize : installed.size = familyGeneratedSnapshot.size := by
    simp [installed, familyInstalledRecursors, completedSize]
  have installedBound : 0 < installed.size := by
    rw [installedSize]
    exact familyGeneratedSnapshotNonempty
  refine ⟨installed, installedBound, ?_, ?_⟩
  · simpa [installed] using familyRuleCommitInstalledCache
  · dsimp only [installed, familyInstalledRecursors] at installedBound ⊢
    rw [Array.getElem_zipWith]
    exact CanonicalArtifactsS.withRules
      familyGeneratedSnapshotTypeCanonical familyGeneratedWithRulesCanonical

/-- Canonical artifact at the unique explicit installed position. -/
theorem familyInstalledRecursorCanonical :
    CanonicalArtifactsS indexedVecFinalEnv nameOf RawProjRel.none
      transaction.certificate.generation familyInstalledRecursors[0]! := by
  obtain ⟨installed, installedBound, cache, canonical⟩ :=
    familyRuleCommitCanonical
  have installedEq : installed = familyInstalledRecursors := by
    rw [familyRuleCommitInstalledCache] at cache
    exact Option.some.inj cache.symm
  subst installed
  simpa only [getElem!_pos familyInstalledRecursors 0 (by
    rw [familyInstalledRecursorsSize]
    decide)] using canonical

/-- One theorem packages the exact public transaction and its canonical
installed artifact for the production recursor-checker composition. -/
theorem familyRuleCommitExecution :
    (RecM.populateRecursorRulesFromBlock familyBlockId recursorBlockId).run
        checkerMethods familyKernelAfter = .ok () familyRuleCommitAfter ∧
      ∃ installed,
        ∃ installedBound : 0 < installed.size,
          familyRuleCommitAfter.env.recursorCache[familyBlockId]? =
              some installed ∧
            CanonicalArtifactsS indexedVecFinalEnv nameOf RawProjRel.none
              transaction.certificate.generation
              installed[0] :=
  ⟨familyRuleCommitRun, familyRuleCommitCanonical⟩

end Ix.Tc.IndexedRecursiveFixture
