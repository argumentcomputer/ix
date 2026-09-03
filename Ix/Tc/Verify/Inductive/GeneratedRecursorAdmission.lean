import Ix.Tc.Verify.Inductive.GeneratedRecursorInitialInvariant
import Ix.Tc.Verify.Inductive.OneFamilyAdmission

/-!
# Canonical generated-recursor admission

This module closes the first E2c production recursor transaction.  The
certified family transaction has already installed `IndexedVec.rec` and its
two equations in Lean4Lean's Theory environment.  Ix nevertheless keeps the
separately ingressed recursor block untrusted while
`checkRecursorMemberImpl` compares its immutable declaration against the
generated cache.

The successful comparison below is composed with
`ExistingSemanticBlockCertificate`, not `InductiveOracle`.  Consequently the
admission keeps the Theory environment fixed, trusts exactly the physical
recursor-block array, retains every registered equation and exact iota
pattern, and only then converts active cache authority into stable trust and
publishes the block-success verdict.
-/

namespace Ix.Tc.IndexedRecursiveFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures
open IndexedRecursiveCertificateFixture

/-! ## Per-member semantic provenance already present after family generation -/

/-- Direct per-member provenance for the generated recursor in the certified
post-generation Theory environment.  This is the payload formerly reachable
only by constructing the whole recursor `InductiveOracle`; here every field is
assembled directly from the certificate-backed catalog link and the two
position-indexed pattern proofs. -/
private def recursorSemanticEntryBase :
    TrustedCatalogEntry RawProjRel.none world.catalog world.nameOf
      indexedVecFinalEnv recursorId := by
  obtain ⟨hraw, hlookup, hwf⟩ := recursorLink.translateRecursor
  refine .ambient catalog_recursor hraw hlookup hwf ?_ ?_
  · intro rule hrule
    exact recursorLink.registeredRule hrule
  · intro ruleIndex rule hrule
    have hcount : familyLink.constructorIds.size = 2 :=
      IndexedRecursivePattern.constructorCount familyLink
    have hbound := recursorLink.recursorShape.ruleCount hrule
    have hzero : 0 < familyLink.constructorIds.size := by omega
    have hone : 1 < familyLink.constructorIds.size := by omega
    rcases (show ruleIndex = 0 ∨ ruleIndex = 1 by omega) with rfl | rfl
    · exact
        ⟨IndexedRecursivePattern.nilPattern
            (familyLink.constructorIds[0]'hzero),
          IndexedRecursivePattern.nilPatternRel recursorLink hzero hrule,
          rfl⟩
    · exact
        ⟨IndexedRecursivePattern.consPattern
            (familyLink.constructorIds[1]'hone),
          IndexedRecursivePattern.consPatternRel recursorLink hone hrule,
          rfl⟩

/-- The family admission changes neither catalog/name assignment nor the
certified post-generation Theory environment, so the direct recursor entry is
available unchanged in the active family-accepted world. -/
def familyRecursorSemanticEntry :
    TrustedCatalogEntry RawProjRel.none familyAcceptedWorld.catalog
      familyAcceptedWorld.nameOf familyAcceptedWorld.venv recursorId := by
  change TrustedCatalogEntry RawProjRel.none world.catalog world.nameOf
    indexedVecFinalEnv recursorId
  exact recursorSemanticEntryBase

/-! ## Exact oracle-free recursor-block admission -/

/-- The generated recursor is not made trusted as a side effect of admitting
the separately owned family/constructor block. -/
theorem familyAcceptedWorld_recursor_fresh :
    ¬familyAcceptedWorld.trusted recursorId := by
  intro htrusted
  change (recursorId ∈ familyMembers ∨ world.trusted recursorId) at htrusted
  rcases htrusted with hfamily | hold
  · have hcoordinated := (familyCoordinated_iff recursorId).1 hfamily
    obtain ⟨concrete, hcatalog, howner⟩ := hcoordinated
    rw [catalog_recursor] at hcatalog
    cases hcatalog
    exact recursorNotFamilyOwner howner
  · exact recursorLink.fresh hold

/-- Exact physical recursor identity transported across the already-completed
family admission. -/
def exactRecursorBlockAfterFamily :
    ExactCheckBlock familyAcceptedWorld recursorBlockId recursorMembers
      .recursor :=
  exactRecursorBlock.rebaseWorld familyAtomicAdmission.promotion.le

/-- Complete semantic certificate for the singleton physical recursor block.
The member is fresh, but its certified Theory constant and rules are already
installed. -/
def familyRecursorBlockCertificate :
    ExistingSemanticBlockCertificate RawProjRel.none familyAcceptedWorld
      recursorBlockId recursorMembers .recursor where
  exactBlock := exactRecursorBlockAfterFamily
  fresh := by
    intro id hmember
    rw [recursorMembers_eq] at hmember
    have hid : id = recursorId := by simpa using hmember
    subst id
    exact familyAcceptedWorld_recursor_fresh
  entry := by
    intro id hmember
    rw [recursorMembers_eq] at hmember
    have hid : id = recursorId := by simpa using hmember
    subst id
    exact familyRecursorSemanticEntry

/-- Generic one-family certificate instantiated by the concrete `IndexedVec`
family transition and its separately checked generated recursor block. -/
def oneFamilyCertificate :
    OneFamilyRecursorCertificate RawProjRel.none world familyBlockId
      familyMembers recursorBlockId recursorMembers indexedVecFinalEnv where
  family := familyBlockCertificate
  recursor := familyRecursorBlockCertificate

/-- Post-world of the exact generated-recursor trust transition.  Its Theory
environment is definitionally the same `indexedVecFinalEnv`; only the trusted
predicate grows. -/
def familyRecursorAcceptedWorld : VerifyWorld :=
  oneFamilyCertificate.admittedWorld

/-- Oracle-free atomic admission for the physical `IndexedVec.rec` block. -/
theorem familyRecursorAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none familyAcceptedWorld
      familyRecursorAcceptedWorld recursorBlockId recursorMembers
      .recursor :=
  oneFamilyCertificate.recursorAdmission trustedCatalog

/-- The reusable one-family closure theorem specializes to the complete
`IndexedVec` family/recursor pair. -/
theorem oneFamilyAtomicClosure : oneFamilyCertificate.AtomicClosure :=
  oneFamilyCertificate.atomicClosure trustedCatalog

/-! ## Production comparison followed by stable close -/

/-- The canonical member-check result retains the complete active invariant
at its actual final state. -/
theorem familyMemberCheckAfter_activeInvariant :
    ScopedActiveWhnfStateInv familyMemberModel .accelerated
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      familyMemberSupport recursorMembers [] familyMemberCheckAfter := by
  obtain ⟨_index, _selected, _afterSelection, _selection, _lookup,
    accepted⟩ := familyMemberCheckCanonicalConcrete
  exact accepted.finalInvariant

/-- Rebase the successful concrete member-check state across the exact
ghost-only recursor admission. -/
theorem familyRecursorAdmissionState :
    BlockStateWF RawProjRel.none familyMemberCheckAfter
      familyRecursorAcceptedWorld :=
  (familyRecursorBlockCertificate.admitState
    familyMemberCheckAfter_activeInvariant.active.blockState).2

/-- Stable post-state after the canonical member comparison, exact semantic
admission, elimination of temporary recursor-member authority, and physical
success publication. -/
theorem familyMemberCheckStable :
    KernelStateWF
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      RawProjRel.none familyRecursorAcceptedWorld familyMemberSupport
      (familyMemberCheckAfter.withBlockCheckResult recursorBlockId
        (.ok ())) :=
  familyMemberCheckAfter_activeInvariant.active.closeSuccess
    familyRecursorAtomicAdmission familyRecursorAdmissionState

/-- One premise-free statement joins the real outer member run, exhaustive
canonical artifact comparison, exact oracle-free admission, and stable cache
publication.  This is the first E2c recursor transaction closed at the same
boundary used by coordinated block checking. -/
structure CanonicalRecursorAtomicClosure : Prop where
  memberRun :
    (RecM.checkRecursorMemberImpl recursorId).run checkerMethods
      familyMemberInitial = .ok () familyMemberCheckAfter
  canonical :
    GeneratedRecursorSemantics.CanonicalCacheAcceptance indexedVecFinalEnv
      nameOf RawProjRel.none transaction.certificate.generation
      recursorBlockId recursorId recursorConcrete.ty 2 false 1 1 2 1 familyId
      recursorRules familyInstalledRecursors checkerMethods
      (ScopedActiveWhnfStateInv familyMemberModel .accelerated
        (kernelCacheSemanticsWithInductives familyMemberModel.keys
          RawProjRel.none)
        familyMemberSupport recursorMembers [])
      familyMemberPreparationAfter familyMemberCheckAfter
  admission :
    AtomicBlockAdmission RawProjRel.none familyAcceptedWorld
      familyRecursorAcceptedWorld recursorBlockId recursorMembers .recursor
  oneFamily : oneFamilyCertificate.AtomicClosure
  stable :
    KernelStateWF
      (kernelCacheSemanticsWithInductives familyMemberModel.keys
        RawProjRel.none)
      RawProjRel.none familyRecursorAcceptedWorld familyMemberSupport
      (familyMemberCheckAfter.withBlockCheckResult recursorBlockId
        (.ok ()))

/-- The complete concrete `IndexedVec.rec` atomic closure. -/
theorem familyRecursorAtomicClosure : CanonicalRecursorAtomicClosure where
  memberRun := familyMemberCheckRun
  canonical := familyMemberCheckCanonicalConcrete
  admission := familyRecursorAtomicAdmission
  oneFamily := oneFamilyAtomicClosure
  stable := familyMemberCheckStable

end Ix.Tc.IndexedRecursiveFixture
