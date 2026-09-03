import Ix.Tc.Verify.Check.BlockAcceptance
import Ix.Tc.Verify.Inductive.RecursivePiFixture

/-!
# Production acceptance of the recursive-Pi family

This module joins three independently checked facts about the same physical
`Acc` block:

* anonymous ingress produced its exact family/constructor member array;
* the production family checker accepted that exact array; and
* the Lean4Lean certificate gives every member its stable Theory meaning in
  one atomic semantic transition.

The result is deliberately limited to the family block. The separately
generated `Acc.rec` declaration and its recursive-Pi iota rule are the next
slice.
-/

namespace Ix.Tc.RecursivePiFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open RecursivePiCertificateFixture

local instance acceptanceAnonKIdDecidableEq : DecidableEq (KId .anon) :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by cases equality; exact beq_self_eq_true left)

/-! ## Exact physical ownership -/

/-- Direct ownership is the block field stored by an inductive declaration.
A constructor inherits that owner through its exact catalogued parent. -/
private def IsDirectInductiveOwner (block : KId .anon) : KConst .anon → Prop
  | .indc (block := owner) .. => owner = block
  | _ => False

local instance directInductiveOwnerDecidable (block : KId .anon)
    (concrete : KConst .anon) :
    Decidable (IsDirectInductiveOwner block concrete) := by
  cases concrete <;> simp only [IsDirectInductiveOwner] <;> infer_instance

private theorem directInductiveOwner_inductiveMemberOf
    {catalog : Catalog} {block : KId .anon} {concrete : KConst .anon}
    (howner : IsDirectInductiveOwner block concrete) :
    concrete.IsInductiveMemberOf catalog block := by
  cases concrete <;>
    simp_all [IsDirectInductiveOwner, KConst.IsInductiveMemberOf]

private theorem certifiedConstructor_inductiveMemberOf
    {source : VInductDecl} {familyId block : KId .anon}
    {index : Nat} {sourceConstructor : VConstVal}
    {concrete familyConcrete : KConst .anon} {catalog : Catalog}
    (hshape : concrete.IsCertifiedSingletonConstructor source familyId index
      sourceConstructor)
    (hcatalog : catalog familyId = some familyConcrete)
    (hfamilyOwner : IsDirectInductiveOwner block familyConcrete) :
    concrete.IsInductiveMemberOf catalog block := by
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonConstructor,
      KConst.IsInductiveMemberOf, IsDirectInductiveOwner]
  exact hfamilyOwner

private theorem familyDirectOwnerNative :
    IsDirectInductiveOwner familyBlockId familyConcrete := by
  native_decide

theorem familyDirectOwner :
    IsDirectInductiveOwner familyBlockId familyConcrete :=
  familyDirectOwnerNative

theorem familyOwner :
    familyConcrete.IsInductiveMemberOf catalog familyBlockId :=
  directInductiveOwner_inductiveMemberOf familyDirectOwner

theorem introOwner :
    introConcrete.IsInductiveMemberOf catalog familyBlockId :=
  certifiedConstructor_inductiveMemberOf introShape catalog_family
    familyDirectOwner

/-- Every successful lookup in this deliberately finite catalog is exactly
one of the two declarations returned by the physical ingress execution. -/
theorem catalog_entry_cases {id : KId .anon} {concrete : KConst .anon}
    (hcatalog : catalog id = some concrete) :
    (id = familyId ∧ concrete = familyConcrete) ∨
      (id = introId ∧ concrete = introConcrete) := by
  unfold catalog at hcatalog
  split at hcatalog
  · left
    exact ⟨eq_of_beq (by assumption), (Option.some.inj hcatalog).symm⟩
  · split at hcatalog
    · right
      exact ⟨eq_of_beq (by assumption), (Option.some.inj hcatalog).symm⟩
    · contradiction

theorem familyCoordinated_iff (id : KId .anon) :
    id ∈ members ↔
      catalog.CoordinatedMember familyBlockId .inductive' id := by
  constructor
  · intro hmember
    simp [members] at hmember
    rcases hmember with rfl | rfl
    · exact ⟨familyConcrete, catalog_family, familyOwner⟩
    · exact ⟨introConcrete, catalog_intro, introOwner⟩
  · rintro ⟨concrete, hcatalog, howner⟩
    rcases catalog_entry_cases hcatalog with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [members]
    · simp [members]

theorem world_family_block :
    world.blocks familyBlockId = some members := by
  change ingressAfter.getBlock? familyBlockId = some members
  simpa [checkerInitial, TcState.ofEnvAnon] using blockLoaded

def exactFamilyBlock :
    ExactCheckBlock world familyBlockId members .inductive' where
  blockLookup := world_family_block
  nonempty := by rw [members]; decide
  memberIff := familyCoordinated_iff

/-! ## Atomic semantic admission -/

/-- The certificate link and the production checker consume the same exact
physical member order. -/
theorem familyLink_members_eq : familyLink.members = members := by
  rfl

private def familySemanticEntry {id : KId .anon}
    (hmember : id ∈ members) :
    TrustedCatalogEntry RawProjRel.none world.catalog world.nameOf finalEnv
      id := by
  have hlinked : id ∈ familyLink.members := by
    rw [familyLink_members_eq]
    exact hmember
  obtain ⟨concrete, name, ci, hcatalog, hraw, hlookup, hwf⟩ :=
    familyLink.translateMember hlinked
  exact .ambient hcatalog hraw hlookup hwf
    (by
      intro rule hrule
      exact False.elim
        (familyLink.noRecursorRule hlinked hcatalog rule hrule))
    (by
      intro ruleIndex rule hrule
      exact False.elim
        (familyLink.noRecursorRuleAt hlinked hcatalog
          ruleIndex rule hrule))

def familyBlockCertificate :
    SemanticBlockTransitionCertificate RawProjRel.none world familyBlockId
      members .inductive' finalEnv where
  exactBlock := exactFamilyBlock
  fresh := by
    intro id hmember
    have hlinked : id ∈ familyLink.members := by
      rw [familyLink_members_eq]
      exact hmember
    exact familyLink.fresh id hlinked
  envLE := transaction.facts.envLE
  afterWF := transaction.facts.afterWF
  entry := fun {_} hmember => familySemanticEntry hmember

def familyAcceptedWorld : VerifyWorld :=
  familyBlockCertificate.admittedWorld

theorem familyAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none world familyAcceptedWorld
      familyBlockId members .inductive' :=
  familyBlockCertificate.admit trustedCatalog

theorem familyBlockAccepted :
    familyAcceptedWorld.AcceptedBlock familyBlockId :=
  familyAtomicAdmission.accepted

/-- End-to-end evidence for the currently supported recursive-Pi family
surface: the exact production checker run and the trust-minimal semantic
admission concern the same physical block and certified `Acc` transaction. -/
structure CheckedSemanticAdmission : Prop where
  ingress : ingressOutcome = .ok ingressResult ingressAfter
  checked :
    (RecM.checkInductiveBlock familyBlockId members).run checkerMethods
      checkerInitial = .ok () kernelAfter
  admitted :
    AtomicBlockAdmission RawProjRel.none world familyAcceptedWorld
      familyBlockId members .inductive'
  recursivePi : RecursivePiCertificateFixture.BreadthFacts

theorem checkedSemanticAdmission : CheckedSemanticAdmission where
  ingress := ingressRun
  checked := kernelRun
  admitted := familyAtomicAdmission
  recursivePi := breadth

end Ix.Tc.RecursivePiFixture
