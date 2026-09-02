import Ix.Tc.Verify.Inductive.RecursivePiSoundness
import Ix.Tc.Verify.Inductive.OneFamilyAdmission

/-!
# Oracle-free recursive-Pi admission

This module closes the concrete `Acc` E2c transaction.  The family and its
constructor are admitted by the exact certified Theory-environment
transition.  The separately ingressed and production-checked `Acc.rec` block
is then admitted from semantic entries already installed by that transition.
No `InductiveOracle`, ambient future-world choice, or sequential stand-in for
a mutual declaration is used.
-/

namespace Ix.Tc.RecursivePiRecursorFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open RecursivePiCertificateFixture
open RecursivePiFixture

local instance admissionAnonKIdDecidableEq : DecidableEq (KId .anon) :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by cases equality; exact beq_self_eq_true left)

def familyMembers : Array (KId .anon) := RecursivePiFixture.members

@[simp] theorem familyMembers_eq :
    familyMembers = #[familyId, introId] := rfl

/-! ## Exact physical ownership in the complete catalog -/

private def IsDirectInductiveOwner
    (block : KId .anon) : KConst .anon → Prop
  | .indc (block := owner) .. => owner = block
  | _ => False

local instance directInductiveOwnerDecidable (block : KId .anon)
    (concrete : KConst .anon) :
    Decidable (IsDirectInductiveOwner block concrete) := by
  cases concrete <;> simp only [IsDirectInductiveOwner] <;> infer_instance

local instance recursorOwnerDecidable (block : KId .anon)
    (concrete : KConst .anon) :
    Decidable (concrete.IsRecursorMemberOf block) := by
  cases concrete <;>
    simp only [KConst.IsRecursorMemberOf] <;> infer_instance

private theorem directInductiveOwner_inductiveMemberOf
    {selectedCatalog : Catalog} {block : KId .anon}
    {concrete : KConst .anon}
    (howner : IsDirectInductiveOwner block concrete) :
    concrete.IsInductiveMemberOf selectedCatalog block := by
  cases concrete <;>
    simp_all [IsDirectInductiveOwner, KConst.IsInductiveMemberOf]

private theorem certifiedConstructor_inductiveMemberOf
    {source : VInductDecl} {familyId block : KId .anon}
    {index : Nat} {sourceConstructor : VConstVal}
    {concrete familyConcrete : KConst .anon}
    {selectedCatalog : Catalog}
    (hshape : concrete.IsCertifiedSingletonConstructor source familyId index
      sourceConstructor)
    (hcatalog : selectedCatalog familyId = some familyConcrete)
    (hfamilyOwner : IsDirectInductiveOwner block familyConcrete) :
    concrete.IsInductiveMemberOf selectedCatalog block := by
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonConstructor,
      KConst.IsInductiveMemberOf, IsDirectInductiveOwner]
  exact hfamilyOwner

private theorem certifiedRecursor_not_inductiveMemberOf
    {source : VInductDecl} {sourceGeneration : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    {selectedCatalog : Catalog} {block : KId .anon}
    (hshape : concrete.IsCertifiedSingletonRecursor source sourceGeneration
      constructorIds) :
    ¬concrete.IsInductiveMemberOf selectedCatalog block := by
  intro howner
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonRecursor,
      KConst.IsInductiveMemberOf]

private theorem certifiedFamily_not_recursorMemberOf
    {source : VInductDecl} {sourceGeneration : source.GenerationChecked}
    {constructorIds : Array (KId .anon)} {concrete : KConst .anon}
    {block : KId .anon}
    (hshape : concrete.IsCertifiedSingletonFamily source sourceGeneration
      constructorIds) :
    ¬concrete.IsRecursorMemberOf block := by
  intro howner
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonFamily,
      KConst.IsRecursorMemberOf]

private theorem certifiedConstructor_not_recursorMemberOf
    {source : VInductDecl} {familyId : KId .anon}
    {index : Nat} {sourceConstructor : VConstVal}
    {concrete : KConst .anon} {block : KId .anon}
    (hshape : concrete.IsCertifiedSingletonConstructor source familyId index
      sourceConstructor) :
    ¬concrete.IsRecursorMemberOf block := by
  intro howner
  cases concrete <;>
    simp_all [KConst.IsCertifiedSingletonConstructor,
      KConst.IsRecursorMemberOf]

private theorem familyDirectOwnerNative :
    IsDirectInductiveOwner familyBlockId
      RecursivePiFixture.familyConcrete := by
  native_decide

theorem familyOwner :
    RecursivePiFixture.familyConcrete.IsInductiveMemberOf catalog
      familyBlockId :=
  directInductiveOwner_inductiveMemberOf familyDirectOwnerNative

theorem introOwner :
    RecursivePiFixture.introConcrete.IsInductiveMemberOf catalog
      familyBlockId :=
  certifiedConstructor_inductiveMemberOf RecursivePiFixture.introShape
    catalog_family familyDirectOwnerNative

theorem recursorNotFamilyOwner :
    ¬recursorConcrete.IsInductiveMemberOf catalog familyBlockId :=
  certifiedRecursor_not_inductiveMemberOf recursorShape

private theorem recursorOwnerNative :
    recursorConcrete.IsRecursorMemberOf recursorBlockId := by
  native_decide

theorem recursorOwner :
    recursorConcrete.IsRecursorMemberOf recursorBlockId :=
  recursorOwnerNative

theorem familyNotRecursorOwner :
    ¬RecursivePiFixture.familyConcrete.IsRecursorMemberOf recursorBlockId :=
  certifiedFamily_not_recursorMemberOf RecursivePiFixture.familyShape

theorem introNotRecursorOwner :
    ¬RecursivePiFixture.introConcrete.IsRecursorMemberOf recursorBlockId :=
  certifiedConstructor_not_recursorMemberOf RecursivePiFixture.introShape

/-- Every successful lookup in the complete fixture catalog is one of the
family, constructor, or generated recursor entries. -/
theorem catalog_entry_cases {id : KId .anon} {concrete : KConst .anon}
    (hcatalog : catalog id = some concrete) :
    (id = familyId ∧ concrete = RecursivePiFixture.familyConcrete) ∨
      (id = introId ∧ concrete = RecursivePiFixture.introConcrete) ∨
      (id = recursorId ∧ concrete = recursorConcrete) := by
  unfold catalog at hcatalog
  split at hcatalog
  · left
    exact ⟨eq_of_beq (by assumption), (Option.some.inj hcatalog).symm⟩
  · split at hcatalog
    · right; left
      exact ⟨eq_of_beq (by assumption), (Option.some.inj hcatalog).symm⟩
    · split at hcatalog
      · right; right
        exact ⟨eq_of_beq (by assumption),
          (Option.some.inj hcatalog).symm⟩
      · contradiction

theorem familyCoordinated_iff (id : KId .anon) :
    id ∈ familyMembers ↔
      catalog.CoordinatedMember familyBlockId .inductive' id := by
  constructor
  · intro hmember
    simp [familyMembers_eq] at hmember
    rcases hmember with rfl | rfl
    · exact ⟨RecursivePiFixture.familyConcrete, catalog_family, familyOwner⟩
    · exact ⟨RecursivePiFixture.introConcrete, catalog_intro, introOwner⟩
  · rintro ⟨concrete, hcatalog, howner⟩
    rcases catalog_entry_cases hcatalog with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [familyMembers_eq]
    · simp [familyMembers_eq]
    · exact False.elim (recursorNotFamilyOwner howner)

theorem recursorCoordinated_iff (id : KId .anon) :
    id ∈ recursorMembers ↔
      catalog.CoordinatedMember recursorBlockId .recursor id := by
  constructor
  · intro hmember
    have hid : id = recursorId := by simpa [recursorMembers] using hmember
    subst id
    exact ⟨recursorConcrete, catalog_recursor, recursorOwner⟩
  · rintro ⟨concrete, hcatalog, howner⟩
    rcases catalog_entry_cases hcatalog with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact False.elim (familyNotRecursorOwner howner)
    · exact False.elim (introNotRecursorOwner howner)
    · simp [recursorMembers]

theorem world_family_block :
    world.blocks familyBlockId = some familyMembers := by
  change recursorIngressAfter.getBlock? familyBlockId = some familyMembers
  simpa [familyMembers, checkerInitial, TcState.ofEnvAnon] using
    familyBlockLoaded

theorem world_recursor_block :
    world.blocks recursorBlockId = some recursorMembers := by
  change recursorIngressAfter.getBlock? recursorBlockId = some recursorMembers
  simpa [checkerInitial, TcState.ofEnvAnon] using recursorBlockLoaded

def exactFamilyBlock :
    ExactCheckBlock world familyBlockId familyMembers .inductive' where
  blockLookup := world_family_block
  nonempty := by rw [familyMembers_eq]; decide
  memberIff := familyCoordinated_iff

def exactRecursorBlock :
    ExactCheckBlock world recursorBlockId recursorMembers .recursor where
  blockLookup := world_recursor_block
  nonempty := by rw [show recursorMembers = #[recursorId] from rfl]; decide
  memberIff := recursorCoordinated_iff

/-! ## Exact family transition -/

theorem familyLink_members_eq : familyLink.members = familyMembers := by
  rfl

private def familySemanticEntry {id : KId .anon}
    (hmember : id ∈ familyMembers) :
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
      familyMembers .inductive' finalEnv where
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
      familyBlockId familyMembers .inductive' :=
  familyBlockCertificate.admit trustedCatalog

/-! ## Existing generated-recursor transition -/

private def recursorSemanticEntryBase :
    TrustedCatalogEntry RawProjRel.none world.catalog world.nameOf finalEnv
      recursorId := by
  obtain ⟨hraw, hlookup, hwf⟩ := recursorLink.translateRecursor
  refine .ambient catalog_recursor hraw hlookup hwf ?_ ?_
  · intro rule hrule
    exact recursorLink.registeredRule hrule
  · intro ruleIndex rule hrule
    have hcount : familyLink.constructorIds.size = 1 := by rfl
    have hbound := recursorLink.recursorShape.ruleCount hrule
    have hzero : 0 < familyLink.constructorIds.size := by omega
    have hindex : ruleIndex = 0 := by omega
    subst ruleIndex
    exact ⟨RecursivePiPattern.pattern introId,
      RecursivePiPattern.patternRel hrule, rfl⟩

def familyRecursorSemanticEntry :
    TrustedCatalogEntry RawProjRel.none familyAcceptedWorld.catalog
      familyAcceptedWorld.nameOf familyAcceptedWorld.venv recursorId := by
  change TrustedCatalogEntry RawProjRel.none world.catalog world.nameOf
    finalEnv recursorId
  exact recursorSemanticEntryBase

theorem familyAcceptedWorld_recursor_fresh :
    ¬familyAcceptedWorld.trusted recursorId := by
  intro htrusted
  change recursorId ∈ familyMembers ∨ world.trusted recursorId at htrusted
  rcases htrusted with hfamily | hold
  · have hcoordinated := (familyCoordinated_iff recursorId).1 hfamily
    obtain ⟨concrete, hcatalog, howner⟩ := hcoordinated
    rw [catalog_recursor] at hcatalog
    cases hcatalog
    exact recursorNotFamilyOwner howner
  · exact recursorLink.fresh hold

def exactRecursorBlockAfterFamily :
    ExactCheckBlock familyAcceptedWorld recursorBlockId recursorMembers
      .recursor :=
  exactRecursorBlock.rebaseWorld familyAtomicAdmission.promotion.le

def familyRecursorBlockCertificate :
    ExistingSemanticBlockCertificate RawProjRel.none familyAcceptedWorld
      recursorBlockId recursorMembers .recursor where
  exactBlock := exactRecursorBlockAfterFamily
  fresh := by
    intro id hmember
    have hid : id = recursorId := by
      simpa [recursorMembers] using hmember
    subst id
    exact familyAcceptedWorld_recursor_fresh
  entry := by
    intro id hmember
    have hid : id = recursorId := by
      simpa [recursorMembers] using hmember
    subst id
    exact familyRecursorSemanticEntry

/-- Generic one-family certificate instantiated by the concrete recursive-Pi
family transition and its separately checked generated recursor block. -/
def oneFamilyCertificate :
    OneFamilyRecursorCertificate RawProjRel.none world familyBlockId
      familyMembers recursorBlockId recursorMembers finalEnv where
  family := familyBlockCertificate
  recursor := familyRecursorBlockCertificate

def familyRecursorAcceptedWorld : VerifyWorld :=
  oneFamilyCertificate.admittedWorld

theorem familyRecursorAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none familyAcceptedWorld
      familyRecursorAcceptedWorld recursorBlockId recursorMembers
      .recursor :=
  oneFamilyCertificate.recursorAdmission trustedCatalog

/-- The reusable one-family closure theorem specializes to the complete
recursive-Pi family/recursor pair. -/
theorem oneFamilyAtomicClosure : oneFamilyCertificate.AtomicClosure :=
  oneFamilyCertificate.atomicClosure trustedCatalog

/-- One theorem joins both real ingress/check executions to the two exact
semantic admissions and the registered recursive-Pi iota equation. -/
structure RecursivePiAtomicClosure : Prop where
  familyIngress :
    RecursivePiFixture.ingressOutcome =
      .ok RecursivePiFixture.ingressResult RecursivePiFixture.ingressAfter
  recursorIngress :
    recursorIngressOutcome =
      .ok recursorIngressResult recursorIngressAfter
  familyChecked :
    (RecM.checkInductiveBlock familyBlockId familyMembers).run checkerMethods
      checkerInitial = .ok () familyKernelAfter
  recursorChecked :
    (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
      checkerMethods familyKernelAfter = .ok () recursorKernelAfter
  familyAdmission :
    AtomicBlockAdmission RawProjRel.none world familyAcceptedWorld
      familyBlockId familyMembers .inductive'
  recursorAdmission :
    AtomicBlockAdmission RawProjRel.none familyAcceptedWorld
      familyRecursorAcceptedWorld recursorBlockId recursorMembers .recursor
  oneFamily : oneFamilyCertificate.AtomicClosure
  iota :
    RawRecursorRulePatternRel finalEnv catalog nameOf recursorId
      recursorConcrete concreteRule
      (RecursivePiPattern.pattern introId)
  recursivePi : RecursivePiCertificateFixture.BreadthFacts

theorem recursivePiAtomicClosure : RecursivePiAtomicClosure where
  familyIngress := RecursivePiFixture.ingressRun
  recursorIngress := recursorIngressRun
  familyChecked := by
    simpa [familyMembers] using familyKernelRun
  recursorChecked := recursorKernelRun
  familyAdmission := familyAtomicAdmission
  recursorAdmission := familyRecursorAtomicAdmission
  oneFamily := oneFamilyAtomicClosure
  iota := RecursivePiPattern.patternRel concreteRule_ruleAt
  recursivePi := RecursivePiCertificateFixture.breadth

end Ix.Tc.RecursivePiRecursorFixture
