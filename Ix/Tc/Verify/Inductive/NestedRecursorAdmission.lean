import Ix.Tc.Verify.Inductive.NestedRecursorSoundness
import Ix.Tc.Verify.Inductive.OneFamilyAdmission

/-!
# Atomic admission of the nested family and both restored recursors

The aux-aware compiler stores the source `LeanTree` block and a distinct
two-member recursor block.  Lean4Lean's nested transaction installs the
source family, constructor, both restored recursors, and both equations in
one semantic step.  This module reconciles those shapes as two exact physical
admissions: the source block advances the Theory environment, then the
already-installed recursor block is admitted with its two concrete iota
patterns.
-/

namespace Ix.Tc.NestedRecursiveFixture

open Lean4Lean
open InductiveConcreteFixture

local instance nestedRecursorAdmissionAddressDecidableEq :
    DecidableEq Address :=
  AnonStructural.addressDecidableEq

local instance nestedRecursorAdmissionKIdDecidableEq :
    DecidableEq (KId .anon) :=
  AnonStructural.idDecidableEq

local instance nestedRecursorAdmissionKConstDecidableEq :
    DecidableEq (KConst .anon) :=
  AnonStructural.constDecidableEq

/-! ## Immutable world and dependency log -/

def nestedRecursorBlockCatalog : BlockCatalog := fun id =>
  recursorIngressAfter.getBlock? id

def nestedRecursorWorld : VerifyWorld where
  catalog := nestedRecursorCatalog
  blocks := nestedRecursorBlockCatalog
  trusted := fun _ => False
  venv := semanticBoxEnv
  nameOf := nestedRecursorNameOf
  venvWF := semanticBoxEnvWF
  trustedCatalogued := fun {_} htrusted => False.elim htrusted

theorem nestedRecursorTrustedCatalog :
    TrustedCatalogRel RawProjRel.none nestedRecursorWorld := by
  change TrustedCatalogLog RawProjRel.none nestedRecursorCatalog
    nestedRecursorNameOf (fun _ => False) semanticBoxEnv
  simpa only [or_false] using
    (TrustedCatalogLog.semanticBlock
      (members := fun _ => False)
      (TrustedCatalogLog.empty (trProj := RawProjRel.none)
        (catalog := nestedRecursorCatalog)
        (nameOf := nestedRecursorNameOf))
      semanticBoxTransaction.facts.envLE semanticBoxEnvWF
      (fun {_} member => False.elim member))

/-! ## Source-family correspondence under the complete catalog -/

private theorem nestedRecursorTreeTypeRawNative :
    RawExprRel (uvars := treeConcrete.lvls.toNat) semanticTreeEnv
      nestedRecursorNameOf RawProjRel.none []
      treeConcrete.ty semanticTreeFamily.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem nestedRecursorTreeTypeRaw :
    RawExprRel (uvars := treeConcrete.lvls.toNat) semanticTreeEnv
      nestedRecursorNameOf RawProjRel.none []
      treeConcrete.ty semanticTreeFamily.type :=
  nestedRecursorTreeTypeRawNative

private theorem nestedRecursorNodeTypeRawNative :
    RawExprRel (uvars := nodeConcrete.lvls.toNat) semanticTreeEnv
      nestedRecursorNameOf RawProjRel.none []
      nodeConcrete.ty semanticTreeNode.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem nestedRecursorNodeTypeRaw :
    RawExprRel (uvars := nodeConcrete.lvls.toNat) semanticTreeEnv
      nestedRecursorNameOf RawProjRel.none []
      nodeConcrete.ty semanticTreeNode.type :=
  nestedRecursorNodeTypeRawNative

def nestedRecursorFamilyLink :
    NestedFamilyCatalogLink RawProjRel.none nestedRecursorWorld
      semanticTreeCertificate where
  members := nestedFamilyMembers
  nonempty := by decide
  member := by
    intro id hmember
    simp [nestedFamilyMembers] at hmember
    rcases hmember with rfl | rfl
    · exact ⟨treeConcrete, ``LeanTree, semanticTreeFamily.toVConstant,
        nestedRecursorCatalog_tree, nestedMemberShapeFacts.treeKind,
        nestedRecursorNameOf_tree, nestedMemberShapeFacts.treeUvars,
        nestedRecursorTreeTypeRaw,
        .inl ⟨semanticTreeType, by simp [semanticTreeDecl], rfl, rfl⟩⟩
    · exact ⟨nodeConcrete, ``LeanTree.node,
        semanticTreeNode.toVConstant, nestedRecursorCatalog_node,
        nestedMemberShapeFacts.nodeKind, nestedRecursorNameOf_node,
        nestedMemberShapeFacts.nodeUvars, nestedRecursorNodeTypeRaw,
        .inr ⟨semanticTreeNode, by
          rw [semanticTreeSourceInventory.2]
          simp, semanticTreeNodeName.symm, rfl⟩⟩
  fresh := by
    intro id _ htrusted
    exact htrusted

/-! ## Exact physical ownership -/

private def IsDirectNestedOwner
    (block : KId .anon) : KConst .anon → Prop
  | .indc (block := owner) .. => owner = block
  | _ => False

private def IsDirectNestedConstructor
    (family : KId .anon) : KConst .anon → Prop
  | .ctor (induct := parent) .. => parent = family
  | _ => False

local instance directNestedOwnerDecidable (block : KId .anon)
    (concrete : KConst .anon) :
    Decidable (IsDirectNestedOwner block concrete) := by
  cases concrete <;>
    simp only [IsDirectNestedOwner] <;> infer_instance

local instance directNestedConstructorDecidable (family : KId .anon)
    (concrete : KConst .anon) :
    Decidable (IsDirectNestedConstructor family concrete) := by
  cases concrete <;>
    simp only [IsDirectNestedConstructor] <;> infer_instance

local instance nestedRecursorOwnerDecidable (block : KId .anon)
    (concrete : KConst .anon) :
    Decidable (concrete.IsRecursorMemberOf block) := by
  cases concrete <;>
    simp only [KConst.IsRecursorMemberOf] <;> infer_instance

private theorem directNestedOwner_member
    {selectedCatalog : Catalog} {block : KId .anon}
    {concrete : KConst .anon}
    (owner : IsDirectNestedOwner block concrete) :
    concrete.IsInductiveMemberOf selectedCatalog block := by
  cases concrete <;>
    simp_all [IsDirectNestedOwner, KConst.IsInductiveMemberOf]

private theorem directNestedConstructor_member
    {selectedCatalog : Catalog} {block family : KId .anon}
    {concrete familyConcrete : KConst .anon}
    (constructor : IsDirectNestedConstructor family concrete)
    (familyLookup : selectedCatalog family = some familyConcrete)
    (owner : IsDirectNestedOwner block familyConcrete) :
    concrete.IsInductiveMemberOf selectedCatalog block := by
  cases concrete <;>
    simp_all [IsDirectNestedConstructor, KConst.IsInductiveMemberOf,
      IsDirectNestedOwner]
  exact owner

private theorem directNestedOwner_not_member
    {selectedCatalog : Catalog} {ownerBlock targetBlock : KId .anon}
    {concrete : KConst .anon}
    (owner : IsDirectNestedOwner ownerBlock concrete)
    (different : ownerBlock ≠ targetBlock) :
    ¬concrete.IsInductiveMemberOf selectedCatalog targetBlock := by
  intro member
  cases concrete <;>
    simp_all [IsDirectNestedOwner, KConst.IsInductiveMemberOf]

private theorem directNestedConstructor_not_member
    {selectedCatalog : Catalog}
    {ownerBlock targetBlock family : KId .anon}
    {concrete familyConcrete : KConst .anon}
    (constructor : IsDirectNestedConstructor family concrete)
    (familyLookup : selectedCatalog family = some familyConcrete)
    (owner : IsDirectNestedOwner ownerBlock familyConcrete)
    (different : ownerBlock ≠ targetBlock) :
    ¬concrete.IsInductiveMemberOf selectedCatalog targetBlock := by
  intro member
  cases concrete <;>
    simp_all [IsDirectNestedConstructor, KConst.IsInductiveMemberOf,
      IsDirectNestedOwner]
  cases familyConcrete <;> simp_all

private theorem directNestedOwner_not_recursor
    {block : KId .anon} {concrete : KConst .anon}
    (owner : IsDirectNestedOwner block concrete) (target : KId .anon) :
    ¬concrete.IsRecursorMemberOf target := by
  intro member
  cases concrete <;>
    simp_all [IsDirectNestedOwner, KConst.IsRecursorMemberOf]

private theorem directNestedConstructor_not_recursor
    {family : KId .anon} {concrete : KConst .anon}
    (constructor : IsDirectNestedConstructor family concrete)
    (target : KId .anon) :
    ¬concrete.IsRecursorMemberOf target := by
  intro member
  cases concrete <;>
    simp_all [IsDirectNestedConstructor, KConst.IsRecursorMemberOf]

private theorem directRecursor_not_inductive
    {selectedCatalog : Catalog} {block : KId .anon}
    {concrete : KConst .anon}
    (owner : concrete.IsRecursorMemberOf block) (target : KId .anon) :
    ¬concrete.IsInductiveMemberOf selectedCatalog target := by
  intro member
  cases concrete <;>
    simp_all [KConst.IsRecursorMemberOf, KConst.IsInductiveMemberOf]

private theorem nestedBoxDirectOwner :
    IsDirectNestedOwner boxBlockId boxConcrete := by
  native_decide

private theorem nestedTreeDirectOwnerComplete :
    IsDirectNestedOwner treeBlockId treeConcrete := by
  native_decide

private theorem nestedWrapDirectConstructor :
    IsDirectNestedConstructor boxId wrapConcrete := by
  native_decide

private theorem nestedNodeDirectConstructorComplete :
    IsDirectNestedConstructor treeId nodeConcrete := by
  native_decide

private theorem nestedBlocksDistinct : boxBlockId ≠ treeBlockId := by
  native_decide

private theorem treeRecDirectOwner :
    treeRecConcrete.IsRecursorMemberOf recursorBlockId := by
  native_decide

private theorem treeRecOneDirectOwner :
    treeRecOneConcrete.IsRecursorMemberOf recursorBlockId := by
  native_decide

theorem nestedRecursorTreeFamilyOwner :
    treeConcrete.IsInductiveMemberOf nestedRecursorCatalog treeBlockId :=
  directNestedOwner_member nestedTreeDirectOwnerComplete

theorem nestedRecursorNodeFamilyOwner :
    nodeConcrete.IsInductiveMemberOf nestedRecursorCatalog treeBlockId :=
  directNestedConstructor_member nestedNodeDirectConstructorComplete
    nestedRecursorCatalog_tree nestedTreeDirectOwnerComplete

private theorem nestedBoxNotTreeFamilyOwner :
    ¬boxConcrete.IsInductiveMemberOf nestedRecursorCatalog treeBlockId :=
  directNestedOwner_not_member nestedBoxDirectOwner nestedBlocksDistinct

private theorem nestedWrapNotTreeFamilyOwner :
    ¬wrapConcrete.IsInductiveMemberOf nestedRecursorCatalog treeBlockId :=
  directNestedConstructor_not_member nestedWrapDirectConstructor
    nestedRecursorCatalog_box nestedBoxDirectOwner nestedBlocksDistinct

private theorem treeRecNotTreeFamilyOwner :
    ¬treeRecConcrete.IsInductiveMemberOf nestedRecursorCatalog treeBlockId :=
  directRecursor_not_inductive treeRecDirectOwner treeBlockId

private theorem treeRecOneNotTreeFamilyOwner :
    ¬treeRecOneConcrete.IsInductiveMemberOf nestedRecursorCatalog
      treeBlockId :=
  directRecursor_not_inductive treeRecOneDirectOwner treeBlockId

private theorem nestedBoxNotRecursorOwner :
    ¬boxConcrete.IsRecursorMemberOf recursorBlockId :=
  directNestedOwner_not_recursor nestedBoxDirectOwner recursorBlockId

private theorem nestedWrapNotRecursorOwner :
    ¬wrapConcrete.IsRecursorMemberOf recursorBlockId :=
  directNestedConstructor_not_recursor nestedWrapDirectConstructor
    recursorBlockId

private theorem nestedTreeNotRecursorOwner :
    ¬treeConcrete.IsRecursorMemberOf recursorBlockId :=
  directNestedOwner_not_recursor nestedTreeDirectOwnerComplete
    recursorBlockId

private theorem nestedNodeNotRecursorOwner :
    ¬nodeConcrete.IsRecursorMemberOf recursorBlockId :=
  directNestedConstructor_not_recursor nestedNodeDirectConstructorComplete
    recursorBlockId

theorem nestedRecursorCatalog_entry_cases {id : KId .anon}
    {concrete : KConst .anon}
    (hcatalog : nestedRecursorCatalog id = some concrete) :
    (id = boxId ∧ concrete = boxConcrete) ∨
      (id = wrapId ∧ concrete = wrapConcrete) ∨
      (id = treeId ∧ concrete = treeConcrete) ∨
      (id = nodeId ∧ concrete = nodeConcrete) ∨
      (id = treeRecId ∧ concrete = treeRecConcrete) ∨
      (id = treeRecOneId ∧ concrete = treeRecOneConcrete) := by
  unfold nestedRecursorCatalog at hcatalog
  split at hcatalog
  · left
    exact ⟨eq_of_beq (by assumption),
      (Option.some.inj hcatalog).symm⟩
  · split at hcatalog
    · right; left
      exact ⟨eq_of_beq (by assumption),
        (Option.some.inj hcatalog).symm⟩
    · split at hcatalog
      · right; right; left
        exact ⟨eq_of_beq (by assumption),
          (Option.some.inj hcatalog).symm⟩
      · split at hcatalog
        · right; right; right; left
          exact ⟨eq_of_beq (by assumption),
            (Option.some.inj hcatalog).symm⟩
        · split at hcatalog
          · right; right; right; right; left
            exact ⟨eq_of_beq (by assumption),
              (Option.some.inj hcatalog).symm⟩
          · split at hcatalog
            · right; right; right; right; right
              exact ⟨eq_of_beq (by assumption),
                (Option.some.inj hcatalog).symm⟩
            · contradiction

theorem nestedRecursorFamilyCoordinated_iff (id : KId .anon) :
    id ∈ nestedFamilyMembers ↔
      nestedRecursorCatalog.CoordinatedMember treeBlockId .inductive' id := by
  constructor
  · intro hmember
    simp [nestedFamilyMembers] at hmember
    rcases hmember with rfl | rfl
    · exact ⟨treeConcrete, nestedRecursorCatalog_tree,
        nestedRecursorTreeFamilyOwner⟩
    · exact ⟨nodeConcrete, nestedRecursorCatalog_node,
        nestedRecursorNodeFamilyOwner⟩
  · rintro ⟨concrete, hcatalog, howner⟩
    rcases nestedRecursorCatalog_entry_cases hcatalog with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact False.elim (nestedBoxNotTreeFamilyOwner howner)
    · exact False.elim (nestedWrapNotTreeFamilyOwner howner)
    · simp [nestedFamilyMembers]
    · simp [nestedFamilyMembers]
    · exact False.elim (treeRecNotTreeFamilyOwner howner)
    · exact False.elim (treeRecOneNotTreeFamilyOwner howner)

theorem nestedRecursorCoordinated_iff (id : KId .anon) :
    id ∈ recursorMembers ↔
      nestedRecursorCatalog.CoordinatedMember recursorBlockId .recursor id := by
  constructor
  · intro hmember
    simp [recursorMembers] at hmember
    rcases hmember with rfl | rfl
    · exact ⟨treeRecConcrete, nestedRecursorCatalog_treeRec,
        treeRecDirectOwner⟩
    · exact ⟨treeRecOneConcrete, nestedRecursorCatalog_treeRecOne,
        treeRecOneDirectOwner⟩
  · rintro ⟨concrete, hcatalog, howner⟩
    rcases nestedRecursorCatalog_entry_cases hcatalog with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact False.elim (nestedBoxNotRecursorOwner howner)
    · exact False.elim (nestedWrapNotRecursorOwner howner)
    · exact False.elim (nestedTreeNotRecursorOwner howner)
    · exact False.elim (nestedNodeNotRecursorOwner howner)
    · simp [recursorMembers]
    · simp [recursorMembers]

theorem nestedRecursorWorld_familyBlock :
    nestedRecursorWorld.blocks treeBlockId = some nestedFamilyMembers := by
  change recursorIngressAfter.getBlock? treeBlockId =
    some nestedFamilyMembers
  simpa [nestedRecursorCheckerInitial, TcState.ofEnvAnon] using
    nestedRecursorFamilyBlockLoaded

theorem nestedRecursorWorld_recursorBlock :
    nestedRecursorWorld.blocks recursorBlockId = some recursorMembers := by
  change recursorIngressAfter.getBlock? recursorBlockId =
    some recursorMembers
  simpa [nestedRecursorCheckerInitial, TcState.ofEnvAnon] using
    nestedRecursorBlockLoaded

def exactNestedRecursorFamilyBlock :
    ExactCheckBlock nestedRecursorWorld treeBlockId nestedFamilyMembers
      .inductive' where
  blockLookup := nestedRecursorWorld_familyBlock
  nonempty := by decide
  memberIff := nestedRecursorFamilyCoordinated_iff

def exactNestedRecursorBlock :
    ExactCheckBlock nestedRecursorWorld recursorBlockId recursorMembers
      .recursor where
  blockLookup := nestedRecursorWorld_recursorBlock
  nonempty := by decide
  memberIff := nestedRecursorCoordinated_iff

/-! ## Source transition -/

theorem nestedRecursorFamilyBlockCertificate :
    SemanticBlockTransitionCertificate RawProjRel.none nestedRecursorWorld
      treeBlockId nestedFamilyMembers .inductive' semanticTreeEnv :=
  nestedRecursorFamilyLink.transition exactNestedRecursorFamilyBlock

def nestedRecursorFamilyAcceptedWorld : VerifyWorld :=
  nestedRecursorFamilyBlockCertificate.admittedWorld

theorem nestedRecursorFamilyAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none nestedRecursorWorld
      nestedRecursorFamilyAcceptedWorld treeBlockId nestedFamilyMembers
        .inductive' :=
  nestedRecursorFamilyBlockCertificate.admit nestedRecursorTrustedCatalog

/-! ## Existing two-recursor transition -/

private theorem treeRecRuleIndexBound {index : Nat}
    {rule : RecRule .anon}
    (hrule : treeRecConcrete.RecursorRuleAt index rule) : index < 1 := by
  rw [treeRecRuleAt_iff] at hrule
  have bound := (Array.getElem?_eq_some_iff.mp hrule).choose
  simpa [nestedRecursorRepresentationFacts.treeRuleCount] using bound

private theorem treeRecOneRuleIndexBound {index : Nat}
    {rule : RecRule .anon}
    (hrule : treeRecOneConcrete.RecursorRuleAt index rule) : index < 1 := by
  rw [treeRecOneRuleAt_iff] at hrule
  have bound := (Array.getElem?_eq_some_iff.mp hrule).choose
  simpa [nestedRecursorRepresentationFacts.treeRecOneRuleCount] using bound

private theorem treeRecRegisteredRule {rule : RecRule .anon}
    (hrule : treeRecConcrete.HasRecursorRule rule) :
    RawRecursorRuleRel semanticTreeEnv nestedRecursorNameOf RawProjRel.none
      treeRecId treeRecConcrete rule := by
  obtain ⟨index, hindex⟩ := hrule.exists_ruleAt
  have hbound := treeRecRuleIndexBound hindex
  have hzero : index = 0 := by omega
  subst index
  have equality := KConst.RecursorRuleAt.unique hindex treeNodeRecRuleAt
  subst rule
  exact ⟨_, treeNodeRuleRegistered⟩

private theorem treeRecOneRegisteredRule {rule : RecRule .anon}
    (hrule : treeRecOneConcrete.HasRecursorRule rule) :
    RawRecursorRuleRel semanticTreeEnv nestedRecursorNameOf RawProjRel.none
      treeRecOneId treeRecOneConcrete rule := by
  obtain ⟨index, hindex⟩ := hrule.exists_ruleAt
  have hbound := treeRecOneRuleIndexBound hindex
  have hzero : index = 0 := by omega
  subst index
  have equality := KConst.RecursorRuleAt.unique hindex treeWrapRecRuleAt
  subst rule
  exact ⟨_, treeWrapRuleRegistered⟩

private theorem treeRecPattern {index : Nat} {rule : RecRule .anon}
    (hrule : treeRecConcrete.RecursorRuleAt index rule) :
    ∃ pattern,
      RawRecursorRulePatternRel semanticTreeEnv nestedRecursorCatalog
        nestedRecursorNameOf treeRecId treeRecConcrete rule pattern ∧
        pattern.ruleIndex = index := by
  have hbound := treeRecRuleIndexBound hrule
  have hzero : index = 0 := by omega
  subst index
  have equality := KConst.RecursorRuleAt.unique hrule treeNodeRecRuleAt
  subst rule
  exact ⟨treeNodePattern, treeNodePatternRel, rfl⟩

private theorem treeRecOnePattern {index : Nat} {rule : RecRule .anon}
    (hrule : treeRecOneConcrete.RecursorRuleAt index rule) :
    ∃ pattern,
      RawRecursorRulePatternRel semanticTreeEnv nestedRecursorCatalog
        nestedRecursorNameOf treeRecOneId treeRecOneConcrete rule pattern ∧
        pattern.ruleIndex = index := by
  have hbound := treeRecOneRuleIndexBound hrule
  have hzero : index = 0 := by omega
  subst index
  have equality := KConst.RecursorRuleAt.unique hrule treeWrapRecRuleAt
  subst rule
  exact ⟨treeWrapPattern, treeWrapPatternRel, rfl⟩

private theorem treeRecSemanticEntry :
    TrustedCatalogEntry RawProjRel.none nestedRecursorCatalog
      nestedRecursorNameOf semanticTreeEnv treeRecId :=
  .ambient nestedRecursorCatalog_treeRec treeRecRaw
    semanticTreeTransactionFacts.primaryRecursor
    (semanticTreeEnvWF.ordered.constWF
      semanticTreeTransactionFacts.primaryRecursor)
    (fun {_} hrule => treeRecRegisteredRule hrule)
    (fun {_ _} hrule => treeRecPattern hrule)

private theorem treeRecOneSemanticEntry :
    TrustedCatalogEntry RawProjRel.none nestedRecursorCatalog
      nestedRecursorNameOf semanticTreeEnv treeRecOneId :=
  .ambient nestedRecursorCatalog_treeRecOne treeRecOneRaw
    semanticTreeTransactionFacts.dependencyRecursor
    (semanticTreeEnvWF.ordered.constWF
      semanticTreeTransactionFacts.dependencyRecursor)
    (fun {_} hrule => treeRecOneRegisteredRule hrule)
    (fun {_ _} hrule => treeRecOnePattern hrule)

theorem nestedFamilyTreeRecSemanticEntry :
    TrustedCatalogEntry RawProjRel.none
      nestedRecursorFamilyAcceptedWorld.catalog
      nestedRecursorFamilyAcceptedWorld.nameOf
      nestedRecursorFamilyAcceptedWorld.venv treeRecId := by
  change TrustedCatalogEntry RawProjRel.none nestedRecursorCatalog
    nestedRecursorNameOf semanticTreeEnv treeRecId
  exact treeRecSemanticEntry

theorem nestedFamilyTreeRecOneSemanticEntry :
    TrustedCatalogEntry RawProjRel.none
      nestedRecursorFamilyAcceptedWorld.catalog
      nestedRecursorFamilyAcceptedWorld.nameOf
      nestedRecursorFamilyAcceptedWorld.venv treeRecOneId := by
  change TrustedCatalogEntry RawProjRel.none nestedRecursorCatalog
    nestedRecursorNameOf semanticTreeEnv treeRecOneId
  exact treeRecOneSemanticEntry

private theorem treeRecNotFamily : treeRecId ∉ nestedFamilyMembers := by
  native_decide

private theorem treeRecOneNotFamily :
    treeRecOneId ∉ nestedFamilyMembers := by
  native_decide

theorem nestedRecursorFamilyAccepted_recursorsFresh {id : KId .anon}
    (hmember : id ∈ recursorMembers) :
    ¬nestedRecursorFamilyAcceptedWorld.trusted id := by
  change ¬(id ∈ nestedFamilyMembers ∨ nestedRecursorWorld.trusted id)
  simp [recursorMembers] at hmember
  rcases hmember with rfl | rfl
  · intro htrusted
    rcases htrusted with hfamily | hold
    · exact treeRecNotFamily hfamily
    · exact hold
  · intro htrusted
    rcases htrusted with hfamily | hold
    · exact treeRecOneNotFamily hfamily
    · exact hold

theorem exactNestedRecursorBlockAfterFamily :
    ExactCheckBlock nestedRecursorFamilyAcceptedWorld recursorBlockId
      recursorMembers .recursor :=
  exactNestedRecursorBlock.rebaseWorld
    nestedRecursorFamilyAtomicAdmission.promotion.le

theorem nestedExistingRecursorBlockCertificate :
    ExistingSemanticBlockCertificate RawProjRel.none
      nestedRecursorFamilyAcceptedWorld recursorBlockId recursorMembers
        .recursor where
  exactBlock := exactNestedRecursorBlockAfterFamily
  fresh := fun {_} hmember =>
    nestedRecursorFamilyAccepted_recursorsFresh hmember
  entry := by
    intro id hmember
    simp [recursorMembers] at hmember
    rcases hmember with rfl | rfl
    · exact nestedFamilyTreeRecSemanticEntry
    · exact nestedFamilyTreeRecOneSemanticEntry

/-- The generic two-stage certificate instantiated by the nested source
transaction and its physical two-recursor block. -/
def nestedOneFamilyCertificate :
    OneFamilyRecursorCertificate RawProjRel.none nestedRecursorWorld
      treeBlockId nestedFamilyMembers recursorBlockId recursorMembers
        semanticTreeEnv where
  family := nestedRecursorFamilyBlockCertificate
  recursor := nestedExistingRecursorBlockCertificate

def nestedRecursorAcceptedWorld : VerifyWorld :=
  nestedOneFamilyCertificate.admittedWorld

theorem nestedRecursorAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none nestedRecursorFamilyAcceptedWorld
      nestedRecursorAcceptedWorld recursorBlockId recursorMembers .recursor :=
  nestedOneFamilyCertificate.recursorAdmission nestedRecursorTrustedCatalog

theorem nestedOneFamilyAtomicClosure :
    nestedOneFamilyCertificate.AtomicClosure :=
  nestedOneFamilyCertificate.atomicClosure nestedRecursorTrustedCatalog

/-! ## End-to-end closure -/

structure NestedRecursorAtomicClosure : Prop where
  compiler : nestedCompilerOutcome = .ok nestedCompilerResult
  grounded : nestedCompiledState.ungrounded.isEmpty = true
  identity : NestedCompiledIdentityFacts
  ingress : recursorIngressOutcome =
    .ok recursorIngressResult recursorIngressAfter
  ingressIds : recursorIngressResult.allEntries.map (·.1) = recursorMembers
  ingressUnique : EntryKeysUnique recursorIngressResult.allEntries
  familyChecked :
    (RecM.checkInductiveBlock treeBlockId nestedFamilyMembers).run
      checkerMethods nestedRecursorCheckerInitial =
        .ok () nestedRecursorFamilyAfter
  recursorChecked :
    (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
      checkerMethods nestedRecursorFamilyAfter =
        .ok () nestedRecursorKernelAfter
  semantic : SemanticTreeTransactionFacts
  restoredPatterns : NestedRestoredPatternSound
  familyAdmission :
    AtomicBlockAdmission RawProjRel.none nestedRecursorWorld
      nestedRecursorFamilyAcceptedWorld treeBlockId nestedFamilyMembers
        .inductive'
  recursorAdmission :
    AtomicBlockAdmission RawProjRel.none nestedRecursorFamilyAcceptedWorld
      nestedRecursorAcceptedWorld recursorBlockId recursorMembers .recursor
  oneFamily : nestedOneFamilyCertificate.AtomicClosure
  familyAccepted : nestedRecursorAcceptedWorld.AcceptedBlock treeBlockId
  recursorAccepted : nestedRecursorAcceptedWorld.AcceptedBlock recursorBlockId

theorem nestedRecursorAtomicClosure : NestedRecursorAtomicClosure where
  compiler := nestedCompilerRun
  grounded := nestedCompilerGrounded
  identity := nestedCompiledIdentityFacts
  ingress := recursorIngressRun
  ingressIds := recursorEntryIds
  ingressUnique := recursorEntriesUnique
  familyChecked := nestedRecursorFamilyRun
  recursorChecked := nestedRecursorKernelRun
  semantic := semanticTreeTransactionFacts
  restoredPatterns := nestedRestoredPatternSound
  familyAdmission := nestedRecursorFamilyAtomicAdmission
  recursorAdmission := nestedRecursorAtomicAdmission
  oneFamily := nestedOneFamilyAtomicClosure
  familyAccepted := nestedOneFamilyAtomicClosure.familyAccepted
  recursorAccepted := nestedOneFamilyAtomicClosure.recursorAccepted

end Ix.Tc.NestedRecursiveFixture
