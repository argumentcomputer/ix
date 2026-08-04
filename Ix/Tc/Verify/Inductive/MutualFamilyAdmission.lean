import Ix.Tc.Verify.Inductive.MutualBlockValidation
import Ix.Tc.Verify.Inductive.MutualFamily

/-!
# Atomic mutual `Tree`/`TreeList` family admission

This module joins the production compiler/ingress/checker witness to the
single Lean4Lean `Tree`/`TreeList` block transaction.  The seven physical
family/constructor declarations are interpreted in the complete source
inventory and admitted in one atomic semantic transition.

The generated recursors remain a separately owned physical block.  Their
semantic constants and rules are already installed by this transaction; the
next recursor-link module supplies their rule and pattern provenance.
-/

namespace Ix.Tc.MutualTreeFixture

open Lean4Lean
open Lean4Lean.MutualInductiveFixtures
open Lean4Lean.MutualInductiveReplayFixtures
open MutualTreeCertificateFixture

local instance admissionAnonKIdDecidableEq : DecidableEq (KId .anon) :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by cases equality; exact beq_self_eq_true left)

local instance mutualFamilyMemberDecidable (concrete : KConst .anon) :
    Decidable concrete.IsMutualFamilyMember := by
  cases concrete <;>
    simp only [KConst.IsMutualFamilyMember] <;> infer_instance

/-! ## Complete physical catalog and source naming -/

def concreteAt (id : KId .anon) : KConst .anon :=
  (recursorIngressAfter.get? id).getD default

def treeConcrete : KConst .anon := concreteAt treeId
def treeListConcrete : KConst .anon := concreteAt treeListId
def treeLeafConcrete : KConst .anon := concreteAt treeLeafId
def treeNodeConcrete : KConst .anon := concreteAt treeNodeId
def treeBranchConcrete : KConst .anon := concreteAt treeBranchId
def treeListNilConcrete : KConst .anon := concreteAt treeListNilId
def treeListConsConcrete : KConst .anon := concreteAt treeListConsId
def treeRecConcrete : KConst .anon := concreteAt treeRecId
def treeListRecConcrete : KConst .anon := concreteAt treeListRecId

/-- The explicit semantic catalog contains exactly the nine declarations
produced by the two successful ingress calls. -/
def catalog : Catalog := fun id =>
  if id == treeId then some treeConcrete
  else if id == treeListId then some treeListConcrete
  else if id == treeLeafId then some treeLeafConcrete
  else if id == treeNodeId then some treeNodeConcrete
  else if id == treeBranchId then some treeBranchConcrete
  else if id == treeListNilId then some treeListNilConcrete
  else if id == treeListConsId then some treeListConsConcrete
  else if id == treeRecId then some treeRecConcrete
  else if id == treeListRecId then some treeListRecConcrete
  else none

def nameOf (address : Address) : Option Lean.Name :=
  if address == treeId.addr then some ``Tree
  else if address == treeListId.addr then some ``TreeList
  else if address == treeLeafId.addr then some ``Tree.leaf
  else if address == treeNodeId.addr then some ``Tree.node
  else if address == treeBranchId.addr then some ``Tree.branch
  else if address == treeListNilId.addr then some ``TreeList.nil
  else if address == treeListConsId.addr then some ``TreeList.cons
  else if address == treeRecId.addr then some ``Tree.rec
  else if address == treeListRecId.addr then some ``TreeList.rec
  else none

private def allPhysicalEntriesLoaded : Bool :=
  [recursorIngressAfter.get? treeId,
    recursorIngressAfter.get? treeListId,
    recursorIngressAfter.get? treeLeafId,
    recursorIngressAfter.get? treeNodeId,
    recursorIngressAfter.get? treeBranchId,
    recursorIngressAfter.get? treeListNilId,
    recursorIngressAfter.get? treeListConsId,
    recursorIngressAfter.get? treeRecId,
    recursorIngressAfter.get? treeListRecId].all Option.isSome

private theorem allPhysicalEntriesLoadedNative :
    allPhysicalEntriesLoaded = true := by
  native_decide

theorem allPhysicalEntriesLoaded_eq : allPhysicalEntriesLoaded = true :=
  allPhysicalEntriesLoadedNative

theorem catalog_tree : catalog treeId = some treeConcrete := by
  unfold catalog
  rw [if_pos (by native_decide)]

theorem catalog_treeList : catalog treeListId = some treeListConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_pos (by native_decide)]

theorem catalog_leaf : catalog treeLeafId = some treeLeafConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem catalog_node : catalog treeNodeId = some treeNodeConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]

theorem catalog_branch : catalog treeBranchId = some treeBranchConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem catalog_nil : catalog treeListNilId = some treeListNilConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]

theorem catalog_cons : catalog treeListConsId = some treeListConsConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem catalog_treeRec : catalog treeRecId = some treeRecConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]

theorem catalog_treeListRec :
    catalog treeListRecId = some treeListRecConcrete := by
  unfold catalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem nameOf_tree : nameOf treeId.addr = some ``Tree := by
  unfold nameOf
  rw [if_pos (by native_decide)]

theorem nameOf_treeList : nameOf treeListId.addr = some ``TreeList := by
  unfold nameOf
  rw [if_neg (by native_decide), if_pos (by native_decide)]

theorem nameOf_leaf : nameOf treeLeafId.addr = some ``Tree.leaf := by
  unfold nameOf
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem nameOf_node : nameOf treeNodeId.addr = some ``Tree.node := by
  unfold nameOf
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]

theorem nameOf_branch : nameOf treeBranchId.addr = some ``Tree.branch := by
  unfold nameOf
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem nameOf_nil : nameOf treeListNilId.addr = some ``TreeList.nil := by
  unfold nameOf
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]

theorem nameOf_cons : nameOf treeListConsId.addr = some ``TreeList.cons := by
  unfold nameOf
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem nameOf_treeRec : nameOf treeRecId.addr = some ``Tree.rec := by
  unfold nameOf
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]

theorem nameOf_treeListRec :
    nameOf treeListRecId.addr = some ``TreeList.rec := by
  unfold nameOf
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

def blockCatalog : BlockCatalog := fun id => recursorIngressAfter.getBlock? id

def world : VerifyWorld where
  catalog := catalog
  blocks := blockCatalog
  trusted := fun _ => False
  venv := .empty
  nameOf := nameOf
  venvWF := ⟨[], .empty⟩
  trustedCatalogued := fun {_} htrusted => False.elim htrusted

theorem trustedCatalog : TrustedCatalogRel RawProjRel.none world :=
  TrustedCatalogLog.empty

/-! ## Exact source constants and raw translations -/

def treeLeafSource : VConstVal := treeType.ctors[0]
def treeNodeSource : VConstVal := treeType.ctors[1]
def treeBranchSource : VConstVal := treeType.ctors[2]
def treeListNilSource : VConstVal := treeListType.ctors[0]
def treeListConsSource : VConstVal := treeListType.ctors[1]

structure FamilyMemberShapeFacts : Prop where
  treeKind : treeConcrete.IsMutualFamilyMember
  treeListKind : treeListConcrete.IsMutualFamilyMember
  leafKind : treeLeafConcrete.IsMutualFamilyMember
  nodeKind : treeNodeConcrete.IsMutualFamilyMember
  branchKind : treeBranchConcrete.IsMutualFamilyMember
  nilKind : treeListNilConcrete.IsMutualFamilyMember
  consKind : treeListConsConcrete.IsMutualFamilyMember
  treeUvars : treeConcrete.lvls.toNat = treeType.toVConstant.uvars
  treeListUvars : treeListConcrete.lvls.toNat = treeListType.toVConstant.uvars
  leafUvars : treeLeafConcrete.lvls.toNat = treeLeafSource.toVConstant.uvars
  nodeUvars : treeNodeConcrete.lvls.toNat = treeNodeSource.toVConstant.uvars
  branchUvars :
    treeBranchConcrete.lvls.toNat = treeBranchSource.toVConstant.uvars
  nilUvars :
    treeListNilConcrete.lvls.toNat = treeListNilSource.toVConstant.uvars
  consUvars :
    treeListConsConcrete.lvls.toNat = treeListConsSource.toVConstant.uvars
  leafSource : treeLeafSource ∈ treeDecl.blockConstructorConstants
  nodeSource : treeNodeSource ∈ treeDecl.blockConstructorConstants
  branchSource : treeBranchSource ∈ treeDecl.blockConstructorConstants
  nilSource : treeListNilSource ∈ treeDecl.blockConstructorConstants
  consSource : treeListConsSource ∈ treeDecl.blockConstructorConstants

private theorem familyMemberShapeFactsNative : FamilyMemberShapeFacts := by
  constructor <;> native_decide

theorem familyMemberShapeFacts : FamilyMemberShapeFacts :=
  familyMemberShapeFactsNative

private theorem treeTypeRawNative :
    RawExprRel (uvars := treeConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeConcrete.ty
      treeType.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem treeTypeRaw :
    RawExprRel (uvars := treeConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeConcrete.ty
      treeType.type :=
  treeTypeRawNative

private theorem treeListTypeRawNative :
    RawExprRel (uvars := treeListConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeListConcrete.ty
      treeListType.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem treeListTypeRaw :
    RawExprRel (uvars := treeListConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeListConcrete.ty
      treeListType.type :=
  treeListTypeRawNative

private theorem treeLeafTypeRawNative :
    RawExprRel (uvars := treeLeafConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeLeafConcrete.ty
      treeLeafSource.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem treeLeafTypeRaw :
    RawExprRel (uvars := treeLeafConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeLeafConcrete.ty
      treeLeafSource.type :=
  treeLeafTypeRawNative

private theorem treeNodeTypeRawNative :
    RawExprRel (uvars := treeNodeConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeNodeConcrete.ty
      treeNodeSource.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem treeNodeTypeRaw :
    RawExprRel (uvars := treeNodeConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeNodeConcrete.ty
      treeNodeSource.type :=
  treeNodeTypeRawNative

private theorem treeBranchTypeRawNative :
    RawExprRel (uvars := treeBranchConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeBranchConcrete.ty
      treeBranchSource.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem treeBranchTypeRaw :
    RawExprRel (uvars := treeBranchConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeBranchConcrete.ty
      treeBranchSource.type :=
  treeBranchTypeRawNative

private theorem treeListNilTypeRawNative :
    RawExprRel (uvars := treeListNilConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeListNilConcrete.ty
      treeListNilSource.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem treeListNilTypeRaw :
    RawExprRel (uvars := treeListNilConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeListNilConcrete.ty
      treeListNilSource.type :=
  treeListNilTypeRawNative

private theorem treeListConsTypeRawNative :
    RawExprRel (uvars := treeListConsConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeListConsConcrete.ty
      treeListConsSource.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem treeListConsTypeRaw :
    RawExprRel (uvars := treeListConsConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeListConsConcrete.ty
      treeListConsSource.type :=
  treeListConsTypeRawNative

/-! ## Exhaustive physical/source representation link -/

def familyLink : MutualFamilyCatalogLink RawProjRel.none world transaction where
  members := familyMembers
  nonempty := by rw [familyMembers_eq]; decide
  member := by
    intro id hmember
    rw [familyMembers_eq] at hmember
    simp at hmember
    rcases hmember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨treeListConcrete, ``TreeList, treeListType.toVConstant,
        catalog_treeList,
        familyMemberShapeFacts.treeListKind,
        nameOf_treeList,
        familyMemberShapeFacts.treeListUvars, treeListTypeRaw,
        .inl ⟨treeListType, by simp [treeDecl], rfl, rfl⟩⟩
    · exact ⟨treeListNilConcrete, ``TreeList.nil,
        treeListNilSource.toVConstant, catalog_nil,
        familyMemberShapeFacts.nilKind, nameOf_nil,
        familyMemberShapeFacts.nilUvars, treeListNilTypeRaw,
        .inr ⟨treeListNilSource, familyMemberShapeFacts.nilSource,
          rfl, rfl⟩⟩
    · exact ⟨treeListConsConcrete, ``TreeList.cons,
        treeListConsSource.toVConstant, catalog_cons,
        familyMemberShapeFacts.consKind, nameOf_cons,
        familyMemberShapeFacts.consUvars, treeListConsTypeRaw,
        .inr ⟨treeListConsSource, familyMemberShapeFacts.consSource,
          rfl, rfl⟩⟩
    · exact ⟨treeConcrete, ``Tree, treeType.toVConstant,
        catalog_tree, familyMemberShapeFacts.treeKind,
        nameOf_tree, familyMemberShapeFacts.treeUvars,
        treeTypeRaw, .inl ⟨treeType, by simp [treeDecl], rfl, rfl⟩⟩
    · exact ⟨treeLeafConcrete, ``Tree.leaf, treeLeafSource.toVConstant,
        catalog_leaf, familyMemberShapeFacts.leafKind,
        nameOf_leaf, familyMemberShapeFacts.leafUvars,
        treeLeafTypeRaw, .inr ⟨treeLeafSource,
          familyMemberShapeFacts.leafSource, rfl, rfl⟩⟩
    · exact ⟨treeNodeConcrete, ``Tree.node, treeNodeSource.toVConstant,
        catalog_node, familyMemberShapeFacts.nodeKind,
        nameOf_node, familyMemberShapeFacts.nodeUvars,
        treeNodeTypeRaw, .inr ⟨treeNodeSource,
          familyMemberShapeFacts.nodeSource, rfl, rfl⟩⟩
    · exact ⟨treeBranchConcrete, ``Tree.branch,
        treeBranchSource.toVConstant, catalog_branch,
        familyMemberShapeFacts.branchKind, nameOf_branch,
        familyMemberShapeFacts.branchUvars, treeBranchTypeRaw,
        .inr ⟨treeBranchSource, familyMemberShapeFacts.branchSource,
          rfl, rfl⟩⟩
  fresh := by
    intro id _ htrusted
    exact htrusted

/-! ## Exact physical ownership -/

private def IsDirectInductiveOwner
    (block : KId .anon) : KConst .anon → Prop
  | .indc (block := owner) .. => owner = block
  | _ => False

private def IsDirectConstructorOf
    (family : KId .anon) : KConst .anon → Prop
  | .ctor (induct := parent) .. => parent = family
  | _ => False

local instance directInductiveOwnerDecidable (block : KId .anon)
    (concrete : KConst .anon) :
    Decidable (IsDirectInductiveOwner block concrete) := by
  cases concrete <;>
    simp only [IsDirectInductiveOwner] <;> infer_instance

local instance directConstructorOfDecidable (family : KId .anon)
    (concrete : KConst .anon) :
    Decidable (IsDirectConstructorOf family concrete) := by
  cases concrete <;>
    simp only [IsDirectConstructorOf] <;> infer_instance

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

private theorem directConstructor_inductiveMemberOf
    {selectedCatalog : Catalog} {block family : KId .anon}
    {concrete familyConcrete : KConst .anon}
    (hconstructor : IsDirectConstructorOf family concrete)
    (hfamily : selectedCatalog family = some familyConcrete)
    (howner : IsDirectInductiveOwner block familyConcrete) :
    concrete.IsInductiveMemberOf selectedCatalog block := by
  cases concrete <;>
    simp_all [IsDirectConstructorOf, KConst.IsInductiveMemberOf,
      IsDirectInductiveOwner]
  exact howner

private theorem recursor_not_inductiveMemberOf
    {selectedCatalog : Catalog} {familyBlock recursorBlock : KId .anon}
    {concrete : KConst .anon}
    (howner : concrete.IsRecursorMemberOf recursorBlock) :
    ¬concrete.IsInductiveMemberOf selectedCatalog familyBlock := by
  intro hinductive
  cases concrete <;>
    simp_all [KConst.IsRecursorMemberOf, KConst.IsInductiveMemberOf]

structure OwnershipShapeFacts : Prop where
  tree : IsDirectInductiveOwner familyBlockId treeConcrete
  treeList : IsDirectInductiveOwner familyBlockId treeListConcrete
  leaf : IsDirectConstructorOf treeId treeLeafConcrete
  node : IsDirectConstructorOf treeId treeNodeConcrete
  branch : IsDirectConstructorOf treeId treeBranchConcrete
  nil : IsDirectConstructorOf treeListId treeListNilConcrete
  cons : IsDirectConstructorOf treeListId treeListConsConcrete
  treeRec : treeRecConcrete.IsRecursorMemberOf recursorBlockId
  treeListRec : treeListRecConcrete.IsRecursorMemberOf recursorBlockId

private theorem ownershipShapeFactsNative : OwnershipShapeFacts := by
  constructor <;> native_decide

theorem ownershipShapeFacts : OwnershipShapeFacts :=
  ownershipShapeFactsNative

theorem treeOwner :
    treeConcrete.IsInductiveMemberOf catalog familyBlockId :=
  directInductiveOwner_inductiveMemberOf ownershipShapeFacts.tree

theorem treeListOwner :
    treeListConcrete.IsInductiveMemberOf catalog familyBlockId :=
  directInductiveOwner_inductiveMemberOf ownershipShapeFacts.treeList

theorem leafOwner :
    treeLeafConcrete.IsInductiveMemberOf catalog familyBlockId :=
  directConstructor_inductiveMemberOf ownershipShapeFacts.leaf catalog_tree
    ownershipShapeFacts.tree

theorem nodeOwner :
    treeNodeConcrete.IsInductiveMemberOf catalog familyBlockId :=
  directConstructor_inductiveMemberOf ownershipShapeFacts.node catalog_tree
    ownershipShapeFacts.tree

theorem branchOwner :
    treeBranchConcrete.IsInductiveMemberOf catalog familyBlockId :=
  directConstructor_inductiveMemberOf ownershipShapeFacts.branch catalog_tree
    ownershipShapeFacts.tree

theorem nilOwner :
    treeListNilConcrete.IsInductiveMemberOf catalog familyBlockId :=
  directConstructor_inductiveMemberOf ownershipShapeFacts.nil catalog_treeList
    ownershipShapeFacts.treeList

theorem consOwner :
    treeListConsConcrete.IsInductiveMemberOf catalog familyBlockId :=
  directConstructor_inductiveMemberOf ownershipShapeFacts.cons catalog_treeList
    ownershipShapeFacts.treeList

theorem treeRecNotFamilyOwner :
    ¬treeRecConcrete.IsInductiveMemberOf catalog familyBlockId :=
  recursor_not_inductiveMemberOf ownershipShapeFacts.treeRec

theorem treeListRecNotFamilyOwner :
    ¬treeListRecConcrete.IsInductiveMemberOf catalog familyBlockId :=
  recursor_not_inductiveMemberOf ownershipShapeFacts.treeListRec

theorem treeRecOwner :
    treeRecConcrete.IsRecursorMemberOf recursorBlockId :=
  ownershipShapeFacts.treeRec

theorem treeListRecOwner :
    treeListRecConcrete.IsRecursorMemberOf recursorBlockId :=
  ownershipShapeFacts.treeListRec

/-- Every successful lookup in the explicit catalog is one of the complete
seven-member family block or the two-member generated-recursor block. -/
theorem catalog_entry_cases {id : KId .anon} {concrete : KConst .anon}
    (hcatalog : catalog id = some concrete) :
    (id = treeId ∧ concrete = treeConcrete) ∨
      (id = treeListId ∧ concrete = treeListConcrete) ∨
      (id = treeLeafId ∧ concrete = treeLeafConcrete) ∨
      (id = treeNodeId ∧ concrete = treeNodeConcrete) ∨
      (id = treeBranchId ∧ concrete = treeBranchConcrete) ∨
      (id = treeListNilId ∧ concrete = treeListNilConcrete) ∨
      (id = treeListConsId ∧ concrete = treeListConsConcrete) ∨
      (id = treeRecId ∧ concrete = treeRecConcrete) ∨
      (id = treeListRecId ∧ concrete = treeListRecConcrete) := by
  unfold catalog at hcatalog
  split at hcatalog
  · left
    exact ⟨eq_of_beq (by assumption), (Option.some.inj hcatalog).symm⟩
  · split at hcatalog
    · right; left
      exact ⟨eq_of_beq (by assumption), (Option.some.inj hcatalog).symm⟩
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
            · right; right; right; right; right; left
              exact ⟨eq_of_beq (by assumption),
                (Option.some.inj hcatalog).symm⟩
            · split at hcatalog
              · right; right; right; right; right; right; left
                exact ⟨eq_of_beq (by assumption),
                  (Option.some.inj hcatalog).symm⟩
              · split at hcatalog
                · right; right; right; right; right; right; right; left
                  exact ⟨eq_of_beq (by assumption),
                    (Option.some.inj hcatalog).symm⟩
                · split at hcatalog
                  · right; right; right; right; right; right; right; right
                    exact ⟨eq_of_beq (by assumption),
                      (Option.some.inj hcatalog).symm⟩
                  · contradiction

theorem familyCoordinated_iff (id : KId .anon) :
    id ∈ familyMembers ↔
      catalog.CoordinatedMember familyBlockId .inductive' id := by
  constructor
  · intro hmember
    rw [familyMembers_eq] at hmember
    simp at hmember
    rcases hmember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨treeListConcrete, catalog_treeList, treeListOwner⟩
    · exact ⟨treeListNilConcrete, catalog_nil, nilOwner⟩
    · exact ⟨treeListConsConcrete, catalog_cons, consOwner⟩
    · exact ⟨treeConcrete, catalog_tree, treeOwner⟩
    · exact ⟨treeLeafConcrete, catalog_leaf, leafOwner⟩
    · exact ⟨treeNodeConcrete, catalog_node, nodeOwner⟩
    · exact ⟨treeBranchConcrete, catalog_branch, branchOwner⟩
  · rintro ⟨concrete, hcatalog, howner⟩
    rcases catalog_entry_cases hcatalog with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩
    · simp [familyMembers_eq]
    · simp [familyMembers_eq]
    · simp [familyMembers_eq]
    · simp [familyMembers_eq]
    · simp [familyMembers_eq]
    · simp [familyMembers_eq]
    · simp [familyMembers_eq]
    · exact False.elim (treeRecNotFamilyOwner howner)
    · exact False.elim (treeListRecNotFamilyOwner howner)

theorem recursorCoordinated_iff (id : KId .anon) :
    id ∈ recursorMembers ↔
      catalog.CoordinatedMember recursorBlockId .recursor id := by
  constructor
  · intro hmember
    rw [recursorMembers_eq] at hmember
    simp at hmember
    rcases hmember with rfl | rfl
    · exact ⟨treeListRecConcrete, catalog_treeListRec, treeListRecOwner⟩
    · exact ⟨treeRecConcrete, catalog_treeRec, treeRecOwner⟩
  · rintro ⟨concrete, hcatalog, howner⟩
    rcases catalog_entry_cases hcatalog with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩
    · exact False.elim
        (familyMemberShapeFacts.treeKind.notRecursorMemberOf _ howner)
    · exact False.elim
        (familyMemberShapeFacts.treeListKind.notRecursorMemberOf _ howner)
    · exact False.elim
        (familyMemberShapeFacts.leafKind.notRecursorMemberOf _ howner)
    · exact False.elim
        (familyMemberShapeFacts.nodeKind.notRecursorMemberOf _ howner)
    · exact False.elim
        (familyMemberShapeFacts.branchKind.notRecursorMemberOf _ howner)
    · exact False.elim
        (familyMemberShapeFacts.nilKind.notRecursorMemberOf _ howner)
    · exact False.elim
        (familyMemberShapeFacts.consKind.notRecursorMemberOf _ howner)
    · simp [recursorMembers_eq]
    · simp [recursorMembers_eq]

theorem world_family_block :
    world.blocks familyBlockId = some familyMembers := by
  exact familyBlockLoaded

theorem world_recursor_block :
    world.blocks recursorBlockId = some recursorMembers := by
  exact recursorBlockLoaded

theorem exactFamilyBlock :
    ExactCheckBlock world familyBlockId familyMembers .inductive' where
  blockLookup := world_family_block
  nonempty := by rw [familyMembers_eq]; decide
  memberIff := familyCoordinated_iff

theorem exactRecursorBlock :
    ExactCheckBlock world recursorBlockId recursorMembers .recursor where
  blockLookup := world_recursor_block
  nonempty := by rw [recursorMembers_eq]; decide
  memberIff := recursorCoordinated_iff

/-! ## One atomic mutual-family transaction -/

theorem familyBlockCertificate :
    SemanticBlockTransitionCertificate RawProjRel.none world familyBlockId
      familyMembers .inductive' treeFinalEnv :=
  familyLink.transition exactFamilyBlock

def familyAcceptedWorld : VerifyWorld :=
  familyBlockCertificate.admittedWorld

theorem familyAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none world familyAcceptedWorld
      familyBlockId familyMembers .inductive' :=
  familyBlockCertificate.admit trustedCatalog

theorem familyBlockAccepted :
    familyAcceptedWorld.AcceptedBlock familyBlockId :=
  familyAtomicAdmission.accepted

/-- Current end-to-end checkpoint: both physical production checkers execute
successfully, and the complete seven-member family block is admitted by the
one retained mutual Theory transaction.  Generated-recursor semantic
admission is intentionally not claimed until its rule/pattern link lands. -/
structure MutualFamilyAtomicClosure : Prop where
  execution : EndToEndExecution
  exactFamily : ExactCheckBlock world familyBlockId familyMembers .inductive'
  exactRecursor : ExactCheckBlock world recursorBlockId recursorMembers .recursor
  ruleClosure : lean4leanCertificate.generation.RuleClosure
  familyAdmission :
    AtomicBlockAdmission RawProjRel.none world familyAcceptedWorld
      familyBlockId familyMembers .inductive'
  accepted : familyAcceptedWorld.AcceptedBlock familyBlockId

theorem mutualFamilyAtomicClosure : MutualFamilyAtomicClosure where
  execution := endToEndExecution
  exactFamily := exactFamilyBlock
  exactRecursor := exactRecursorBlock
  ruleClosure := lean4leanCertificate.ruleClosure
  familyAdmission := familyAtomicAdmission
  accepted := familyBlockAccepted

end Ix.Tc.MutualTreeFixture
