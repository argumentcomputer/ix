import Ix.Tc.Verify.Inductive.NestedSemanticTransaction

/-!
# Atomic admission of the nested `LeanTree` source block

This module joins the concrete Ix block to the completed Lean4Lean nested
transaction.  The physical block contains only the stored `Tree` family and
`node` constructor.  Lean4Lean's transaction independently flattens the
nested dependency, checks the restored constants/equations, removes every
auxiliary name, and commits the source family, constructor, two recursors,
and two rules at one public `addInductNested` boundary.
-/

namespace Ix.Tc.NestedRecursiveFixture

open Lean4Lean
open InductiveConcreteFixture

local instance nestedAdmissionAddressDecidableEq : DecidableEq Address :=
  AnonStructural.addressDecidableEq

local instance nestedAdmissionKIdDecidableEq : DecidableEq (KId .anon) :=
  AnonStructural.idDecidableEq

local instance nestedSourceMemberDecidable (concrete : KConst .anon) :
    Decidable concrete.IsNestedSourceMember := by
  cases concrete <;>
    simp only [KConst.IsNestedSourceMember] <;> infer_instance

/-! ## Production checker execution -/

def nestedFamilyMembers : Array (KId .anon) := #[treeId, nodeId]

private theorem nestedFamilyBlockLoadedNative :
    checkerInitial.env.getBlock? treeBlockId = some nestedFamilyMembers := by
  native_decide

theorem nestedFamilyBlockLoaded :
    checkerInitial.env.getBlock? treeBlockId = some nestedFamilyMembers :=
  nestedFamilyBlockLoadedNative

def nestedFamilyKernelOutcome :=
  (RecM.checkInductiveBlock treeBlockId nestedFamilyMembers).run
    checkerMethods checkerInitial

def nestedFamilyKernelAfter : TcState .anon :=
  match nestedFamilyKernelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem nestedFamilyKernelSucceededNative :
    (match nestedFamilyKernelOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem nestedFamilyKernelRun :
    (RecM.checkInductiveBlock treeBlockId nestedFamilyMembers).run
      checkerMethods checkerInitial = .ok () nestedFamilyKernelAfter := by
  have success := nestedFamilyKernelSucceededNative
  unfold nestedFamilyKernelAfter
  generalize houtcome : nestedFamilyKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all [nestedFamilyKernelOutcome]

/-! ## Complete physical catalog and source naming -/

def nestedCatalog : Catalog := fun id =>
  if id == treeId then some treeConcrete
  else if id == nodeId then some nodeConcrete
  else none

def nestedNameOf (address : Address) : Option Lean.Name :=
  if address == boxId.addr then some ``LeanBox
  else if address == wrapId.addr then some ``LeanBox.wrap
  else if address == treeId.addr then some ``LeanTree
  else if address == nodeId.addr then some ``LeanTree.node
  else none

theorem nestedCatalog_tree : nestedCatalog treeId = some treeConcrete := by
  unfold nestedCatalog
  rw [if_pos (by native_decide)]

theorem nestedCatalog_node : nestedCatalog nodeId = some nodeConcrete := by
  unfold nestedCatalog
  rw [if_neg (by native_decide), if_pos (by native_decide)]

theorem nestedNameOf_box : nestedNameOf boxId.addr = some ``LeanBox := by
  unfold nestedNameOf
  rw [if_pos (by native_decide)]

theorem nestedNameOf_wrap :
    nestedNameOf wrapId.addr = some ``LeanBox.wrap := by
  unfold nestedNameOf
  rw [if_neg (by native_decide), if_pos (by native_decide)]

theorem nestedNameOf_tree : nestedNameOf treeId.addr = some ``LeanTree := by
  unfold nestedNameOf
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem nestedNameOf_node :
    nestedNameOf nodeId.addr = some ``LeanTree.node := by
  unfold nestedNameOf
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]

def nestedBlockCatalog : BlockCatalog := fun id =>
  treeIngressAfter.getBlock? id

def nestedWorld : VerifyWorld where
  catalog := nestedCatalog
  blocks := nestedBlockCatalog
  trusted := fun _ => False
  venv := semanticBoxEnv
  nameOf := nestedNameOf
  venvWF := semanticBoxEnvWF
  trustedCatalogued := fun {_} htrusted => False.elim htrusted

theorem nestedTrustedCatalog : TrustedCatalogRel RawProjRel.none nestedWorld :=
  by
    change TrustedCatalogLog RawProjRel.none nestedCatalog nestedNameOf
      (fun _ => False) semanticBoxEnv
    simpa only [or_false] using
      (TrustedCatalogLog.semanticBlock
        (members := fun _ => False)
        (TrustedCatalogLog.empty (trProj := RawProjRel.none)
          (catalog := nestedCatalog) (nameOf := nestedNameOf))
        semanticBoxTransaction.facts.envLE semanticBoxEnvWF
        (fun {_} member => False.elim member))

/-! ## Exact source constants and raw translations -/

structure NestedMemberShapeFacts : Prop where
  treeKind : treeConcrete.IsNestedSourceMember
  nodeKind : nodeConcrete.IsNestedSourceMember
  treeUvars :
    treeConcrete.lvls.toNat = semanticTreeFamily.toVConstant.uvars
  nodeUvars :
    nodeConcrete.lvls.toNat = semanticTreeNode.toVConstant.uvars

private theorem nestedMemberShapeFactsNative : NestedMemberShapeFacts := by
  constructor <;> native_decide

theorem nestedMemberShapeFacts : NestedMemberShapeFacts :=
  nestedMemberShapeFactsNative

private theorem nestedTreeTypeRawNative :
    RawExprRel (uvars := treeConcrete.lvls.toNat) semanticTreeEnv nestedNameOf
      RawProjRel.none [] treeConcrete.ty semanticTreeFamily.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem nestedTreeTypeRaw :
    RawExprRel (uvars := treeConcrete.lvls.toNat) semanticTreeEnv nestedNameOf
      RawProjRel.none [] treeConcrete.ty semanticTreeFamily.type :=
  nestedTreeTypeRawNative

private theorem nestedNodeTypeRawNative :
    RawExprRel (uvars := nodeConcrete.lvls.toNat) semanticTreeEnv nestedNameOf
      RawProjRel.none [] nodeConcrete.ty semanticTreeNode.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem nestedNodeTypeRaw :
    RawExprRel (uvars := nodeConcrete.lvls.toNat) semanticTreeEnv nestedNameOf
      RawProjRel.none [] nodeConcrete.ty semanticTreeNode.type :=
  nestedNodeTypeRawNative

/-! ## Exhaustive source correspondence -/

def nestedFamilyLink : NestedFamilyCatalogLink RawProjRel.none nestedWorld
    semanticTreeCertificate where
  members := nestedFamilyMembers
  nonempty := by decide
  member := by
    intro id hmember
    simp [nestedFamilyMembers] at hmember
    rcases hmember with rfl | rfl
    · exact ⟨treeConcrete, ``LeanTree, semanticTreeFamily.toVConstant,
        nestedCatalog_tree, nestedMemberShapeFacts.treeKind,
        nestedNameOf_tree, nestedMemberShapeFacts.treeUvars,
        nestedTreeTypeRaw,
        .inl ⟨semanticTreeType, by simp [semanticTreeDecl], rfl, rfl⟩⟩
    · exact ⟨nodeConcrete, ``LeanTree.node,
        semanticTreeNode.toVConstant, nestedCatalog_node,
        nestedMemberShapeFacts.nodeKind, nestedNameOf_node,
        nestedMemberShapeFacts.nodeUvars, nestedNodeTypeRaw,
        .inr ⟨semanticTreeNode, by
          rw [semanticTreeSourceInventory.2]
          simp, semanticTreeNodeName.symm, rfl⟩⟩
  fresh := by
    intro id _ htrusted
    exact htrusted

/-! ## Exact physical ownership -/

private def IsDirectNestedInductiveOwner
    (block : KId .anon) : KConst .anon → Prop
  | .indc (block := owner) .. => owner = block
  | _ => False

private def IsDirectNestedConstructorOf
    (family : KId .anon) : KConst .anon → Prop
  | .ctor (induct := parent) .. => parent = family
  | _ => False

local instance directNestedInductiveOwnerDecidable (block : KId .anon)
    (concrete : KConst .anon) :
    Decidable (IsDirectNestedInductiveOwner block concrete) := by
  cases concrete <;>
    simp only [IsDirectNestedInductiveOwner] <;> infer_instance

local instance directNestedConstructorOfDecidable (family : KId .anon)
    (concrete : KConst .anon) :
    Decidable (IsDirectNestedConstructorOf family concrete) := by
  cases concrete <;>
    simp only [IsDirectNestedConstructorOf] <;> infer_instance

private theorem directNestedInductiveOwner_member
    {selectedCatalog : Catalog} {block : KId .anon}
    {concrete : KConst .anon}
    (owner : IsDirectNestedInductiveOwner block concrete) :
    concrete.IsInductiveMemberOf selectedCatalog block := by
  cases concrete <;>
    simp_all [IsDirectNestedInductiveOwner, KConst.IsInductiveMemberOf]

private theorem directNestedConstructor_member
    {selectedCatalog : Catalog} {block family : KId .anon}
    {concrete familyConcrete : KConst .anon}
    (constructor : IsDirectNestedConstructorOf family concrete)
    (familyLookup : selectedCatalog family = some familyConcrete)
    (owner : IsDirectNestedInductiveOwner block familyConcrete) :
    concrete.IsInductiveMemberOf selectedCatalog block := by
  cases concrete <;>
    simp_all [IsDirectNestedConstructorOf, KConst.IsInductiveMemberOf,
      IsDirectNestedInductiveOwner]
  exact owner

private theorem nestedTreeDirectOwner :
    IsDirectNestedInductiveOwner treeBlockId treeConcrete := by
  native_decide

private theorem nestedNodeDirectConstructor :
    IsDirectNestedConstructorOf treeId nodeConcrete := by
  native_decide

theorem nestedTreeOwner :
    treeConcrete.IsInductiveMemberOf nestedCatalog treeBlockId :=
  directNestedInductiveOwner_member nestedTreeDirectOwner

theorem nestedNodeOwner :
    nodeConcrete.IsInductiveMemberOf nestedCatalog treeBlockId :=
  directNestedConstructor_member nestedNodeDirectConstructor
    nestedCatalog_tree nestedTreeDirectOwner

theorem nestedCatalog_entry_cases {id : KId .anon}
    {concrete : KConst .anon} (hcatalog : nestedCatalog id = some concrete) :
    (id = treeId ∧ concrete = treeConcrete) ∨
      (id = nodeId ∧ concrete = nodeConcrete) := by
  unfold nestedCatalog at hcatalog
  split at hcatalog
  · left
    exact ⟨eq_of_beq (by assumption), (Option.some.inj hcatalog).symm⟩
  · split at hcatalog
    · right
      exact ⟨eq_of_beq (by assumption), (Option.some.inj hcatalog).symm⟩
    · contradiction

theorem nestedFamilyCoordinated_iff (id : KId .anon) :
    id ∈ nestedFamilyMembers ↔
      nestedCatalog.CoordinatedMember treeBlockId .inductive' id := by
  constructor
  · intro hmember
    simp [nestedFamilyMembers] at hmember
    rcases hmember with rfl | rfl
    · exact ⟨treeConcrete, nestedCatalog_tree, nestedTreeOwner⟩
    · exact ⟨nodeConcrete, nestedCatalog_node, nestedNodeOwner⟩
  · rintro ⟨concrete, hcatalog, howner⟩
    rcases nestedCatalog_entry_cases hcatalog with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [nestedFamilyMembers]

theorem nestedWorld_familyBlock :
    nestedWorld.blocks treeBlockId = some nestedFamilyMembers :=
  nestedFamilyBlockLoaded

theorem exactNestedFamilyBlock :
    ExactCheckBlock nestedWorld treeBlockId nestedFamilyMembers
      .inductive' where
  blockLookup := nestedWorld_familyBlock
  nonempty := by decide
  memberIff := nestedFamilyCoordinated_iff

/-! ## One atomic nested-family transaction -/

theorem nestedFamilyBlockCertificate :
    SemanticBlockTransitionCertificate RawProjRel.none nestedWorld
      treeBlockId nestedFamilyMembers .inductive' semanticTreeEnv :=
  nestedFamilyLink.transition exactNestedFamilyBlock

def nestedFamilyAcceptedWorld : VerifyWorld :=
  nestedFamilyBlockCertificate.admittedWorld

theorem nestedFamilyAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none nestedWorld
      nestedFamilyAcceptedWorld treeBlockId nestedFamilyMembers
        .inductive' :=
  nestedFamilyBlockCertificate.admit nestedTrustedCatalog

theorem nestedFamilyBlockAccepted :
    nestedFamilyAcceptedWorld.AcceptedBlock treeBlockId :=
  nestedFamilyAtomicAdmission.accepted

/-- End-to-end checkpoint for the nested semantic-transaction slice. -/
structure NestedSemanticTransactionClosure : Prop where
  boxIngress : boxIngressOutcome = .ok boxIngressResult boxIngressAfter
  treeIngress : treeIngressOutcome = .ok treeIngressResult treeIngressAfter
  productionKernel :
    (RecM.checkInductiveBlock treeBlockId nestedFamilyMembers).run
      checkerMethods checkerInitial = .ok () nestedFamilyKernelAfter
  auxiliaryReachability :
    positivityRequest.ProducedBy (positivityFuel - 1) boxId #[] #[treeExpr]
      groups rootGroup.addrs #[treeId.addr] checkerMethods nestedWhnfAfter
        positivityAfter
  flatNodeValidation :
    Lean4Lean.AddInductive.checkConstructorType leanFlatStats false 0
      leanFlatNode.name leanFlatNode.type leanFlatConstructorContext = .ok ()
  flatWrapValidation :
    Lean4Lean.AddInductive.checkConstructorType leanFlatStats false 1
      leanFlatWrap.name leanFlatWrap.type leanFlatConstructorContext = .ok ()
  semantic : SemanticTreeTransactionFacts
  ruleMetadata :
    semanticTreeNodeRule.rhs = kernelRecRuleRhs% LeanTree.rec 0 ∧
      semanticTreeWrapRule.rhs = kernelRecRuleRhs% LeanTree.rec_1 0
  exactSource :
    ExactCheckBlock nestedWorld treeBlockId nestedFamilyMembers .inductive'
  admission :
    AtomicBlockAdmission RawProjRel.none nestedWorld
      nestedFamilyAcceptedWorld treeBlockId nestedFamilyMembers .inductive'
  accepted : nestedFamilyAcceptedWorld.AcceptedBlock treeBlockId

theorem nestedSemanticTransactionClosure :
    NestedSemanticTransactionClosure where
  boxIngress := boxIngressRun
  treeIngress := treeIngressRun
  productionKernel := nestedFamilyKernelRun
  auxiliaryReachability := nestedAuxiliaryReachability.1
  flatNodeValidation := leanFlatNodeConstructorValidationRun
  flatWrapValidation := leanFlatWrapConstructorValidationRun
  semantic := semanticTreeTransactionFacts
  ruleMetadata := semanticTreeRuleMetadata
  exactSource := exactNestedFamilyBlock
  admission := nestedFamilyAtomicAdmission
  accepted := nestedFamilyBlockAccepted

end Ix.Tc.NestedRecursiveFixture
