import Ix.Tc.Verify.Inductive.MutualFamilyAdmission
import Ix.Tc.Verify.Inductive.MutualRecursor
import Ix.Tc.Verify.Upstream.Pending

/-!
# Conditional atomic admission of the mutual `Tree`/`TreeList` recursors

The original Lean4Lean transaction has already installed both generated
recursors and all five globally flattened equations.  This module proves the
complete Ix-side correspondence for the separately owned two-member physical
recursor block: exact family-local dispatch, global equation positions,
structural translations, constructor metadata, ownership, and admission.

The reversed-order semantic certificate and generated-pattern soundness are
conditional on two fixture-specific Theory witnesses in
`Verify.Upstream.Pending`: family-permutation preservation of generation WF,
and the certified rule-pattern conclusion.  None of the Ix representation,
ingress, ownership, or production-execution facts are assumed there.
-/

namespace Ix.Tc.MutualTreeFixture

open Lean4Lean
open Lean4Lean.MutualInductiveFixtures
open Lean4Lean.MutualInductiveReplayFixtures
open MutualTreeCertificateFixture

/- The physical compiler canonically orders this SCC as `TreeList, Tree`.
These private aliases keep every rule index below tied to the exact reversed
Lean4Lean descriptor certified in the quarantined upstream module. -/
private abbrev treeGeneration :=
  Upstream.Pending.mutualTreePhysicalGeneration
private abbrev lean4leanCertificate :=
  Upstream.Pending.mutualTreePhysicalCertificate
private abbrev treeFinalEnv :=
  Upstream.Pending.mutualTreePhysicalFinalEnv

local instance anonKIdDecidableEq : DecidableEq (KId .anon) :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by
        cases equality
        exact beq_self_eq_true left)

local instance inductiveMemberDecidable (concrete : KConst .anon) :
    Decidable concrete.IsInductiveMember := by
  cases concrete <;> simp only [KConst.IsInductiveMember] <;> infer_instance

local instance recursorMajorIdxCoherentDecidable (concrete : KConst .anon) :
    Decidable concrete.RecursorMajorIdxCoherent := by
  cases concrete <;>
    simp only [KConst.RecursorMajorIdxCoherent] <;> infer_instance

local instance constructorAtDecidable (concrete : KConst .anon)
    (index : Nat) (params fields : UInt64) :
    Decidable (concrete.ConstructorAt index params fields) := by
  cases concrete <;> simp only [KConst.ConstructorAt] <;> infer_instance

/-! ## Exact source and physical positions -/

private theorem flatCtorZero : 0 < treeGeneration.flatCtors.length := by
  native_decide
private theorem flatCtorOne : 1 < treeGeneration.flatCtors.length := by
  native_decide
private theorem flatCtorTwo : 2 < treeGeneration.flatCtors.length := by
  native_decide
private theorem flatCtorThree : 3 < treeGeneration.flatCtors.length := by
  native_decide
private theorem flatCtorFour : 4 < treeGeneration.flatCtors.length := by
  native_decide

def leafNormalized : VInductDecl.NormalizedBlockCtor :=
  treeGeneration.flatCtors[2]'flatCtorTwo

def nodeNormalized : VInductDecl.NormalizedBlockCtor :=
  treeGeneration.flatCtors[3]'flatCtorThree

def branchNormalized : VInductDecl.NormalizedBlockCtor :=
  treeGeneration.flatCtors[4]'flatCtorFour

def nilNormalized : VInductDecl.NormalizedBlockCtor :=
  treeGeneration.flatCtors[0]'flatCtorZero

def consNormalized : VInductDecl.NormalizedBlockCtor :=
  treeGeneration.flatCtors[1]'flatCtorOne

theorem leafEntry : treeGeneration.flatCtors[2]? = some leafNormalized := rfl
theorem nodeEntry : treeGeneration.flatCtors[3]? = some nodeNormalized := rfl
theorem branchEntry :
    treeGeneration.flatCtors[4]? = some branchNormalized := rfl
theorem nilEntry : treeGeneration.flatCtors[0]? = some nilNormalized := rfl
theorem consEntry : treeGeneration.flatCtors[1]? = some consNormalized := rfl

private theorem recursorZero : 0 < treeGeneration.recursors.length := by
  native_decide
private theorem recursorOne : 1 < treeGeneration.recursors.length := by
  native_decide

def treeRecSource : VConstVal :=
  treeGeneration.recursors[1]'recursorOne
def treeListRecSource : VConstVal :=
  treeGeneration.recursors[0]'recursorZero

theorem treeRecSourceAt :
    treeGeneration.recursors[1]? = some treeRecSource := rfl
theorem treeListRecSourceAt :
    treeGeneration.recursors[0]? = some treeListRecSource := rfl

def recursorRules : KConst .anon → Array (RecRule .anon)
  | .recr (rules := rules) .. => rules
  | _ => #[]

def treeRecRules : Array (RecRule .anon) := recursorRules treeRecConcrete
def treeListRecRules : Array (RecRule .anon) :=
  recursorRules treeListRecConcrete

private theorem treeRuleZero : 0 < treeRecRules.size := by native_decide
private theorem treeRuleOne : 1 < treeRecRules.size := by native_decide
private theorem treeRuleTwo : 2 < treeRecRules.size := by native_decide
private theorem treeListRuleZero : 0 < treeListRecRules.size := by
  native_decide
private theorem treeListRuleOne : 1 < treeListRecRules.size := by
  native_decide

def leafRule : RecRule .anon := treeRecRules[0]'treeRuleZero
def nodeRule : RecRule .anon := treeRecRules[1]'treeRuleOne
def branchRule : RecRule .anon := treeRecRules[2]'treeRuleTwo
def nilRule : RecRule .anon := treeListRecRules[0]'treeListRuleZero
def consRule : RecRule .anon := treeListRecRules[1]'treeListRuleOne

theorem treeRecRuleAt_iff {index : Nat} {rule : RecRule .anon} :
    treeRecConcrete.RecursorRuleAt index rule ↔
      treeRecRules[index]? = some rule := by
  unfold KConst.RecursorRuleAt treeRecRules recursorRules
  cases treeRecConcrete <;> simp

theorem treeListRecRuleAt_iff {index : Nat} {rule : RecRule .anon} :
    treeListRecConcrete.RecursorRuleAt index rule ↔
      treeListRecRules[index]? = some rule := by
  unfold KConst.RecursorRuleAt treeListRecRules recursorRules
  cases treeListRecConcrete <;> simp

theorem leafRuleAt : treeRecConcrete.RecursorRuleAt 0 leafRule := by
  rw [treeRecRuleAt_iff]
  rw [Array.getElem?_eq_getElem treeRuleZero]
  congr

theorem nodeRuleAt : treeRecConcrete.RecursorRuleAt 1 nodeRule := by
  rw [treeRecRuleAt_iff]
  rw [Array.getElem?_eq_getElem treeRuleOne]
  congr

theorem branchRuleAt : treeRecConcrete.RecursorRuleAt 2 branchRule := by
  rw [treeRecRuleAt_iff]
  rw [Array.getElem?_eq_getElem treeRuleTwo]
  congr

theorem nilRuleAt : treeListRecConcrete.RecursorRuleAt 0 nilRule := by
  rw [treeListRecRuleAt_iff]
  rw [Array.getElem?_eq_getElem treeListRuleZero]
  congr

theorem consRuleAt : treeListRecConcrete.RecursorRuleAt 1 consRule := by
  rw [treeListRecRuleAt_iff]
  rw [Array.getElem?_eq_getElem treeListRuleOne]
  congr

/-- All closed representation facts are evaluated together, yielding one
auditable native-decision origin for the complete two-recursor link. -/
structure RecursorRepresentationFacts : Prop where
  treeRecKind : treeRecConcrete.IsInductiveMember
  treeListRecKind : treeListRecConcrete.IsInductiveMember
  treeRecName : treeRecSource.name = ``Tree.rec
  treeListRecName : treeListRecSource.name = ``TreeList.rec
  treeRecUvars :
    treeRecConcrete.lvls.toNat = treeRecSource.toVConstant.uvars
  treeListRecUvars :
    treeListRecConcrete.lvls.toNat = treeListRecSource.toVConstant.uvars
  treeRuleCount : treeRecRules.size = 3
  treeListRuleCount : treeListRecRules.size = 2
  treeMajor :
    treeRecConcrete.RecursorMajorIdx =
      some (treeGeneration.ruleMajorArity leafNormalized)
  treeNodeMajor :
    treeRecConcrete.RecursorMajorIdx =
      some (treeGeneration.ruleMajorArity nodeNormalized)
  treeBranchMajor :
    treeRecConcrete.RecursorMajorIdx =
      some (treeGeneration.ruleMajorArity branchNormalized)
  treeListMajor :
    treeListRecConcrete.RecursorMajorIdx =
      some (treeGeneration.ruleMajorArity nilNormalized)
  treeListConsMajor :
    treeListRecConcrete.RecursorMajorIdx =
      some (treeGeneration.ruleMajorArity consNormalized)
  treeMajorCoherent : treeRecConcrete.RecursorMajorIdxCoherent
  treeListMajorCoherent : treeListRecConcrete.RecursorMajorIdxCoherent
  leafConstructorAt : treeLeafConcrete.ConstructorAt 0 1 1
  nodeConstructorAt : treeNodeConcrete.ConstructorAt 1 1 1
  branchConstructorAt : treeBranchConcrete.ConstructorAt 2 1 1
  nilConstructorAt : treeListNilConcrete.ConstructorAt 0 1 0
  consConstructorAt : treeListConsConcrete.ConstructorAt 1 1 2
  leafArgumentArity :
    (1 : UInt64).toNat + (1 : UInt64).toNat =
      treeGeneration.ruleArgArity leafNormalized
  nodeArgumentArity :
    (1 : UInt64).toNat + (1 : UInt64).toNat =
      treeGeneration.ruleArgArity nodeNormalized
  branchArgumentArity :
    (1 : UInt64).toNat + (1 : UInt64).toNat =
      treeGeneration.ruleArgArity branchNormalized
  nilArgumentArity :
    (1 : UInt64).toNat + (0 : UInt64).toNat =
      treeGeneration.ruleArgArity nilNormalized
  consArgumentArity :
    (1 : UInt64).toNat + (2 : UInt64).toNat =
      treeGeneration.ruleArgArity consNormalized
  leafRecursorName :
    treeGeneration.ruleRecName leafNormalized = ``Tree.rec
  nodeRecursorName :
    treeGeneration.ruleRecName nodeNormalized = ``Tree.rec
  branchRecursorName :
    treeGeneration.ruleRecName branchNormalized = ``Tree.rec
  nilRecursorName :
    treeGeneration.ruleRecName nilNormalized = ``TreeList.rec
  consRecursorName :
    treeGeneration.ruleRecName consNormalized = ``TreeList.rec
  leafConstructorName : leafNormalized.ctor.raw.name = ``Tree.leaf
  nodeConstructorName : nodeNormalized.ctor.raw.name = ``Tree.node
  branchConstructorName : branchNormalized.ctor.raw.name = ``Tree.branch
  nilConstructorName : nilNormalized.ctor.raw.name = ``TreeList.nil
  consConstructorName : consNormalized.ctor.raw.name = ``TreeList.cons
  leafFields : leafRule.fields = 1
  nodeFields : nodeRule.fields = 1
  branchFields : branchRule.fields = 1
  nilFields : nilRule.fields = 0
  consFields : consRule.fields = 2
  leafBinderCore : leafRule.rhs.binderCore = true
  nodeBinderCore : nodeRule.rhs.binderCore = true
  branchBinderCore : branchRule.rhs.binderCore = true
  nilBinderCore : nilRule.rhs.binderCore = true
  consBinderCore : consRule.rhs.binderCore = true
  leafScoped : leafRule.rhs.Scoped 0
    (treeGeneration.rule 2 leafNormalized).uvars
  nodeScoped : nodeRule.rhs.Scoped 0
    (treeGeneration.rule 3 nodeNormalized).uvars
  branchScoped : branchRule.rhs.Scoped 0
    (treeGeneration.rule 4 branchNormalized).uvars
  nilScoped : nilRule.rhs.Scoped 0
    (treeGeneration.rule 0 nilNormalized).uvars
  consScoped : consRule.rhs.Scoped 0
    (treeGeneration.rule 1 consNormalized).uvars
  leafSize : leafRule.rhs.size < UInt64.size
  nodeSize : nodeRule.rhs.size < UInt64.size
  branchSize : branchRule.rhs.size < UInt64.size
  nilSize : nilRule.rhs.size < UInt64.size
  consSize : consRule.rhs.size < UInt64.size

private theorem recursorRepresentationFactsNative :
    RecursorRepresentationFacts := by
  constructor <;> native_decide

theorem recursorRepresentationFacts : RecursorRepresentationFacts :=
  recursorRepresentationFactsNative

private theorem certificateGeneration_eq :
    lean4leanCertificate.generation = treeGeneration := rfl

private theorem treeRecTypeRawNative :
    RawExprRel (uvars := treeRecConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeRecConcrete.ty
      treeRecSource.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem treeRecTypeRaw :
    RawExprRel (uvars := treeRecConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeRecConcrete.ty
      treeRecSource.type := treeRecTypeRawNative

private theorem treeListRecTypeRawNative :
    RawExprRel (uvars := treeListRecConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeListRecConcrete.ty
      treeListRecSource.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem treeListRecTypeRaw :
    RawExprRel (uvars := treeListRecConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeListRecConcrete.ty
      treeListRecSource.type := treeListRecTypeRawNative

private theorem leafRuleRawNative :
    RawExprRel (uvars := (treeGeneration.rule 2 leafNormalized).uvars)
      treeFinalEnv nameOf RawProjRel.none [] leafRule.rhs
      (treeGeneration.rule 2 leafNormalized).rhs := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem leafRuleRaw :
    RawExprRel (uvars := (treeGeneration.rule 2 leafNormalized).uvars)
      treeFinalEnv nameOf RawProjRel.none [] leafRule.rhs
      (treeGeneration.rule 2 leafNormalized).rhs := leafRuleRawNative

private theorem nodeRuleRawNative :
    RawExprRel (uvars := (treeGeneration.rule 3 nodeNormalized).uvars)
      treeFinalEnv nameOf RawProjRel.none [] nodeRule.rhs
      (treeGeneration.rule 3 nodeNormalized).rhs := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem nodeRuleRaw :
    RawExprRel (uvars := (treeGeneration.rule 3 nodeNormalized).uvars)
      treeFinalEnv nameOf RawProjRel.none [] nodeRule.rhs
      (treeGeneration.rule 3 nodeNormalized).rhs := nodeRuleRawNative

private theorem branchRuleRawNative :
    RawExprRel (uvars := (treeGeneration.rule 4 branchNormalized).uvars)
      treeFinalEnv nameOf RawProjRel.none [] branchRule.rhs
      (treeGeneration.rule 4 branchNormalized).rhs := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem branchRuleRaw :
    RawExprRel (uvars := (treeGeneration.rule 4 branchNormalized).uvars)
      treeFinalEnv nameOf RawProjRel.none [] branchRule.rhs
      (treeGeneration.rule 4 branchNormalized).rhs := branchRuleRawNative

private theorem nilRuleRawNative :
    RawExprRel (uvars := (treeGeneration.rule 0 nilNormalized).uvars)
      treeFinalEnv nameOf RawProjRel.none [] nilRule.rhs
      (treeGeneration.rule 0 nilNormalized).rhs := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem nilRuleRaw :
    RawExprRel (uvars := (treeGeneration.rule 0 nilNormalized).uvars)
      treeFinalEnv nameOf RawProjRel.none [] nilRule.rhs
      (treeGeneration.rule 0 nilNormalized).rhs := nilRuleRawNative

private theorem consRuleRawNative :
    RawExprRel (uvars := (treeGeneration.rule 1 consNormalized).uvars)
      treeFinalEnv nameOf RawProjRel.none [] consRule.rhs
      (treeGeneration.rule 1 consNormalized).rhs := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem consRuleRaw :
    RawExprRel (uvars := (treeGeneration.rule 1 consNormalized).uvars)
      treeFinalEnv nameOf RawProjRel.none [] consRule.rhs
      (treeGeneration.rule 1 consNormalized).rhs := consRuleRawNative

/-! ## Typed structural translations and registered equations -/

private theorem upgradeRule
    {index : Nat} {constructor : VInductDecl.NormalizedBlockCtor}
    (entry : treeGeneration.ruleEntry index constructor)
    {rule : RecRule .anon}
    (raw : RawExprRel
      (uvars := (treeGeneration.rule index constructor).uvars)
      treeFinalEnv nameOf RawProjRel.none [] rule.rhs
      (treeGeneration.rule index constructor).rhs)
    (binderCore : rule.rhs.binderCore = true)
    (hscoped : rule.rhs.Scoped 0
      (treeGeneration.rule index constructor).uvars)
    (hsize : rule.rhs.size < UInt64.size) :
    TrKExprS treeFinalEnv (treeGeneration.rule index constructor).uvars
      nameOf RawProjRel.none [] rule.rhs
      (treeGeneration.rule index constructor).rhs := by
  let pre := raw.toPreBinderCore_of_scoped binderCore hscoped hsize
  have ruleWF := (lean4leanCertificate.recursorRuleFacts entry).wf
  exact pre.upgradeBinderCoreOfWF lean4leanCertificate.afterWF
    (Delta := []) (hDelta := trivial) binderCore ⟨_, ruleWF.2⟩

theorem leafRuleTyped :
    TrKExprS treeFinalEnv (treeGeneration.rule 2 leafNormalized).uvars
      nameOf RawProjRel.none [] leafRule.rhs
      (treeGeneration.rule 2 leafNormalized).rhs :=
  upgradeRule leafEntry
    leafRuleRaw
    recursorRepresentationFacts.leafBinderCore
    recursorRepresentationFacts.leafScoped
    recursorRepresentationFacts.leafSize

theorem nodeRuleTyped :
    TrKExprS treeFinalEnv (treeGeneration.rule 3 nodeNormalized).uvars
      nameOf RawProjRel.none [] nodeRule.rhs
      (treeGeneration.rule 3 nodeNormalized).rhs :=
  upgradeRule nodeEntry
    nodeRuleRaw
    recursorRepresentationFacts.nodeBinderCore
    recursorRepresentationFacts.nodeScoped
    recursorRepresentationFacts.nodeSize

theorem branchRuleTyped :
    TrKExprS treeFinalEnv (treeGeneration.rule 4 branchNormalized).uvars
      nameOf RawProjRel.none [] branchRule.rhs
      (treeGeneration.rule 4 branchNormalized).rhs :=
  upgradeRule branchEntry
    branchRuleRaw
    recursorRepresentationFacts.branchBinderCore
    recursorRepresentationFacts.branchScoped
    recursorRepresentationFacts.branchSize

theorem nilRuleTyped :
    TrKExprS treeFinalEnv (treeGeneration.rule 0 nilNormalized).uvars
      nameOf RawProjRel.none [] nilRule.rhs
      (treeGeneration.rule 0 nilNormalized).rhs :=
  upgradeRule nilEntry
    nilRuleRaw
    recursorRepresentationFacts.nilBinderCore
    recursorRepresentationFacts.nilScoped
    recursorRepresentationFacts.nilSize

theorem consRuleTyped :
    TrKExprS treeFinalEnv (treeGeneration.rule 1 consNormalized).uvars
      nameOf RawProjRel.none [] consRule.rhs
      (treeGeneration.rule 1 consNormalized).rhs :=
  upgradeRule consEntry
    consRuleRaw
    recursorRepresentationFacts.consBinderCore
    recursorRepresentationFacts.consScoped
    recursorRepresentationFacts.consSize

theorem treeRecRaw :
    RawInductiveConstRel treeFinalEnv nameOf RawProjRel.none treeRecId
      treeRecConcrete ``Tree.rec treeRecSource.toVConstant where
  kind := recursorRepresentationFacts.treeRecKind
  nameEq := nameOf_treeRec
  uvars := recursorRepresentationFacts.treeRecUvars
  type := treeRecTypeRaw

theorem treeListRecRaw :
    RawInductiveConstRel treeFinalEnv nameOf RawProjRel.none treeListRecId
      treeListRecConcrete ``TreeList.rec treeListRecSource.toVConstant where
  kind := recursorRepresentationFacts.treeListRecKind
  nameEq := nameOf_treeListRec
  uvars := recursorRepresentationFacts.treeListRecUvars
  type := treeListRecTypeRaw

theorem treeRecLookup :
    treeFinalEnv.constants ``Tree.rec =
      some treeRecSource.toVConstant := by
  have lookup := lean4leanCertificate.recursorLookup
    (List.mem_of_getElem? treeRecSourceAt)
  simpa [recursorRepresentationFacts.treeRecName] using lookup

theorem treeListRecLookup :
    treeFinalEnv.constants ``TreeList.rec =
      some treeListRecSource.toVConstant := by
  have lookup := lean4leanCertificate.recursorLookup
    (List.mem_of_getElem? treeListRecSourceAt)
  simpa [recursorRepresentationFacts.treeListRecName] using lookup

theorem leafRegistered :
    RegisteredRecursorRuleRhsRel treeFinalEnv nameOf RawProjRel.none treeRecId
      treeRecConcrete leafRule (treeGeneration.rule 2 leafNormalized) :=
  CertifiedMutualRecursor.registeredRule lean4leanCertificate treeRecRaw
    treeRecLookup recursorRepresentationFacts.leafRecursorName.symm
    leafEntry leafRuleRaw leafRuleTyped

theorem nodeRegistered :
    RegisteredRecursorRuleRhsRel treeFinalEnv nameOf RawProjRel.none treeRecId
      treeRecConcrete nodeRule (treeGeneration.rule 3 nodeNormalized) :=
  CertifiedMutualRecursor.registeredRule lean4leanCertificate treeRecRaw
    treeRecLookup recursorRepresentationFacts.nodeRecursorName.symm
    nodeEntry nodeRuleRaw nodeRuleTyped

theorem branchRegistered :
    RegisteredRecursorRuleRhsRel treeFinalEnv nameOf RawProjRel.none treeRecId
      treeRecConcrete branchRule (treeGeneration.rule 4 branchNormalized) :=
  CertifiedMutualRecursor.registeredRule lean4leanCertificate treeRecRaw
    treeRecLookup recursorRepresentationFacts.branchRecursorName.symm
    branchEntry branchRuleRaw branchRuleTyped

theorem nilRegistered :
    RegisteredRecursorRuleRhsRel treeFinalEnv nameOf RawProjRel.none
      treeListRecId treeListRecConcrete nilRule
      (treeGeneration.rule 0 nilNormalized) :=
  CertifiedMutualRecursor.registeredRule lean4leanCertificate treeListRecRaw
    treeListRecLookup recursorRepresentationFacts.nilRecursorName.symm
    nilEntry nilRuleRaw nilRuleTyped

theorem consRegistered :
    RegisteredRecursorRuleRhsRel treeFinalEnv nameOf RawProjRel.none
      treeListRecId treeListRecConcrete consRule
      (treeGeneration.rule 1 consNormalized) :=
  CertifiedMutualRecursor.registeredRule lean4leanCertificate treeListRecRaw
    treeListRecLookup recursorRepresentationFacts.consRecursorName.symm
    consEntry consRuleRaw consRuleTyped

/-! ## Exact generated patterns -/

def leafPattern : RecursorRulePattern :=
  CertifiedMutualRecursor.generatedPattern lean4leanCertificate
    leafEntry treeLeafId 0 1 1
    recursorRepresentationFacts.leafArgumentArity

def nodePattern : RecursorRulePattern :=
  CertifiedMutualRecursor.generatedPattern lean4leanCertificate
    nodeEntry treeNodeId 1 1 1
    recursorRepresentationFacts.nodeArgumentArity

def branchPattern : RecursorRulePattern :=
  CertifiedMutualRecursor.generatedPattern lean4leanCertificate
    branchEntry treeBranchId 2 1 1
    recursorRepresentationFacts.branchArgumentArity

def nilPattern : RecursorRulePattern :=
  CertifiedMutualRecursor.generatedPattern lean4leanCertificate
    nilEntry treeListNilId 0 1 0
    recursorRepresentationFacts.nilArgumentArity

def consPattern : RecursorRulePattern :=
  CertifiedMutualRecursor.generatedPattern lean4leanCertificate
    consEntry treeListConsId 1 1 2
    recursorRepresentationFacts.consArgumentArity

private theorem leafPatternMetadata :
    RawRecursorRulePatternMetadataRel catalog nameOf treeRecId treeRecConcrete
      leafRule leafPattern := by
  refine {
    recursorName := by simpa [leafPattern,
      CertifiedMutualRecursor.generatedPattern, certificateGeneration_eq,
      recursorRepresentationFacts.leafRecursorName] using nameOf_treeRec
    majorIdx := by simpa [leafPattern,
      CertifiedMutualRecursor.generatedPattern, certificateGeneration_eq] using
        recursorRepresentationFacts.treeMajor
    majorIdxCoherent := recursorRepresentationFacts.treeMajorCoherent
    ruleAt := leafRuleAt
    constructorName := by simpa [leafPattern,
      CertifiedMutualRecursor.generatedPattern,
      recursorRepresentationFacts.leafConstructorName] using nameOf_leaf
    constructorAt := ⟨treeLeafConcrete, catalog_leaf,
      recursorRepresentationFacts.leafConstructorAt⟩
    fields := recursorRepresentationFacts.leafFields }

private theorem nodePatternMetadata :
    RawRecursorRulePatternMetadataRel catalog nameOf treeRecId treeRecConcrete
      nodeRule nodePattern := by
  refine {
    recursorName := by simpa [nodePattern,
      CertifiedMutualRecursor.generatedPattern, certificateGeneration_eq,
      recursorRepresentationFacts.nodeRecursorName] using nameOf_treeRec
    majorIdx := by simpa [nodePattern,
      CertifiedMutualRecursor.generatedPattern, certificateGeneration_eq] using
        recursorRepresentationFacts.treeNodeMajor
    majorIdxCoherent := recursorRepresentationFacts.treeMajorCoherent
    ruleAt := nodeRuleAt
    constructorName := by simpa [nodePattern,
      CertifiedMutualRecursor.generatedPattern,
      recursorRepresentationFacts.nodeConstructorName] using nameOf_node
    constructorAt := ⟨treeNodeConcrete, catalog_node,
      recursorRepresentationFacts.nodeConstructorAt⟩
    fields := recursorRepresentationFacts.nodeFields }

private theorem branchPatternMetadata :
    RawRecursorRulePatternMetadataRel catalog nameOf treeRecId treeRecConcrete
      branchRule branchPattern := by
  refine {
    recursorName := by simpa [branchPattern,
      CertifiedMutualRecursor.generatedPattern, certificateGeneration_eq,
      recursorRepresentationFacts.branchRecursorName] using nameOf_treeRec
    majorIdx := by simpa [branchPattern,
      CertifiedMutualRecursor.generatedPattern, certificateGeneration_eq] using
        recursorRepresentationFacts.treeBranchMajor
    majorIdxCoherent := recursorRepresentationFacts.treeMajorCoherent
    ruleAt := branchRuleAt
    constructorName := by simpa [branchPattern,
      CertifiedMutualRecursor.generatedPattern,
      recursorRepresentationFacts.branchConstructorName] using nameOf_branch
    constructorAt := ⟨treeBranchConcrete, catalog_branch,
      recursorRepresentationFacts.branchConstructorAt⟩
    fields := recursorRepresentationFacts.branchFields }

private theorem nilPatternMetadata :
    RawRecursorRulePatternMetadataRel catalog nameOf treeListRecId
      treeListRecConcrete nilRule nilPattern := by
  refine {
    recursorName := by simpa [nilPattern,
      CertifiedMutualRecursor.generatedPattern, certificateGeneration_eq,
      recursorRepresentationFacts.nilRecursorName] using nameOf_treeListRec
    majorIdx := by simpa [nilPattern,
      CertifiedMutualRecursor.generatedPattern, certificateGeneration_eq] using
        recursorRepresentationFacts.treeListMajor
    majorIdxCoherent := recursorRepresentationFacts.treeListMajorCoherent
    ruleAt := nilRuleAt
    constructorName := by simpa [nilPattern,
      CertifiedMutualRecursor.generatedPattern,
      recursorRepresentationFacts.nilConstructorName] using nameOf_nil
    constructorAt := ⟨treeListNilConcrete, catalog_nil,
      recursorRepresentationFacts.nilConstructorAt⟩
    fields := recursorRepresentationFacts.nilFields }

private theorem consPatternMetadata :
    RawRecursorRulePatternMetadataRel catalog nameOf treeListRecId
      treeListRecConcrete consRule consPattern := by
  refine {
    recursorName := by simpa [consPattern,
      CertifiedMutualRecursor.generatedPattern, certificateGeneration_eq,
      recursorRepresentationFacts.consRecursorName] using nameOf_treeListRec
    majorIdx := by simpa [consPattern,
      CertifiedMutualRecursor.generatedPattern, certificateGeneration_eq] using
        recursorRepresentationFacts.treeListConsMajor
    majorIdxCoherent := recursorRepresentationFacts.treeListMajorCoherent
    ruleAt := consRuleAt
    constructorName := by simpa [consPattern,
      CertifiedMutualRecursor.generatedPattern,
      recursorRepresentationFacts.consConstructorName] using nameOf_cons
    constructorAt := ⟨treeListConsConcrete, catalog_cons,
      recursorRepresentationFacts.consConstructorAt⟩
    fields := recursorRepresentationFacts.consFields }

theorem leafPatternRel :
    RawRecursorRulePatternRel treeFinalEnv catalog nameOf treeRecId
      treeRecConcrete leafRule leafPattern :=
  CertifiedMutualRecursor.generatedPatternRel lean4leanCertificate
    Upstream.Pending.mutualTreePhysicalRulePatternSound
    leafEntry treeLeafId 0 1 1
    recursorRepresentationFacts.leafArgumentArity leafPatternMetadata

theorem nodePatternRel :
    RawRecursorRulePatternRel treeFinalEnv catalog nameOf treeRecId
      treeRecConcrete nodeRule nodePattern :=
  CertifiedMutualRecursor.generatedPatternRel lean4leanCertificate
    Upstream.Pending.mutualTreePhysicalRulePatternSound
    nodeEntry treeNodeId 1 1 1
    recursorRepresentationFacts.nodeArgumentArity nodePatternMetadata

theorem branchPatternRel :
    RawRecursorRulePatternRel treeFinalEnv catalog nameOf treeRecId
      treeRecConcrete branchRule branchPattern :=
  CertifiedMutualRecursor.generatedPatternRel lean4leanCertificate
    Upstream.Pending.mutualTreePhysicalRulePatternSound
    branchEntry treeBranchId 2 1 1
    recursorRepresentationFacts.branchArgumentArity branchPatternMetadata

theorem nilPatternRel :
    RawRecursorRulePatternRel treeFinalEnv catalog nameOf treeListRecId
      treeListRecConcrete nilRule nilPattern :=
  CertifiedMutualRecursor.generatedPatternRel lean4leanCertificate
    Upstream.Pending.mutualTreePhysicalRulePatternSound
    nilEntry treeListNilId 0 1 0
    recursorRepresentationFacts.nilArgumentArity nilPatternMetadata

theorem consPatternRel :
    RawRecursorRulePatternRel treeFinalEnv catalog nameOf treeListRecId
      treeListRecConcrete consRule consPattern :=
  CertifiedMutualRecursor.generatedPatternRel lean4leanCertificate
    Upstream.Pending.mutualTreePhysicalRulePatternSound
    consEntry treeListConsId 1 1 2
    recursorRepresentationFacts.consArgumentArity consPatternMetadata

/-! ## Atomic family admission in the physical permutation -/

/-- Historical adapter for the exact `TreeList, Tree` certificate.  This is
the same computed generation and post-environment exposed by the current
Lean4Lean consumer package in `Upstream.Pending`. -/
def physicalTransaction : CertifiedBlockGenerationTransaction
    Upstream.Pending.mutualTreePhysicalDecl VEnv.empty treeFinalEnv where
  certificate := Upstream.Pending.mutualTreePhysicalSemantic
  success := Upstream.Pending.mutualTreePhysicalSuccess
  beforeWF := ⟨[], .empty⟩

private theorem physicalTreeTypeRawNative :
    RawExprRel (uvars := treeConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeConcrete.ty
      treeType.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem physicalTreeTypeRaw :
    RawExprRel (uvars := treeConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeConcrete.ty
      treeType.type := physicalTreeTypeRawNative

private theorem physicalTreeListTypeRawNative :
    RawExprRel (uvars := treeListConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeListConcrete.ty
      treeListType.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem physicalTreeListTypeRaw :
    RawExprRel (uvars := treeListConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeListConcrete.ty
      treeListType.type := physicalTreeListTypeRawNative

private theorem physicalLeafTypeRawNative :
    RawExprRel (uvars := treeLeafConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeLeafConcrete.ty
      treeLeafSource.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem physicalLeafTypeRaw :
    RawExprRel (uvars := treeLeafConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeLeafConcrete.ty
      treeLeafSource.type := physicalLeafTypeRawNative

private theorem physicalNodeTypeRawNative :
    RawExprRel (uvars := treeNodeConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeNodeConcrete.ty
      treeNodeSource.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem physicalNodeTypeRaw :
    RawExprRel (uvars := treeNodeConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeNodeConcrete.ty
      treeNodeSource.type := physicalNodeTypeRawNative

private theorem physicalBranchTypeRawNative :
    RawExprRel (uvars := treeBranchConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeBranchConcrete.ty
      treeBranchSource.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem physicalBranchTypeRaw :
    RawExprRel (uvars := treeBranchConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeBranchConcrete.ty
      treeBranchSource.type := physicalBranchTypeRawNative

private theorem physicalNilTypeRawNative :
    RawExprRel (uvars := treeListNilConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeListNilConcrete.ty
      treeListNilSource.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem physicalNilTypeRaw :
    RawExprRel (uvars := treeListNilConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeListNilConcrete.ty
      treeListNilSource.type := physicalNilTypeRawNative

private theorem physicalConsTypeRawNative :
    RawExprRel (uvars := treeListConsConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeListConsConcrete.ty
      treeListConsSource.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem physicalConsTypeRaw :
    RawExprRel (uvars := treeListConsConcrete.lvls.toNat) treeFinalEnv nameOf
      RawProjRel.none [] treeListConsConcrete.ty
      treeListConsSource.type := physicalConsTypeRawNative

structure PhysicalSourceMembershipFacts : Prop where
  leaf : treeLeafSource ∈
    Upstream.Pending.mutualTreePhysicalDecl.blockConstructorConstants
  node : treeNodeSource ∈
    Upstream.Pending.mutualTreePhysicalDecl.blockConstructorConstants
  branch : treeBranchSource ∈
    Upstream.Pending.mutualTreePhysicalDecl.blockConstructorConstants
  nil : treeListNilSource ∈
    Upstream.Pending.mutualTreePhysicalDecl.blockConstructorConstants
  cons : treeListConsSource ∈
    Upstream.Pending.mutualTreePhysicalDecl.blockConstructorConstants

private theorem physicalSourceMembershipFactsNative :
    PhysicalSourceMembershipFacts := by
  constructor <;> native_decide

theorem physicalSourceMembershipFacts : PhysicalSourceMembershipFacts :=
  physicalSourceMembershipFactsNative

/-- Exhaustive seven-member representation link to the exact generation
order selected by the physical compiler.  Every address, source position,
and raw translation remains an Ix proof obligation. -/
def physicalFamilyLink :
    MutualFamilyCatalogLink RawProjRel.none world physicalTransaction where
  members := familyMembers
  nonempty := by rw [familyMembers_eq]; decide
  member := by
    intro id hmember
    rw [familyMembers_eq] at hmember
    simp at hmember
    rcases hmember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨treeListConcrete, ``TreeList, treeListType.toVConstant,
        catalog_treeList, familyMemberShapeFacts.treeListKind,
        nameOf_treeList, familyMemberShapeFacts.treeListUvars,
        physicalTreeListTypeRaw,
        .inl ⟨treeListType, by
          simp [Upstream.Pending.mutualTreePhysicalDecl], rfl, rfl⟩⟩
    · exact ⟨treeListNilConcrete, ``TreeList.nil,
        treeListNilSource.toVConstant, catalog_nil,
        familyMemberShapeFacts.nilKind, nameOf_nil,
        familyMemberShapeFacts.nilUvars, physicalNilTypeRaw,
        .inr ⟨treeListNilSource, physicalSourceMembershipFacts.nil,
          rfl, rfl⟩⟩
    · exact ⟨treeListConsConcrete, ``TreeList.cons,
        treeListConsSource.toVConstant, catalog_cons,
        familyMemberShapeFacts.consKind, nameOf_cons,
        familyMemberShapeFacts.consUvars, physicalConsTypeRaw,
        .inr ⟨treeListConsSource, physicalSourceMembershipFacts.cons,
          rfl, rfl⟩⟩
    · exact ⟨treeConcrete, ``Tree, treeType.toVConstant,
        catalog_tree, familyMemberShapeFacts.treeKind, nameOf_tree,
        familyMemberShapeFacts.treeUvars, physicalTreeTypeRaw,
        .inl ⟨treeType, by
          simp [Upstream.Pending.mutualTreePhysicalDecl], rfl, rfl⟩⟩
    · exact ⟨treeLeafConcrete, ``Tree.leaf,
        treeLeafSource.toVConstant, catalog_leaf,
        familyMemberShapeFacts.leafKind, nameOf_leaf,
        familyMemberShapeFacts.leafUvars, physicalLeafTypeRaw,
        .inr ⟨treeLeafSource, physicalSourceMembershipFacts.leaf,
          rfl, rfl⟩⟩
    · exact ⟨treeNodeConcrete, ``Tree.node,
        treeNodeSource.toVConstant, catalog_node,
        familyMemberShapeFacts.nodeKind, nameOf_node,
        familyMemberShapeFacts.nodeUvars, physicalNodeTypeRaw,
        .inr ⟨treeNodeSource, physicalSourceMembershipFacts.node,
          rfl, rfl⟩⟩
    · exact ⟨treeBranchConcrete, ``Tree.branch,
        treeBranchSource.toVConstant, catalog_branch,
        familyMemberShapeFacts.branchKind, nameOf_branch,
        familyMemberShapeFacts.branchUvars, physicalBranchTypeRaw,
        .inr ⟨treeBranchSource, physicalSourceMembershipFacts.branch,
          rfl, rfl⟩⟩
  fresh := by
    intro id _ htrusted
    exact htrusted

theorem physicalFamilyBlockCertificate :
    SemanticBlockTransitionCertificate RawProjRel.none world familyBlockId
      familyMembers .inductive' treeFinalEnv :=
  physicalFamilyLink.transition exactFamilyBlock

def physicalFamilyAcceptedWorld : VerifyWorld :=
  physicalFamilyBlockCertificate.admittedWorld

theorem physicalFamilyAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none world physicalFamilyAcceptedWorld
      familyBlockId familyMembers .inductive' :=
  physicalFamilyBlockCertificate.admit trustedCatalog

theorem physicalFamilyBlockAccepted :
    physicalFamilyAcceptedWorld.AcceptedBlock familyBlockId :=
  physicalFamilyAtomicAdmission.accepted

/-! ## Complete semantic entries and atomic recursor admission -/

private theorem treeRuleIndexBound {index : Nat} {rule : RecRule .anon}
    (hrule : treeRecConcrete.RecursorRuleAt index rule) : index < 3 := by
  rw [treeRecRuleAt_iff] at hrule
  have bound := (Array.getElem?_eq_some_iff.mp hrule).choose
  simpa [recursorRepresentationFacts.treeRuleCount] using bound

private theorem treeListRuleIndexBound {index : Nat} {rule : RecRule .anon}
    (hrule : treeListRecConcrete.RecursorRuleAt index rule) : index < 2 := by
  rw [treeListRecRuleAt_iff] at hrule
  have bound := (Array.getElem?_eq_some_iff.mp hrule).choose
  simpa [recursorRepresentationFacts.treeListRuleCount] using bound

private theorem treeRecRule {rule : RecRule .anon}
    (hrule : treeRecConcrete.HasRecursorRule rule) :
    RawRecursorRuleRel treeFinalEnv nameOf RawProjRel.none treeRecId
      treeRecConcrete rule := by
  obtain ⟨index, hindex⟩ := hrule.exists_ruleAt
  have bound := treeRuleIndexBound hindex
  rcases (show index = 0 ∨ index = 1 ∨ index = 2 by omega) with
    rfl | rfl | rfl
  · have equality := KConst.RecursorRuleAt.unique hindex
      leafRuleAt
    subst rule
    exact ⟨_, leafRegistered⟩
  · have equality := KConst.RecursorRuleAt.unique hindex
      nodeRuleAt
    subst rule
    exact ⟨_, nodeRegistered⟩
  · have equality := KConst.RecursorRuleAt.unique hindex
      branchRuleAt
    subst rule
    exact ⟨_, branchRegistered⟩

private theorem treeListRecRule {rule : RecRule .anon}
    (hrule : treeListRecConcrete.HasRecursorRule rule) :
    RawRecursorRuleRel treeFinalEnv nameOf RawProjRel.none treeListRecId
      treeListRecConcrete rule := by
  obtain ⟨index, hindex⟩ := hrule.exists_ruleAt
  have bound := treeListRuleIndexBound hindex
  rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
  · have equality := KConst.RecursorRuleAt.unique hindex
      nilRuleAt
    subst rule
    exact ⟨_, nilRegistered⟩
  · have equality := KConst.RecursorRuleAt.unique hindex
      consRuleAt
    subst rule
    exact ⟨_, consRegistered⟩

private theorem treeRecPattern {index : Nat} {rule : RecRule .anon}
    (hrule : treeRecConcrete.RecursorRuleAt index rule) :
    ∃ pattern,
      RawRecursorRulePatternRel treeFinalEnv catalog nameOf treeRecId
        treeRecConcrete rule pattern ∧ pattern.ruleIndex = index := by
  have bound := treeRuleIndexBound hrule
  rcases (show index = 0 ∨ index = 1 ∨ index = 2 by omega) with
    rfl | rfl | rfl
  · have equality := KConst.RecursorRuleAt.unique hrule
      leafRuleAt
    subst rule
    exact ⟨leafPattern, leafPatternRel, rfl⟩
  · have equality := KConst.RecursorRuleAt.unique hrule
      nodeRuleAt
    subst rule
    exact ⟨nodePattern, nodePatternRel, rfl⟩
  · have equality := KConst.RecursorRuleAt.unique hrule
      branchRuleAt
    subst rule
    exact ⟨branchPattern, branchPatternRel, rfl⟩

private theorem treeListRecPattern {index : Nat} {rule : RecRule .anon}
    (hrule : treeListRecConcrete.RecursorRuleAt index rule) :
    ∃ pattern,
      RawRecursorRulePatternRel treeFinalEnv catalog nameOf treeListRecId
        treeListRecConcrete rule pattern ∧ pattern.ruleIndex = index := by
  have bound := treeListRuleIndexBound hrule
  rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
  · have equality := KConst.RecursorRuleAt.unique hrule
      nilRuleAt
    subst rule
    exact ⟨nilPattern, nilPatternRel, rfl⟩
  · have equality := KConst.RecursorRuleAt.unique hrule
      consRuleAt
    subst rule
    exact ⟨consPattern, consPatternRel, rfl⟩

private theorem treeRecSemanticEntry :
    TrustedCatalogEntry RawProjRel.none catalog nameOf treeFinalEnv treeRecId :=
  .ambient catalog_treeRec treeRecRaw treeRecLookup
    (lean4leanCertificate.afterWF.ordered.constWF treeRecLookup)
    (fun {_} hrule => treeRecRule hrule)
    (fun {_ _} hrule => treeRecPattern hrule)

private theorem treeListRecSemanticEntry :
    TrustedCatalogEntry RawProjRel.none catalog nameOf treeFinalEnv
      treeListRecId :=
  .ambient catalog_treeListRec treeListRecRaw treeListRecLookup
    (lean4leanCertificate.afterWF.ordered.constWF treeListRecLookup)
    (fun {_} hrule => treeListRecRule hrule)
    (fun {_ _} hrule => treeListRecPattern hrule)

theorem familyTreeRecSemanticEntry :
    TrustedCatalogEntry RawProjRel.none physicalFamilyAcceptedWorld.catalog
      physicalFamilyAcceptedWorld.nameOf physicalFamilyAcceptedWorld.venv
      treeRecId := by
  change TrustedCatalogEntry RawProjRel.none catalog nameOf treeFinalEnv
    treeRecId
  exact treeRecSemanticEntry

theorem familyTreeListRecSemanticEntry :
    TrustedCatalogEntry RawProjRel.none physicalFamilyAcceptedWorld.catalog
      physicalFamilyAcceptedWorld.nameOf physicalFamilyAcceptedWorld.venv
      treeListRecId := by
  change TrustedCatalogEntry RawProjRel.none catalog nameOf treeFinalEnv
    treeListRecId
  exact treeListRecSemanticEntry

private theorem treeRecNotFamily : treeRecId ∉ familyMembers := by
  rw [familyMembers_eq]
  native_decide

private theorem treeListRecNotFamily : treeListRecId ∉ familyMembers := by
  rw [familyMembers_eq]
  native_decide

theorem physicalFamilyAcceptedWorld_recursors_fresh {id : KId .anon}
    (hmember : id ∈ recursorMembers) :
    ¬physicalFamilyAcceptedWorld.trusted id := by
  change ¬(id ∈ familyMembers ∨ world.trusted id)
  rw [recursorMembers_eq] at hmember
  simp at hmember
  rcases hmember with rfl | rfl
  · intro htrusted
    rcases htrusted with hfamily | hold
    · exact treeListRecNotFamily hfamily
    · exact hold
  · intro htrusted
    rcases htrusted with hfamily | hold
    · exact treeRecNotFamily hfamily
    · exact hold

theorem exactRecursorBlockAfterFamily :
    ExactCheckBlock physicalFamilyAcceptedWorld recursorBlockId recursorMembers
      .recursor :=
  exactRecursorBlock.rebaseWorld physicalFamilyAtomicAdmission.promotion.le

theorem familyRecursorBlockCertificate :
    ExistingSemanticBlockCertificate RawProjRel.none
      physicalFamilyAcceptedWorld
      recursorBlockId recursorMembers .recursor where
  exactBlock := exactRecursorBlockAfterFamily
  fresh := fun {_} hmember =>
    physicalFamilyAcceptedWorld_recursors_fresh hmember
  entry := by
    intro id hmember
    rw [recursorMembers_eq] at hmember
    simp at hmember
    rcases hmember with rfl | rfl
    · exact familyTreeListRecSemanticEntry
    · exact familyTreeRecSemanticEntry

def familyRecursorAcceptedWorld : VerifyWorld :=
  familyRecursorBlockCertificate.admittedWorld

theorem familyRecursorAtomicAdmission :
    AtomicBlockAdmission RawProjRel.none physicalFamilyAcceptedWorld
      familyRecursorAcceptedWorld recursorBlockId recursorMembers .recursor :=
  familyRecursorBlockCertificate.admit
    physicalFamilyAtomicAdmission.trustedCatalog

theorem familyRecursorBlockAccepted :
    familyRecursorAcceptedWorld.AcceptedBlock recursorBlockId :=
  familyRecursorAtomicAdmission.accepted

/-- E3-FP's first conditional mutual checkpoint.  Every physical and
semantic fact is closed for the two-family/five-constructor/two-recursor
transaction.  Its transitive trust boundary retains exactly the two
quarantined upstream witnesses: reversed-family generation WF and generated
rule-pattern soundness. -/
structure MutualRecursorConditionalClosure : Prop where
  execution : EndToEndExecution
  family : MutualFamilyAtomicClosure
  patternSound : CertifiedBlockRulePatternSound lean4leanCertificate
  physicalFamilyAdmission :
    AtomicBlockAdmission RawProjRel.none world physicalFamilyAcceptedWorld
      familyBlockId familyMembers .inductive'
  recursorAdmission :
    AtomicBlockAdmission RawProjRel.none physicalFamilyAcceptedWorld
      familyRecursorAcceptedWorld recursorBlockId recursorMembers .recursor
  familyAccepted : familyRecursorAcceptedWorld.AcceptedBlock familyBlockId
  recursorAccepted : familyRecursorAcceptedWorld.AcceptedBlock recursorBlockId

theorem mutualRecursorConditionalClosure :
    MutualRecursorConditionalClosure where
  execution := endToEndExecution
  family := mutualFamilyAtomicClosure
  patternSound := Upstream.Pending.mutualTreePhysicalRulePatternSound
  physicalFamilyAdmission := physicalFamilyAtomicAdmission
  recursorAdmission := familyRecursorAtomicAdmission
  familyAccepted :=
    physicalFamilyBlockAccepted.mono
      familyRecursorAtomicAdmission.promotion.le
  recursorAccepted := familyRecursorBlockAccepted

end Ix.Tc.MutualTreeFixture
