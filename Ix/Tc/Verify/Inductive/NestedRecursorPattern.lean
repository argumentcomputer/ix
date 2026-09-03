import Ix.Tc.Verify.Inductive.IotaPattern
import Ix.Tc.Verify.Inductive.NestedRecursorFixture

/-!
# Physical restored-recursion patterns for `LeanTree`

The aux-aware compiler emits one physical recursor for the stored `LeanTree`
family and one for the flattened `LeanBox LeanTree` dependency.  Lean4Lean's
nested transaction restores those declarations as `LeanTree.rec` and
`LeanTree.rec_1`, with one registered equation apiece.  This module proves the
complete representation correspondence and constructs the exact two iota
patterns consumed by semantic admission.
-/

namespace Ix.Tc.NestedRecursiveFixture

open Lean4Lean
open InductiveConcreteFixture

local instance nestedPatternAddressDecidableEq : DecidableEq Address :=
  AnonStructural.addressDecidableEq

local instance nestedPatternKIdDecidableEq : DecidableEq (KId .anon) :=
  AnonStructural.idDecidableEq

local instance nestedPatternKConstDecidableEq : DecidableEq (KConst .anon) :=
  AnonStructural.constDecidableEq

local instance nestedPatternInductiveMemberDecidable
    (concrete : KConst .anon) : Decidable concrete.IsInductiveMember := by
  cases concrete <;>
    simp only [KConst.IsInductiveMember] <;> infer_instance

local instance nestedPatternMajorCoherentDecidable
    (concrete : KConst .anon) :
    Decidable concrete.RecursorMajorIdxCoherent := by
  cases concrete <;>
    simp only [KConst.RecursorMajorIdxCoherent] <;> infer_instance

local instance nestedPatternConstructorAtDecidable
    (concrete : KConst .anon) (index : Nat) (params fields : UInt64) :
    Decidable (concrete.ConstructorAt index params fields) := by
  cases concrete <;> simp only [KConst.ConstructorAt] <;> infer_instance

/-! ## Immutable catalog and source names -/

/-- The full immutable catalog needed by the nested family and its generated
recursor block.  `LeanBox` and `LeanBox.wrap` are included because the copied
dependency rule dispatches on the latter. -/
def nestedRecursorCatalog : Catalog := fun id =>
  if id == boxId then some boxConcrete
  else if id == wrapId then some wrapConcrete
  else if id == treeId then some treeConcrete
  else if id == nodeId then some nodeConcrete
  else if id == treeRecId then some treeRecConcrete
  else if id == treeRecOneId then some treeRecOneConcrete
  else none

def nestedRecursorNameOf (address : Address) : Option Lean.Name :=
  if address == boxId.addr then some ``LeanBox
  else if address == wrapId.addr then some ``LeanBox.wrap
  else if address == treeId.addr then some ``LeanTree
  else if address == nodeId.addr then some ``LeanTree.node
  else if address == treeRecId.addr then some ``LeanTree.rec
  else if address == treeRecOneId.addr then some ``LeanTree.rec_1
  else none

theorem nestedRecursorCatalog_box :
    nestedRecursorCatalog boxId = some boxConcrete := by
  unfold nestedRecursorCatalog
  rw [if_pos (by native_decide)]

theorem nestedRecursorCatalog_wrap :
    nestedRecursorCatalog wrapId = some wrapConcrete := by
  unfold nestedRecursorCatalog
  rw [if_neg (by native_decide), if_pos (by native_decide)]

theorem nestedRecursorCatalog_tree :
    nestedRecursorCatalog treeId = some treeConcrete := by
  unfold nestedRecursorCatalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem nestedRecursorCatalog_node :
    nestedRecursorCatalog nodeId = some nodeConcrete := by
  unfold nestedRecursorCatalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]

theorem nestedRecursorCatalog_treeRec :
    nestedRecursorCatalog treeRecId = some treeRecConcrete := by
  unfold nestedRecursorCatalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem nestedRecursorCatalog_treeRecOne :
    nestedRecursorCatalog treeRecOneId = some treeRecOneConcrete := by
  unfold nestedRecursorCatalog
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]

theorem nestedRecursorNameOf_box :
    nestedRecursorNameOf boxId.addr = some ``LeanBox := by
  unfold nestedRecursorNameOf
  rw [if_pos (by native_decide)]

theorem nestedRecursorNameOf_wrap :
    nestedRecursorNameOf wrapId.addr = some ``LeanBox.wrap := by
  unfold nestedRecursorNameOf
  rw [if_neg (by native_decide), if_pos (by native_decide)]

theorem nestedRecursorNameOf_tree :
    nestedRecursorNameOf treeId.addr = some ``LeanTree := by
  unfold nestedRecursorNameOf
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem nestedRecursorNameOf_node :
    nestedRecursorNameOf nodeId.addr = some ``LeanTree.node := by
  unfold nestedRecursorNameOf
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]

theorem nestedRecursorNameOf_treeRec :
    nestedRecursorNameOf treeRecId.addr = some ``LeanTree.rec := by
  unfold nestedRecursorNameOf
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_pos (by native_decide)]

theorem nestedRecursorNameOf_treeRecOne :
    nestedRecursorNameOf treeRecOneId.addr = some ``LeanTree.rec_1 := by
  unfold nestedRecursorNameOf
  rw [if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_neg (by native_decide),
    if_neg (by native_decide), if_pos (by native_decide)]

/-! ## Exact physical rules and finite representation facts -/

def nestedRecursorRules : KConst .anon → Array (RecRule .anon)
  | .recr (rules := rules) .. => rules
  | _ => #[]

def treeRecRules : Array (RecRule .anon) :=
  nestedRecursorRules treeRecConcrete

def treeRecOneRules : Array (RecRule .anon) :=
  nestedRecursorRules treeRecOneConcrete

private theorem treeRecRuleZero : 0 < treeRecRules.size := by
  native_decide

private theorem treeRecOneRuleZero : 0 < treeRecOneRules.size := by
  native_decide

def treeNodeRecRule : RecRule .anon :=
  treeRecRules[0]'treeRecRuleZero

def treeWrapRecRule : RecRule .anon :=
  treeRecOneRules[0]'treeRecOneRuleZero

theorem treeRecRuleAt_iff {index : Nat} {rule : RecRule .anon} :
    treeRecConcrete.RecursorRuleAt index rule ↔
      treeRecRules[index]? = some rule := by
  unfold KConst.RecursorRuleAt treeRecRules nestedRecursorRules
  cases treeRecConcrete <;> simp

theorem treeRecOneRuleAt_iff {index : Nat} {rule : RecRule .anon} :
    treeRecOneConcrete.RecursorRuleAt index rule ↔
      treeRecOneRules[index]? = some rule := by
  unfold KConst.RecursorRuleAt treeRecOneRules nestedRecursorRules
  cases treeRecOneConcrete <;> simp

theorem treeNodeRecRuleAt :
    treeRecConcrete.RecursorRuleAt 0 treeNodeRecRule := by
  rw [treeRecRuleAt_iff, Array.getElem?_eq_getElem treeRecRuleZero]
  congr

theorem treeWrapRecRuleAt :
    treeRecOneConcrete.RecursorRuleAt 0 treeWrapRecRule := by
  rw [treeRecOneRuleAt_iff,
    Array.getElem?_eq_getElem treeRecOneRuleZero]
  congr

/-- All decidable physical layout facts are evaluated at one explicit native
boundary.  Semantic soundness is proved separately below. -/
structure NestedRecursorRepresentationFacts : Prop where
  treeRecKind : treeRecConcrete.IsInductiveMember
  treeRecOneKind : treeRecOneConcrete.IsInductiveMember
  treeRecUvars :
    treeRecConcrete.lvls.toNat = semanticTreeRec.toVConstant.uvars
  treeRecOneUvars :
    treeRecOneConcrete.lvls.toNat = semanticTreeRecOne.toVConstant.uvars
  treeRuleCount : treeRecRules.size = 1
  treeRecOneRuleCount : treeRecOneRules.size = 1
  treeMajor : treeRecConcrete.RecursorMajorIdx = some 4
  treeRecOneMajor : treeRecOneConcrete.RecursorMajorIdx = some 4
  treeMajorCoherent : treeRecConcrete.RecursorMajorIdxCoherent
  treeRecOneMajorCoherent : treeRecOneConcrete.RecursorMajorIdxCoherent
  nodeConstructorAt : nodeConcrete.ConstructorAt 0 0 1
  wrapConstructorAt : wrapConcrete.ConstructorAt 0 1 1
  nodeFields : treeNodeRecRule.fields = 1
  wrapFields : treeWrapRecRule.fields = 1
  nodeBinderCore : treeNodeRecRule.rhs.binderCore = true
  wrapBinderCore : treeWrapRecRule.rhs.binderCore = true
  nodeScoped : treeNodeRecRule.rhs.Scoped 0 semanticTreeNodeRule.uvars
  wrapScoped : treeWrapRecRule.rhs.Scoped 0 semanticTreeWrapRule.uvars
  nodeSize : treeNodeRecRule.rhs.size < UInt64.size
  wrapSize : treeWrapRecRule.rhs.size < UInt64.size

private theorem nestedRecursorRepresentationFactsNative :
    NestedRecursorRepresentationFacts := by
  constructor <;> native_decide

theorem nestedRecursorRepresentationFacts :
    NestedRecursorRepresentationFacts :=
  nestedRecursorRepresentationFactsNative

/-! ## Structural translation and exact registered equations -/

private theorem treeRecTypeRawNative :
    RawExprRel (uvars := treeRecConcrete.lvls.toNat) semanticTreeEnv
      nestedRecursorNameOf RawProjRel.none [] treeRecConcrete.ty
      semanticTreeRec.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem treeRecTypeRaw :
    RawExprRel (uvars := treeRecConcrete.lvls.toNat) semanticTreeEnv
      nestedRecursorNameOf RawProjRel.none [] treeRecConcrete.ty
      semanticTreeRec.type :=
  treeRecTypeRawNative

private theorem treeRecOneTypeRawNative :
    RawExprRel (uvars := treeRecOneConcrete.lvls.toNat) semanticTreeEnv
      nestedRecursorNameOf RawProjRel.none [] treeRecOneConcrete.ty
      semanticTreeRecOne.type := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem treeRecOneTypeRaw :
    RawExprRel (uvars := treeRecOneConcrete.lvls.toNat) semanticTreeEnv
      nestedRecursorNameOf RawProjRel.none [] treeRecOneConcrete.ty
      semanticTreeRecOne.type :=
  treeRecOneTypeRawNative

private theorem treeNodeRuleRawNative :
    RawExprRel (uvars := semanticTreeNodeRule.uvars) semanticTreeEnv
      nestedRecursorNameOf RawProjRel.none [] treeNodeRecRule.rhs
      semanticTreeNodeRule.rhs := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem treeNodeRuleRaw :
    RawExprRel (uvars := semanticTreeNodeRule.uvars) semanticTreeEnv
      nestedRecursorNameOf RawProjRel.none [] treeNodeRecRule.rhs
      semanticTreeNodeRule.rhs :=
  treeNodeRuleRawNative

private theorem treeWrapRuleRawNative :
    RawExprRel (uvars := semanticTreeWrapRule.uvars) semanticTreeEnv
      nestedRecursorNameOf RawProjRel.none [] treeWrapRecRule.rhs
      semanticTreeWrapRule.rhs := by
  apply InductiveConcreteFixture.translateCore?_raw
  native_decide

theorem treeWrapRuleRaw :
    RawExprRel (uvars := semanticTreeWrapRule.uvars) semanticTreeEnv
      nestedRecursorNameOf RawProjRel.none [] treeWrapRecRule.rhs
      semanticTreeWrapRule.rhs :=
  treeWrapRuleRawNative

theorem semanticTreeNodeRuleFinalWF :
    semanticTreeNodeRule.WF semanticTreeEnv :=
  semanticTreeEnvWF.ordered.defEqWF
    semanticTreeTransactionFacts.sourceRule

theorem semanticTreeWrapRuleFinalWF :
    semanticTreeWrapRule.WF semanticTreeEnv :=
  semanticTreeEnvWF.ordered.defEqWF
    semanticTreeTransactionFacts.dependencyRule

theorem treeNodeRuleTyped :
    TrKExprS semanticTreeEnv semanticTreeNodeRule.uvars
      nestedRecursorNameOf RawProjRel.none [] treeNodeRecRule.rhs
      semanticTreeNodeRule.rhs := by
  let pre := treeNodeRuleRaw.toPreBinderCore_of_scoped
    nestedRecursorRepresentationFacts.nodeBinderCore
    nestedRecursorRepresentationFacts.nodeScoped
    nestedRecursorRepresentationFacts.nodeSize
  exact pre.upgradeBinderCoreOfWF semanticTreeEnvWF
    (Delta := []) (hDelta := trivial)
    nestedRecursorRepresentationFacts.nodeBinderCore
    ⟨_, semanticTreeNodeRuleFinalWF.2⟩

theorem treeWrapRuleTyped :
    TrKExprS semanticTreeEnv semanticTreeWrapRule.uvars
      nestedRecursorNameOf RawProjRel.none [] treeWrapRecRule.rhs
      semanticTreeWrapRule.rhs := by
  let pre := treeWrapRuleRaw.toPreBinderCore_of_scoped
    nestedRecursorRepresentationFacts.wrapBinderCore
    nestedRecursorRepresentationFacts.wrapScoped
    nestedRecursorRepresentationFacts.wrapSize
  exact pre.upgradeBinderCoreOfWF semanticTreeEnvWF
    (Delta := []) (hDelta := trivial)
    nestedRecursorRepresentationFacts.wrapBinderCore
    ⟨_, semanticTreeWrapRuleFinalWF.2⟩

theorem treeRecRaw :
    RawInductiveConstRel semanticTreeEnv nestedRecursorNameOf RawProjRel.none
      treeRecId treeRecConcrete ``LeanTree.rec semanticTreeRec.toVConstant where
  kind := nestedRecursorRepresentationFacts.treeRecKind
  nameEq := nestedRecursorNameOf_treeRec
  uvars := nestedRecursorRepresentationFacts.treeRecUvars
  type := treeRecTypeRaw

theorem treeRecOneRaw :
    RawInductiveConstRel semanticTreeEnv nestedRecursorNameOf RawProjRel.none
      treeRecOneId treeRecOneConcrete ``LeanTree.rec_1
      semanticTreeRecOne.toVConstant where
  kind := nestedRecursorRepresentationFacts.treeRecOneKind
  nameEq := nestedRecursorNameOf_treeRecOne
  uvars := nestedRecursorRepresentationFacts.treeRecOneUvars
  type := treeRecOneTypeRaw

private def hasHeadConst (name : Lean.Name) : VExpr → Bool
  | .const actual _ => actual == name
  | .app function _ => hasHeadConst name function
  | _ => false

private theorem hasHeadConst_sound {name : Lean.Name} :
    ∀ {expression : VExpr}, hasHeadConst name expression = true →
      HeadConst name expression
  | .const actual levels, h => by
      simp only [hasHeadConst, beq_iff_eq] at h
      subst actual
      exact .const levels
  | .app function argument, h =>
      .app (hasHeadConst_sound (by simpa [hasHeadConst] using h))
  | .bvar _, h => by simp [hasHeadConst] at h
  | .sort _, h => by simp [hasHeadConst] at h
  | .lam _ _, h => by simp [hasHeadConst] at h
  | .forallE _ _, h => by simp [hasHeadConst] at h

private def hasHeadConstUnderLambdas (name : Lean.Name) : VExpr → Bool
  | .lam _ body => hasHeadConstUnderLambdas name body
  | expression => hasHeadConst name expression

private theorem hasHeadConstUnderLambdas_sound {name : Lean.Name} :
    ∀ {expression : VExpr},
      hasHeadConstUnderLambdas name expression = true →
        HeadConstUnderLambdas name expression
  | .lam type body, h =>
      .lam (hasHeadConstUnderLambdas_sound
        (by simpa [hasHeadConstUnderLambdas] using h))
  | .bvar _, h => .head (hasHeadConst_sound
      (by simpa [hasHeadConstUnderLambdas] using h))
  | .sort _, h => .head (hasHeadConst_sound
      (by simpa [hasHeadConstUnderLambdas] using h))
  | .const _ _, h => .head (hasHeadConst_sound
      (by simpa [hasHeadConstUnderLambdas] using h))
  | .app _ _, h => .head (hasHeadConst_sound
      (by simpa [hasHeadConstUnderLambdas] using h))
  | .forallE _ _, h => .head (hasHeadConst_sound
      (by simpa [hasHeadConstUnderLambdas] using h))

private theorem treeNodeRuleHeadNative :
    hasHeadConstUnderLambdas ``LeanTree.rec semanticTreeNodeRule.lhs = true := by
  native_decide

theorem treeNodeRuleHead :
    HeadConstUnderLambdas ``LeanTree.rec semanticTreeNodeRule.lhs :=
  hasHeadConstUnderLambdas_sound treeNodeRuleHeadNative

private theorem treeWrapRuleHeadNative :
    hasHeadConstUnderLambdas ``LeanTree.rec_1 semanticTreeWrapRule.lhs = true := by
  native_decide

theorem treeWrapRuleHead :
    HeadConstUnderLambdas ``LeanTree.rec_1 semanticTreeWrapRule.lhs :=
  hasHeadConstUnderLambdas_sound treeWrapRuleHeadNative

theorem treeNodeRuleRegistered :
    RegisteredRecursorRuleRhsRel semanticTreeEnv nestedRecursorNameOf
      RawProjRel.none treeRecId treeRecConcrete treeNodeRecRule
      semanticTreeNodeRule :=
  ⟨``LeanTree.rec, semanticTreeRec.toVConstant, treeRecRaw,
    semanticTreeTransactionFacts.primaryRecursor,
    semanticTreeTransactionFacts.sourceRule,
    semanticTreeNodeRuleFinalWF, treeNodeRuleHead, treeNodeRuleRaw,
    treeNodeRuleTyped⟩

theorem treeWrapRuleRegistered :
    RegisteredRecursorRuleRhsRel semanticTreeEnv nestedRecursorNameOf
      RawProjRel.none treeRecOneId treeRecOneConcrete treeWrapRecRule
      semanticTreeWrapRule :=
  ⟨``LeanTree.rec_1, semanticTreeRecOne.toVConstant, treeRecOneRaw,
    semanticTreeTransactionFacts.dependencyRecursor,
    semanticTreeTransactionFacts.dependencyRule,
    semanticTreeWrapRuleFinalWF, treeWrapRuleHead, treeWrapRuleRaw,
    treeWrapRuleTyped⟩

/-! ## Exact restored iota payloads -/

private def nestedRhsAppN {pattern : Pattern} : pattern.RHS →
    List pattern.RHS → pattern.RHS
  | head, [] => head
  | head, argument :: rest => nestedRhsAppN (.app head argument) rest

@[simp] theorem nestedRhsAppN_apply {pattern : Pattern}
    (head : pattern.RHS) (arguments : List pattern.RHS)
    (levels : List VLevel) (captures : pattern.Path → VExpr) :
    (nestedRhsAppN head arguments).apply levels captures =
      VExpr.appN (head.apply levels captures)
        (arguments.map (Pattern.RHS.apply levels captures)) := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument rest ih =>
      simp only [nestedRhsAppN, ih, Pattern.RHS.apply, List.map_cons,
        VExpr.appN]

private def nodeRecursorArgumentRhs (index : Fin 4) :
    (RecursorIotaPattern ``LeanTree.rec 4 ``LeanTree.node 1).RHS :=
  RecursorIotaPattern.recursorArgumentRhs ``LeanTree.rec 4
    ``LeanTree.node 1 index

private def nodeConstructorArgumentRhs (index : Fin 1) :
    (RecursorIotaPattern ``LeanTree.rec 4 ``LeanTree.node 1).RHS :=
  RecursorIotaPattern.constructorArgumentRhs ``LeanTree.rec 4
    ``LeanTree.node 1 index

private def wrapRecursorArgumentRhs (index : Fin 4) :
    (RecursorIotaPattern ``LeanTree.rec_1 4 ``LeanBox.wrap 2).RHS :=
  RecursorIotaPattern.recursorArgumentRhs ``LeanTree.rec_1 4
    ``LeanBox.wrap 2 index

private def wrapConstructorArgumentRhs (index : Fin 2) :
    (RecursorIotaPattern ``LeanTree.rec_1 4 ``LeanBox.wrap 2).RHS :=
  RecursorIotaPattern.constructorArgumentRhs ``LeanTree.rec_1 4
    ``LeanBox.wrap 2 index

private theorem treeNodeSemanticRhsClosed : semanticTreeNodeRule.rhs.Closed :=
  semanticTreeNodeRuleFinalWF.2.closedN semanticTreeEnvWF.ordered (by trivial)

private theorem treeWrapSemanticRhsClosed : semanticTreeWrapRule.rhs.Closed :=
  semanticTreeWrapRuleFinalWF.2.closedN semanticTreeEnvWF.ordered (by trivial)

def treeNodePatternRhs :
    (RecursorIotaPattern ``LeanTree.rec 4 ``LeanTree.node 1).RHS :=
  nestedRhsAppN
    (.fixed semanticTreeNodeRule.rhs treeNodeSemanticRhsClosed)
    [ nodeRecursorArgumentRhs ⟨0, by omega⟩,
      nodeRecursorArgumentRhs ⟨1, by omega⟩,
      nodeRecursorArgumentRhs ⟨2, by omega⟩,
      nodeRecursorArgumentRhs ⟨3, by omega⟩,
      nodeConstructorArgumentRhs ⟨0, by omega⟩ ]

def treeWrapPatternRhs :
    (RecursorIotaPattern ``LeanTree.rec_1 4 ``LeanBox.wrap 2).RHS :=
  nestedRhsAppN
    (.fixed semanticTreeWrapRule.rhs treeWrapSemanticRhsClosed)
    [ wrapRecursorArgumentRhs ⟨0, by omega⟩,
      wrapRecursorArgumentRhs ⟨1, by omega⟩,
      wrapRecursorArgumentRhs ⟨2, by omega⟩,
      wrapRecursorArgumentRhs ⟨3, by omega⟩,
      wrapConstructorArgumentRhs ⟨1, by omega⟩ ]

/-- The restored dependency equation is specialized to `LeanBox LeanTree`;
the physical constructor still carries its ordinary uniform parameter. -/
def treeWrapPatternChecks :
    (RecursorIotaPattern ``LeanTree.rec_1 4 ``LeanBox.wrap 2).Check :=
  .defeq (wrapConstructorArgumentRhs ⟨0, by omega⟩)
    (.fixed (.const ``LeanTree []) (by trivial)) .true

def treeNodePattern : RecursorRulePattern where
  recursorName := ``LeanTree.rec
  constructorId := nodeId
  constructorName := ``LeanTree.node
  constructorParams := 0
  constructorFields := 1
  ruleIndex := 0
  majorIdx := 4
  rhs := treeNodePatternRhs
  checks := .true

def treeWrapPattern : RecursorRulePattern where
  recursorName := ``LeanTree.rec_1
  constructorId := wrapId
  constructorName := ``LeanBox.wrap
  constructorParams := 1
  constructorFields := 1
  ruleIndex := 0
  majorIdx := 4
  rhs := treeWrapPatternRhs
  checks := treeWrapPatternChecks

@[simp] theorem treeNodePattern_rhs_apply (u : VLevel)
    (captures : (RecursorIotaPattern ``LeanTree.rec 4
      ``LeanTree.node 1).Path → VExpr) :
    treeNodePattern.rhs.apply [u] captures =
      VExpr.appN (semanticTreeNodeRule.rhs.instL [u])
        [ captures (RecursorIotaPattern.recursorArgumentPath
            ``LeanTree.rec 4 ``LeanTree.node 1 ⟨0, by omega⟩),
          captures (RecursorIotaPattern.recursorArgumentPath
            ``LeanTree.rec 4 ``LeanTree.node 1 ⟨1, by omega⟩),
          captures (RecursorIotaPattern.recursorArgumentPath
            ``LeanTree.rec 4 ``LeanTree.node 1 ⟨2, by omega⟩),
          captures (RecursorIotaPattern.recursorArgumentPath
            ``LeanTree.rec 4 ``LeanTree.node 1 ⟨3, by omega⟩),
          captures (RecursorIotaPattern.constructorArgumentPath
            ``LeanTree.rec 4 ``LeanTree.node 1 ⟨0, by omega⟩) ] := by
  simp [treeNodePattern, treeNodePatternRhs, nestedRhsAppN_apply,
    nodeRecursorArgumentRhs, nodeConstructorArgumentRhs, Pattern.RHS.apply]

@[simp] theorem treeWrapPattern_rhs_apply (u : VLevel)
    (captures : (RecursorIotaPattern ``LeanTree.rec_1 4
      ``LeanBox.wrap 2).Path → VExpr) :
    treeWrapPattern.rhs.apply [u] captures =
      VExpr.appN (semanticTreeWrapRule.rhs.instL [u])
        [ captures (RecursorIotaPattern.recursorArgumentPath
            ``LeanTree.rec_1 4 ``LeanBox.wrap 2 ⟨0, by omega⟩),
          captures (RecursorIotaPattern.recursorArgumentPath
            ``LeanTree.rec_1 4 ``LeanBox.wrap 2 ⟨1, by omega⟩),
          captures (RecursorIotaPattern.recursorArgumentPath
            ``LeanTree.rec_1 4 ``LeanBox.wrap 2 ⟨2, by omega⟩),
          captures (RecursorIotaPattern.recursorArgumentPath
            ``LeanTree.rec_1 4 ``LeanBox.wrap 2 ⟨3, by omega⟩),
          captures (RecursorIotaPattern.constructorArgumentPath
            ``LeanTree.rec_1 4 ``LeanBox.wrap 2 ⟨1, by omega⟩) ] := by
  simp [treeWrapPattern, treeWrapPatternRhs, nestedRhsAppN_apply,
    wrapRecursorArgumentRhs, wrapConstructorArgumentRhs,
    Pattern.RHS.apply]

theorem treeWrapPattern_checks_ok
    (defeq : VExpr → VExpr → Prop) (levels : List VLevel)
    (captures : (RecursorIotaPattern ``LeanTree.rec_1 4
      ``LeanBox.wrap 2).Path → VExpr)
    (hchecks : treeWrapPattern.checks.OK defeq levels captures) :
    defeq
      (captures (RecursorIotaPattern.constructorArgumentPath
        ``LeanTree.rec_1 4 ``LeanBox.wrap 2 ⟨0, by omega⟩))
      (.const ``LeanTree []) := by
  simpa [treeWrapPattern, treeWrapPatternChecks,
    wrapConstructorArgumentRhs, Pattern.Check.OK, Pattern.RHS.apply,
    VExpr.instL, VLevel.inst] using hchecks

/-! ## Exact pattern metadata -/

theorem treeNodePatternMetadata :
    RawRecursorRulePatternMetadataRel nestedRecursorCatalog
      nestedRecursorNameOf treeRecId treeRecConcrete treeNodeRecRule
      treeNodePattern where
  recursorName := by
    simpa [treeNodePattern] using nestedRecursorNameOf_treeRec
  majorIdx := by
    simpa [treeNodePattern] using nestedRecursorRepresentationFacts.treeMajor
  majorIdxCoherent := nestedRecursorRepresentationFacts.treeMajorCoherent
  ruleAt := treeNodeRecRuleAt
  constructorName := by
    simpa [treeNodePattern] using nestedRecursorNameOf_node
  constructorAt := ⟨nodeConcrete, nestedRecursorCatalog_node, by
    simpa [treeNodePattern] using
      nestedRecursorRepresentationFacts.nodeConstructorAt⟩
  fields := by
    simpa [treeNodePattern] using nestedRecursorRepresentationFacts.nodeFields

theorem treeWrapPatternMetadata :
    RawRecursorRulePatternMetadataRel nestedRecursorCatalog
      nestedRecursorNameOf treeRecOneId treeRecOneConcrete treeWrapRecRule
      treeWrapPattern where
  recursorName := by
    simpa [treeWrapPattern] using nestedRecursorNameOf_treeRecOne
  majorIdx := by
    simpa [treeWrapPattern] using
      nestedRecursorRepresentationFacts.treeRecOneMajor
  majorIdxCoherent := nestedRecursorRepresentationFacts.treeRecOneMajorCoherent
  ruleAt := treeWrapRecRuleAt
  constructorName := by
    simpa [treeWrapPattern] using nestedRecursorNameOf_wrap
  constructorAt := ⟨wrapConcrete, nestedRecursorCatalog_wrap, by
    simpa [treeWrapPattern] using
      nestedRecursorRepresentationFacts.wrapConstructorAt⟩
  fields := by
    simpa [treeWrapPattern] using nestedRecursorRepresentationFacts.wrapFields

/-- Narrow Theory-only interface for the two concrete restored equations.
The representation, metadata, translation, checker, and admission obligations
do not occur in this interface. -/
structure NestedRestoredPatternSound : Prop where
  node : treeNodePattern.Sound semanticTreeEnv
  wrap : treeWrapPattern.Sound semanticTreeEnv

end Ix.Tc.NestedRecursiveFixture
