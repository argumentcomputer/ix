import Ix.Tc.Verify.Inductive.Certificate
import Ix.Tc.Verify.Inductive.NestedBlockCertificate
import Ix.Tc.Verify.Inductive.NestedConstructorValidation
import Lean4Lean.Verify.Environment.NestedReplay

/-!
# Semantic transaction for the concrete nested `LeanBox`/`LeanTree` fixture

The operational fixture has already connected Ix ingress and positivity to
Lean4Lean's flattened constructor validation.  This module keeps the same
exact names and builds the missing Theory half:

* a certified dependency transaction for `LeanBox`;
* the analyzer-produced `NestedBlockChecked` for `LeanTree`;
* restored source-family, constructor, recursor, and rule phase environments;
* one successful `NestedBlockCertificate`/`addInductNested` transaction.

The generated literals below are elaboration-time quotations of closed
analyzer data.  Separate equality theorems pin them both to the analyzer and
to Lean's stored nested metadata, so they cannot be substituted for semantic
or physical correspondence evidence.
-/

namespace Ix.Tc.NestedRecursiveFixture

open Lean
open Lean4Lean
open Lean4Lean.InductiveReplayFixtures
open Lean4Lean.NestedRepresentation
open VInductDecl

local instance : Inhabited VEnv := ⟨.empty⟩
local instance : Inhabited VConstVal :=
  ⟨⟨⟨0, .sort .zero⟩, .anonymous⟩⟩
local instance : Inhabited VDefEq :=
  ⟨⟨0, .sort .zero, .sort .zero, .sort (.succ .zero)⟩⟩

/- Reify one closed analyzer-produced equation as ordinary constructor
syntax so `type_tac` can audit it without reducing the nested analyzer in
every proof. -/
syntax "nestedComputedVDefEq%" term : term

elab_rules : term
  | `(nestedComputedVDefEq% $rule:term) => do
    let e ← Lean.Elab.Term.elabTerm rule (Lean.mkConst ``VDefEq)
    let e ← Lean.instantiateMVars e
    let value ← unsafe Lean.Meta.evalExpr VDefEq (Lean.mkConst ``VDefEq) e
    return Lean.toExpr value

/-! ## Certified dependency block -/

def semanticBoxType : VInductiveType where
  name := ``LeanBox
  uvars := 0
  type := nestedConstVType09A% LeanBox
  ctors := [⟨⟨0, nestedConstVType09A% LeanBox.wrap⟩, ``LeanBox.wrap⟩]

def semanticBoxDecl : VInductDecl where
  uvars := 0
  nparams := 1
  types := [semanticBoxType]

def semanticBoxChecked : semanticBoxDecl.Checked :=
  semanticBoxDecl.checked?.get (by native_decide)

def semanticBoxGeneration : semanticBoxDecl.GenerationChecked :=
  semanticBoxDecl.identityGeneration?.get (by native_decide)

def semanticBoxFamily : VConstVal := semanticBoxType.toVConstVal
def semanticBoxWrap : VConstVal := semanticBoxType.ctors[0]!

structure SemanticBoxShape : Prop where
  familyName : semanticBoxChecked.type.name = ``LeanBox
  resultLevel : semanticBoxChecked.resultLevel = .succ .zero
  noIndices : semanticBoxChecked.indices = []
  parameters : semanticBoxChecked.params.reverse = [.sort (.succ .zero)]
  constructors :
    semanticBoxGeneration.block.sourceType.ctors = [semanticBoxWrap]

theorem semanticBoxShape : SemanticBoxShape := by
  constructor <;> native_decide

theorem semanticBoxCheckedWF : semanticBoxChecked.WF VEnv.empty := by
  constructor
  · change VEnv.empty.OnTel 0 [] [.sort (.succ .zero)]
    exact ⟨⟨.succ (.succ .zero), VEnv.HasType.sort (by decide)⟩, trivial⟩
  · intro ctor hctor
    have hctor' := List.mem_singleton.1 hctor
    subst ctor
    constructor
    · rw [show semanticBoxDecl.uvars = 0 from rfl,
        semanticBoxShape.familyName,
        show semanticBoxDecl.nparams = 1 from rfl,
        semanticBoxShape.resultLevel, semanticBoxShape.noIndices,
        semanticBoxShape.parameters]
      change VInductDecl.fieldsWF 0 ``LeanBox 1 VEnv.empty
        (.succ .zero) [] [.sort (.succ .zero)] 0 [.bvar 0]
      constructor
      · exact .inr (.inr ⟨rfl, .succ .zero, by type_tac,
          .inr (VLevel.le_refl _)⟩)
      constructor
      · intro recursive
        simp [VInductDecl.isRecField] at recursive
        have impossible :
            (VExpr.bvar 0).appHead ≠
              VExpr.const ``LeanBox (VLevel.params 0) := by
          decide
        exact False.elim (impossible recursive.1.1.1)
      · trivial
    · rw [show semanticBoxDecl.uvars = 0 from rfl,
        show semanticBoxDecl.nparams = 1 from rfl,
        semanticBoxShape.resultLevel, semanticBoxShape.noIndices,
        semanticBoxShape.parameters]
      exact .nil

theorem semanticBoxGenerationWF :
    semanticBoxGeneration.WF VEnv.empty := by
  exact semanticBoxCheckedWF.identityGeneration .empty

def semanticBoxCertificate :
    semanticBoxDecl.GenerationCertificate VEnv.empty where
  generation := semanticBoxGeneration
  wf := semanticBoxGenerationWF

def semanticBoxAfter? : Option VEnv :=
  VEnv.empty.addInductCertified semanticBoxCertificate

theorem semanticBoxAfter_isSome : semanticBoxAfter?.isSome := by
  native_decide

def semanticBoxEnv : VEnv :=
  semanticBoxAfter?.get semanticBoxAfter_isSome

theorem semanticBoxSuccess :
    VEnv.empty.addInductCertified semanticBoxCertificate =
      some semanticBoxEnv := by
  change semanticBoxAfter? = some semanticBoxEnv
  exact (Option.some_get semanticBoxAfter_isSome).symm

def semanticBoxTransaction :
    CertifiedGenerationTransaction semanticBoxDecl VEnv.empty semanticBoxEnv where
  certificate := semanticBoxCertificate
  success := semanticBoxSuccess
  beforeWF := ⟨[], .empty⟩

theorem semanticBoxEnvWF : semanticBoxEnv.WF :=
  semanticBoxTransaction.afterWF

def semanticBoxTarget : NestedTargetBlock where
  nparams := 1
  families := [semanticBoxType]

theorem semanticBoxTargetWF : semanticBoxTarget.WF semanticBoxEnv where
  families := by
    intro family hfamily
    have familyEq : family = semanticBoxType := List.mem_singleton.1 hfamily
    subst family
    exact semanticBoxTransaction.facts.familyLookup
  ctors := by
    intro family hfamily constructor hconstructor
    have familyEq : family = semanticBoxType := List.mem_singleton.1 hfamily
    subst family
    have constructorEq : constructor = semanticBoxWrap :=
      List.mem_singleton.1 hconstructor
    subst constructor
    apply semanticBoxTransaction.facts.ctorLookup
    change semanticBoxWrap ∈ semanticBoxGeneration.block.sourceType.ctors
    rw [semanticBoxShape.constructors]
    simp

/-! ## Analyzer-produced nested block and restored inventory -/

def semanticTreeType : VInductiveType where
  name := ``LeanTree
  uvars := 0
  type := nestedConstVType09A% LeanTree
  ctors := [⟨⟨0, nestedConstVType09A% LeanTree.node⟩, ``LeanTree.node⟩]

def semanticTreeDecl : VInductDecl where
  uvars := 0
  nparams := 0
  types := [semanticTreeType]

def semanticTreeNested? : Option (NestedBlockChecked semanticTreeDecl) :=
  nestedBlockChecked? [semanticBoxTarget] semanticTreeDecl

theorem semanticTreeNested_isSome : semanticTreeNested?.isSome := by
  native_decide

def semanticTreeNested : NestedBlockChecked semanticTreeDecl :=
  semanticTreeNested?.get semanticTreeNested_isSome

theorem semanticTreeNested_produced :
    nestedBlockChecked? [semanticBoxTarget] semanticTreeDecl =
      some semanticTreeNested := by
  change semanticTreeNested? = some semanticTreeNested
  exact (Option.some_get semanticTreeNested_isSome).symm

def semanticTreeFamily : VConstVal := semanticTreeType.toVConstVal
def semanticTreeNode : VConstVal := semanticTreeType.ctors[0]!

theorem semanticTreeNodeName : semanticTreeNode.name = ``LeanTree.node := by
  native_decide

theorem semanticTreeSourceInventory :
    semanticTreeDecl.blockTypeConstants = [semanticTreeFamily] ∧
      semanticTreeDecl.blockConstructorConstants = [semanticTreeNode] := by
  constructor <;> native_decide

def semanticTreeRec : VConstVal :=
  ⟨⟨1, nestedConstVType09A% LeanTree.rec⟩, ``LeanTree.rec⟩

def semanticTreeRecOne : VConstVal :=
  ⟨⟨1, nestedConstVType09A% LeanTree.rec_1⟩, ``LeanTree.rec_1⟩

theorem semanticTreeRecursors_eq :
    semanticTreeNested.recursors = [semanticTreeRec, semanticTreeRecOne] := by
  native_decide

def semanticTreeNodeRule : VDefEq :=
  nestedComputedVDefEq% semanticTreeNested.generatedRules[0]!

def semanticTreeWrapRule : VDefEq :=
  nestedComputedVDefEq% semanticTreeNested.generatedRules[1]!

def semanticTreeRules : List VDefEq :=
  [semanticTreeNodeRule, semanticTreeWrapRule]

theorem semanticTreeRules_eq :
    semanticTreeNested.generatedRules = semanticTreeRules := by
  native_decide

/-- The restored rule inventory is the same two-equation inventory stored by
Lean for the actual nested declaration: the source constructor first, then
the copied dependency constructor. -/
theorem semanticTreeRuleMetadata :
    semanticTreeNodeRule.rhs = kernelRecRuleRhs% LeanTree.rec 0 ∧
      semanticTreeWrapRule.rhs = kernelRecRuleRhs% LeanTree.rec_1 0 := by
  constructor <;> rfl

/-- No auxiliary flattening name survives the restored public inventory. -/
theorem semanticTreeRestoredClean :
    semanticTreeNested.recursors.all
        (fun recursor => !recursor.type.hasAnyConst
          [leanAuxiliaryName, leanAuxiliaryConstructorName,
            .str leanAuxiliaryName "rec"]) = true ∧
      semanticTreeNested.generatedRules.all (fun rule =>
        !rule.lhs.hasAnyConst
            [leanAuxiliaryName, leanAuxiliaryConstructorName,
              .str leanAuxiliaryName "rec"] &&
          !rule.rhs.hasAnyConst
            [leanAuxiliaryName, leanAuxiliaryConstructorName,
              .str leanAuxiliaryName "rec"] &&
          !rule.type.hasAnyConst
            [leanAuxiliaryName, leanAuxiliaryConstructorName,
              .str leanAuxiliaryName "rec"]) = true := by
  native_decide

/-! ## Exact semantic phase environments -/

def semanticTreeTypeEnv : VEnv :=
  (semanticBoxEnv.addConst semanticTreeFamily.name
    semanticTreeFamily.toVConstant).get!

def semanticTreeCtorEnv : VEnv :=
  (semanticTreeTypeEnv.addConst semanticTreeNode.name
    semanticTreeNode.toVConstant).get!

def semanticTreeRecEnv : VEnv :=
  (semanticTreeCtorEnv.addConst semanticTreeRec.name
    semanticTreeRec.toVConstant).get!

def semanticTreeRecOneEnv : VEnv :=
  (semanticTreeRecEnv.addConst semanticTreeRecOne.name
    semanticTreeRecOne.toVConstant).get!

def semanticTreeRuleEnvOne : VEnv :=
  semanticTreeRecOneEnv.addDefEq semanticTreeNodeRule

def semanticTreeFinalEnv : VEnv :=
  semanticTreeRuleEnvOne.addDefEq semanticTreeWrapRule

theorem semanticTreeFamilyWF :
    semanticTreeFamily.toVConstant.WF semanticBoxEnv :=
  ⟨_, by type_tac⟩

theorem semanticTreeTypeEnv_eq :
    semanticBoxEnv.addConst semanticTreeFamily.name
        semanticTreeFamily.toVConstant =
      some semanticTreeTypeEnv := rfl

theorem semanticTreeTypeOrdered : semanticTreeTypeEnv.Ordered :=
  .const semanticBoxEnvWF.ordered semanticTreeFamilyWF
    semanticTreeTypeEnv_eq

theorem semanticTreeNodeWF :
    semanticTreeNode.toVConstant.WF semanticTreeTypeEnv := by
  have hBox : semanticTreeTypeEnv.constants ``LeanBox =
      some semanticBoxFamily.toVConstant := rfl
  have hTree : semanticTreeTypeEnv.constants ``LeanTree =
      some semanticTreeFamily.toVConstant := rfl
  exact ⟨_, by type_tac⟩

theorem semanticTreeCtorEnv_eq :
    semanticTreeTypeEnv.addConst semanticTreeNode.name
        semanticTreeNode.toVConstant =
      some semanticTreeCtorEnv := rfl

theorem semanticTreeCtorOrdered : semanticTreeCtorEnv.Ordered :=
  .const semanticTreeTypeOrdered semanticTreeNodeWF semanticTreeCtorEnv_eq

macro "semantic_tree_const_hyps" e:term : tactic => `(tactic| (
  have hBox : VEnv.constants $e ``LeanBox =
      some semanticBoxFamily.toVConstant := rfl
  have hWrap : VEnv.constants $e ``LeanBox.wrap =
      some semanticBoxWrap.toVConstant := rfl
  have hTree : VEnv.constants $e ``LeanTree =
      some semanticTreeFamily.toVConstant := rfl
  have hNode : VEnv.constants $e ``LeanTree.node =
      some semanticTreeNode.toVConstant := rfl))

set_option maxRecDepth 20000 in
theorem semanticTreeRecWF :
    semanticTreeRec.toVConstant.WF semanticTreeCtorEnv := by
  semantic_tree_const_hyps semanticTreeCtorEnv
  exact ⟨_, by type_tac⟩

theorem semanticTreeRecEnv_eq :
    semanticTreeCtorEnv.addConst semanticTreeRec.name
        semanticTreeRec.toVConstant =
      some semanticTreeRecEnv := rfl

theorem semanticTreeRecOrdered : semanticTreeRecEnv.Ordered :=
  .const semanticTreeCtorOrdered semanticTreeRecWF semanticTreeRecEnv_eq

set_option maxRecDepth 20000 in
theorem semanticTreeRecOneWF :
    semanticTreeRecOne.toVConstant.WF semanticTreeRecEnv := by
  semantic_tree_const_hyps semanticTreeRecEnv
  exact ⟨_, by type_tac⟩

theorem semanticTreeRecOneEnv_eq :
    semanticTreeRecEnv.addConst semanticTreeRecOne.name
        semanticTreeRecOne.toVConstant =
      some semanticTreeRecOneEnv := rfl

theorem semanticTreeRecOneOrdered : semanticTreeRecOneEnv.Ordered :=
  .const semanticTreeRecOrdered semanticTreeRecOneWF
    semanticTreeRecOneEnv_eq

macro "semantic_tree_rule_hyps" e:term : tactic => `(tactic| (
  semantic_tree_const_hyps $e
  have hRec : VEnv.constants $e ``LeanTree.rec =
      some semanticTreeRec.toVConstant := rfl
  have hRecOne : VEnv.constants $e ``LeanTree.rec_1 =
      some semanticTreeRecOne.toVConstant := rfl))

set_option maxRecDepth 30000 in
theorem semanticTreeNodeRuleWF :
    semanticTreeNodeRule.WF semanticTreeRecOneEnv := by
  constructor
  · semantic_tree_rule_hyps semanticTreeRecOneEnv
    type_tac
  · semantic_tree_rule_hyps semanticTreeRecOneEnv
    type_tac

set_option maxRecDepth 30000 in
theorem semanticTreeWrapRuleWF :
    semanticTreeWrapRule.WF semanticTreeRuleEnvOne := by
  constructor
  · semantic_tree_rule_hyps semanticTreeRuleEnvOne
    type_tac
  · semantic_tree_rule_hyps semanticTreeRuleEnvOne
    type_tac

/-! ## Semantic package and completed nested transaction -/

theorem semanticTreeTypesFold_eq :
    semanticTreeDecl.blockTypeConstants.foldlM
      (fun env constant => env.addConst constant.name
        constant.toVConstant) semanticBoxEnv =
      some semanticTreeTypeEnv := rfl

theorem semanticTreeCtorsFold_eq :
    semanticTreeDecl.blockConstructorConstants.foldlM
      (fun env constant => env.addConst constant.name
        constant.toVConstant) semanticTreeTypeEnv =
      some semanticTreeCtorEnv := rfl

theorem semanticTreeRecsFold_eq :
    semanticTreeNested.recursors.foldlM
      (fun env constant => env.addConst constant.name
        constant.toVConstant) semanticTreeCtorEnv =
      some semanticTreeRecOneEnv := by
  rw [semanticTreeRecursors_eq]
  rfl

theorem semanticTreeNestedWF : semanticTreeNested.WF semanticBoxEnv := by
  refine ⟨⟨semanticTreeFamilyWF, fun env' h => ?_⟩,
    fun {typeEnv} h => ?_,
    fun {typeEnv ctorEnv} hT hC => ?_,
    fun {typeEnv ctorEnv recEnv} hT hC hR => ?_⟩
  · cases Option.some.inj (semanticTreeTypeEnv_eq.symm.trans h)
    exact trivial
  · cases Option.some.inj (semanticTreeTypesFold_eq.symm.trans h)
    exact ⟨semanticTreeNodeWF, fun env' h' => by
      cases Option.some.inj (semanticTreeCtorEnv_eq.symm.trans h')
      exact trivial⟩
  · cases Option.some.inj (semanticTreeTypesFold_eq.symm.trans hT)
    cases Option.some.inj (semanticTreeCtorsFold_eq.symm.trans hC)
    rw [semanticTreeRecursors_eq]
    exact ⟨semanticTreeRecWF, fun env' h' => by
      cases Option.some.inj (semanticTreeRecEnv_eq.symm.trans h')
      exact ⟨semanticTreeRecOneWF, fun env'' h'' => by
        cases Option.some.inj (semanticTreeRecOneEnv_eq.symm.trans h'')
        exact trivial⟩⟩
  · cases Option.some.inj (semanticTreeTypesFold_eq.symm.trans hT)
    cases Option.some.inj (semanticTreeCtorsFold_eq.symm.trans hC)
    cases Option.some.inj (semanticTreeRecsFold_eq.symm.trans hR)
    rw [semanticTreeRules_eq]
    exact ⟨semanticTreeNodeRuleWF, semanticTreeWrapRuleWF, trivial⟩

def semanticTreeAfter? : Option VEnv :=
  semanticBoxEnv.addInductNested semanticTreeNested

theorem semanticTreeAfter_isSome : semanticTreeAfter?.isSome := by
  native_decide

def semanticTreeEnv : VEnv :=
  semanticTreeAfter?.get semanticTreeAfter_isSome

theorem semanticTreeSuccess :
    semanticBoxEnv.addInductNested semanticTreeNested =
      some semanticTreeEnv := by
  change semanticTreeAfter? = some semanticTreeEnv
  exact (Option.some_get semanticTreeAfter_isSome).symm

def semanticTreeCertificate :
    semanticTreeDecl.NestedBlockCertificate semanticBoxEnv
      semanticTreeEnv where
  nested := semanticTreeNested
  semantic := semanticTreeNestedWF
  success := semanticTreeSuccess
  beforeWF := semanticBoxEnvWF

theorem semanticTreeEnvWF : semanticTreeEnv.WF :=
  semanticTreeCertificate.afterWF

/-- The successful public transaction exposes every source/restored phase
through the certificate while excluding analyzer auxiliaries. -/
structure SemanticTreeTransactionFacts : Prop where
  analyzerProduced :
    nestedBlockChecked? [semanticBoxTarget] semanticTreeDecl =
      some semanticTreeNested
  sourceFamily :
    semanticTreeEnv.constants ``LeanTree =
      some semanticTreeFamily.toVConstant
  sourceConstructor :
    semanticTreeEnv.constants ``LeanTree.node =
      some semanticTreeNode.toVConstant
  primaryRecursor :
    semanticTreeEnv.constants ``LeanTree.rec =
      some semanticTreeRec.toVConstant
  dependencyRecursor :
    semanticTreeEnv.constants ``LeanTree.rec_1 =
      some semanticTreeRecOne.toVConstant
  sourceRule : semanticTreeEnv.defeqs semanticTreeNodeRule
  dependencyRule : semanticTreeEnv.defeqs semanticTreeWrapRule
  restoredInventory :
    semanticTreeNested.recursors = [semanticTreeRec, semanticTreeRecOne] ∧
      semanticTreeNested.generatedRules = semanticTreeRules
  restoredClean :
    semanticTreeNested.recursors.all
        (fun recursor => !recursor.type.hasAnyConst
          [leanAuxiliaryName, leanAuxiliaryConstructorName,
            .str leanAuxiliaryName "rec"]) = true ∧
      semanticTreeNested.generatedRules.all (fun rule =>
        !rule.lhs.hasAnyConst
            [leanAuxiliaryName, leanAuxiliaryConstructorName,
              .str leanAuxiliaryName "rec"] &&
          !rule.rhs.hasAnyConst
            [leanAuxiliaryName, leanAuxiliaryConstructorName,
              .str leanAuxiliaryName "rec"] &&
          !rule.type.hasAnyConst
            [leanAuxiliaryName, leanAuxiliaryConstructorName,
              .str leanAuxiliaryName "rec"]) = true

theorem semanticTreeTransactionFacts : SemanticTreeTransactionFacts := by
  refine ⟨semanticTreeNested_produced, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨semanticTreeRecursors_eq, semanticTreeRules_eq⟩,
    semanticTreeRestoredClean⟩
  · have lookup := semanticTreeCertificate.familyLookup
      (family := semanticTreeType) (by simp [semanticTreeDecl])
    simpa [semanticTreeFamily, semanticTreeType] using lookup
  · have lookup := semanticTreeCertificate.constructorLookup
      (family := semanticTreeType) (constructor := semanticTreeNode)
      (by simp [semanticTreeDecl]) (by
        simp [semanticTreeType, semanticTreeNode])
    simpa only [semanticTreeNodeName] using lookup
  · have member :
        semanticTreeRec ∈ semanticTreeCertificate.nested.recursors := by
      change semanticTreeRec ∈ semanticTreeNested.recursors
      rw [semanticTreeRecursors_eq]
      simp
    have lookup := semanticTreeCertificate.recursorLookup member
    simpa [semanticTreeRec] using lookup
  · have member :
        semanticTreeRecOne ∈ semanticTreeCertificate.nested.recursors := by
      change semanticTreeRecOne ∈ semanticTreeNested.recursors
      rw [semanticTreeRecursors_eq]
      simp
    have lookup := semanticTreeCertificate.recursorLookup member
    simpa [semanticTreeRecOne] using lookup
  · apply semanticTreeCertificate.ruleRegistered
    change semanticTreeNodeRule ∈ semanticTreeNested.generatedRules
    rw [semanticTreeRules_eq]
    simp [semanticTreeRules]
  · apply semanticTreeCertificate.ruleRegistered
    change semanticTreeWrapRule ∈ semanticTreeNested.generatedRules
    rw [semanticTreeRules_eq]
    simp [semanticTreeRules]

end Ix.Tc.NestedRecursiveFixture
