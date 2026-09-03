import Ix.Tc.Verify.Inductive.NestedRecursorPattern

/-!
# Soundness of the two restored nested iota equations

Both physical patterns retain their exact registered closed RHS tower.  The
proofs below invert a production-shaped match, transport its typed spines to
the corresponding restored equation telescope, apply the registered defeq,
and beta-collapse both towers.  The dependency rule additionally uses its
single pattern check to identify the physical `LeanBox` parameter with the
restored specialization `LeanTree`.
-/

namespace Ix.Tc.NestedRecursiveFixture

open Lean4Lean

/-! ## Shared concrete telescope shapes -/

private def commonBinders : List VExpr :=
  VExpr.telN 4 semanticTreeRec.type

@[simp] private theorem commonBindersLength : commonBinders.length = 4 := by
  native_decide

private theorem recOneCommonBinders :
    VExpr.telN 4 semanticTreeRecOne.type = commonBinders := by
  native_decide

private theorem nodeRuleCommonBinders :
    VExpr.telN 4 semanticTreeNodeRule.type = commonBinders := by
  native_decide

private theorem wrapRuleCommonBinders :
    VExpr.telN 4 semanticTreeWrapRule.type = commonBinders := by
  native_decide

private def nodeRuleBinders : List VExpr :=
  VExpr.telN 5 semanticTreeNodeRule.type

private def wrapRuleBinders : List VExpr :=
  VExpr.telN 5 semanticTreeWrapRule.type

private def nodeRuleLhsBody : VExpr :=
  .app
    (VExpr.appN (.const ``LeanTree.rec [.param 0])
      [.bvar 4, .bvar 3, .bvar 2, .bvar 1])
    (.app (.const ``LeanTree.node []) (.bvar 0))

private def wrapRuleLhsBody : VExpr :=
  .app
    (VExpr.appN (.const ``LeanTree.rec_1 [.param 0])
      [.bvar 4, .bvar 3, .bvar 2, .bvar 1])
    (VExpr.appN (.const ``LeanBox.wrap [])
      [.const ``LeanTree [], .bvar 0])

private theorem nodeRuleLhsShape :
    semanticTreeNodeRule.lhs =
      VExpr.lamN nodeRuleBinders nodeRuleLhsBody := by
  native_decide

private theorem wrapRuleLhsShape :
    semanticTreeWrapRule.lhs =
      VExpr.lamN wrapRuleBinders wrapRuleLhsBody := by
  native_decide

@[simp] private theorem nodeRuleBindersLength :
    nodeRuleBinders.length = 5 := by native_decide

@[simp] private theorem wrapRuleBindersLength :
    wrapRuleBinders.length = 5 := by native_decide

private theorem nodeRecTypeCommon (levels : List VLevel) :
    semanticTreeRec.type.instL levels =
      VExpr.forallN (commonBinders.map (VExpr.instL levels))
        (VExpr.dropN 4 (semanticTreeRec.type.instL levels)) := by
  rw [← VExpr.forallN_telN_dropN 4
    (semanticTreeRec.type.instL levels)]
  congr 1

private theorem recOneTypeCommon (levels : List VLevel) :
    semanticTreeRecOne.type.instL levels =
      VExpr.forallN (commonBinders.map (VExpr.instL levels))
        (VExpr.dropN 4 (semanticTreeRecOne.type.instL levels)) := by
  rw [← VExpr.forallN_telN_dropN 4
    (semanticTreeRecOne.type.instL levels)]
  congr 1

private theorem nodeRuleTypeCommon (levels : List VLevel) :
    semanticTreeNodeRule.type.instL levels =
      VExpr.forallN (commonBinders.map (VExpr.instL levels))
        (VExpr.dropN 4 (semanticTreeNodeRule.type.instL levels)) := by
  rw [← VExpr.forallN_telN_dropN 4
    (semanticTreeNodeRule.type.instL levels)]
  congr 1

private theorem wrapRuleTypeCommon (levels : List VLevel) :
    semanticTreeWrapRule.type.instL levels =
      VExpr.forallN (commonBinders.map (VExpr.instL levels))
        (VExpr.dropN 4 (semanticTreeWrapRule.type.instL levels)) := by
  rw [← VExpr.forallN_telN_dropN 4
    (semanticTreeWrapRule.type.instL levels)]
  congr 1

private def nodeEquationFieldType (u : VLevel)
    (motiveTree motiveBox nodeMinor wrapMinor : VExpr) : VExpr :=
  VExpr.instRev
    (VExpr.dropN 4 (semanticTreeNodeRule.type.instL [u]))
    [motiveTree, motiveBox, nodeMinor, wrapMinor]

private def nodeConstructorFieldType : VExpr :=
  semanticTreeNode.type

private theorem nodeConstructorTypeInstLNil :
    semanticTreeNode.type.instL [] = semanticTreeNode.type := by
  native_decide

private theorem nodeFieldBindersEq (u : VLevel)
    (motiveTree motiveBox nodeMinor wrapMinor : VExpr) :
    VExpr.telN 1
        (nodeEquationFieldType u motiveTree motiveBox nodeMinor wrapMinor) =
      VExpr.telN 1 nodeConstructorFieldType := by
  rfl

@[simp] private theorem instRevApp (function argument : VExpr)
    (arguments : List VExpr) :
    VExpr.instRev (.app function argument) arguments =
      .app (VExpr.instRev function arguments)
        (VExpr.instRev argument arguments) := by
  simpa [VExpr.appN] using
    VExpr.instRev_appN arguments function [argument]

@[simp] private theorem instRevConst (name : Lean.Name)
    (levels : List VLevel) (arguments : List VExpr) :
    VExpr.instRev (.const name levels) arguments = .const name levels :=
  VExpr.instRev_closedN arguments trivial

private theorem nodeLhsBodyOpen (u : VLevel)
    (motiveTree motiveBox nodeMinor wrapMinor field : VExpr) :
    VExpr.instRev (nodeRuleLhsBody.instL [u])
        [motiveTree, motiveBox, nodeMinor, wrapMinor, field] =
      .app
        (VExpr.appN (.const ``LeanTree.rec [u])
          [motiveTree, motiveBox, nodeMinor, wrapMinor])
        (.app (.const ``LeanTree.node []) field) := by
  let arguments :=
    [motiveTree, motiveBox, nodeMinor, wrapMinor, field]
  have hmotiveTree : VExpr.instRev (.bvar 4) arguments = motiveTree := by
    simpa [arguments] using
      VExpr.instRev_bvar_at arguments 0 (by simp [arguments])
  have hmotiveBox : VExpr.instRev (.bvar 3) arguments = motiveBox := by
    simpa [arguments] using
      VExpr.instRev_bvar_at arguments 1 (by simp [arguments])
  have hnodeMinor : VExpr.instRev (.bvar 2) arguments = nodeMinor := by
    simpa [arguments] using
      VExpr.instRev_bvar_at arguments 2 (by simp [arguments])
  have hwrapMinor : VExpr.instRev (.bvar 1) arguments = wrapMinor := by
    simpa [arguments] using
      VExpr.instRev_bvar_at arguments 3 (by simp [arguments])
  have hfield : VExpr.instRev (.bvar 0) arguments = field := by
    simpa [arguments] using
      VExpr.instRev_bvar_at arguments 4 (by simp [arguments])
  change VExpr.instRev (nodeRuleLhsBody.instL [u]) arguments = _
  simp [nodeRuleLhsBody, VExpr.instL_appN, VExpr.instRev_appN,
    VExpr.instL, VLevel.inst, hmotiveTree, hmotiveBox, hnodeMinor,
    hwrapMinor, hfield]

private def wrapEquationFieldType (u : VLevel)
    (motiveTree motiveBox nodeMinor wrapMinor : VExpr) : VExpr :=
  VExpr.instRev
    (VExpr.dropN 4 (semanticTreeWrapRule.type.instL [u]))
    [motiveTree, motiveBox, nodeMinor, wrapMinor]

private def wrapConstructorFieldType : VExpr :=
  (VExpr.dropN 1 semanticBoxWrap.type).inst (.const ``LeanTree [])

private theorem wrapConstructorTypeInstLNil :
    semanticBoxWrap.type.instL [] = semanticBoxWrap.type := by
  native_decide

private theorem treeFamilyTypeInstLNil :
    semanticTreeFamily.type.instL [] = semanticTreeFamily.type := by
  native_decide

private theorem treeFamilyTypeShape :
    semanticTreeFamily.type = .sort (.succ .zero) := by
  native_decide

private theorem wrapConstructorTypeParameter :
    semanticBoxWrap.type =
      .forallE (.sort (.succ .zero))
        (VExpr.dropN 1 semanticBoxWrap.type) := by
  rw [← VExpr.forallN_telN_dropN 1 semanticBoxWrap.type]
  congr 1

private theorem wrapFieldBindersEq (u : VLevel)
    (motiveTree motiveBox nodeMinor wrapMinor : VExpr) :
    VExpr.telN 1
        (wrapEquationFieldType u motiveTree motiveBox nodeMinor wrapMinor) =
      VExpr.telN 1 wrapConstructorFieldType := by
  rfl

private theorem semanticTreeWrapLookup :
    semanticTreeEnv.constants ``LeanBox.wrap =
      some semanticBoxWrap.toVConstant := by
  apply semanticTreeCertificate.envLE.constants
  have hmember :
      semanticBoxWrap ∈ semanticBoxGeneration.block.sourceType.ctors := by
    rw [semanticBoxShape.constructors]
    simp
  have hlookup := semanticBoxTransaction.facts.ctorLookup hmember
  simpa [semanticBoxWrap, semanticBoxType] using hlookup

private theorem wrapLhsBodyOpen (u : VLevel)
    (motiveTree motiveBox nodeMinor wrapMinor field : VExpr) :
    VExpr.instRev (wrapRuleLhsBody.instL [u])
        [motiveTree, motiveBox, nodeMinor, wrapMinor, field] =
      .app
        (VExpr.appN (.const ``LeanTree.rec_1 [u])
          [motiveTree, motiveBox, nodeMinor, wrapMinor])
        (VExpr.appN (.const ``LeanBox.wrap [])
          [.const ``LeanTree [], field]) := by
  let arguments :=
    [motiveTree, motiveBox, nodeMinor, wrapMinor, field]
  have hmotiveTree : VExpr.instRev (.bvar 4) arguments = motiveTree := by
    simpa [arguments] using
      VExpr.instRev_bvar_at arguments 0 (by simp [arguments])
  have hmotiveBox : VExpr.instRev (.bvar 3) arguments = motiveBox := by
    simpa [arguments] using
      VExpr.instRev_bvar_at arguments 1 (by simp [arguments])
  have hnodeMinor : VExpr.instRev (.bvar 2) arguments = nodeMinor := by
    simpa [arguments] using
      VExpr.instRev_bvar_at arguments 2 (by simp [arguments])
  have hwrapMinor : VExpr.instRev (.bvar 1) arguments = wrapMinor := by
    simpa [arguments] using
      VExpr.instRev_bvar_at arguments 3 (by simp [arguments])
  have hfield : VExpr.instRev (.bvar 0) arguments = field := by
    simpa [arguments] using
      VExpr.instRev_bvar_at arguments 4 (by simp [arguments])
  change VExpr.instRev (wrapRuleLhsBody.instL [u]) arguments = _
  simp [wrapRuleLhsBody, VExpr.instL_appN, VExpr.instRev_appN,
    VExpr.instL, VLevel.inst, hmotiveTree, hmotiveBox, hnodeMinor,
    hwrapMinor, hfield]

/-! ## Stored `LeanTree.node` rule -/

theorem treeNodePatternSound : treeNodePattern.Sound semanticTreeEnv := by
  unfold RecursorRulePattern.Sound
  simp [treeNodePattern]
  intro future hfuture hfutureWF uvars Gamma matched levels captures A
    hGamma hmatches htype _hchecks
  change Pattern.Matches
      (RecursorIotaPattern ``LeanTree.rec 4 ``LeanTree.node 1)
      matched levels captures at hmatches
  obtain ⟨recursorArguments, constructorLevels, constructorArguments,
    hrecursorLength, hconstructorLength, hmatched, hrecCaptures,
    hconstructorCaptures⟩ :=
    RecursorIotaPattern.matches_spines_full hmatches

  rcases recursorArguments with _ | ⟨motiveTree, rec1⟩
  · simp at hrecursorLength
  rcases rec1 with _ | ⟨motiveBox, rec2⟩
  · simp at hrecursorLength
  rcases rec2 with _ | ⟨nodeMinor, rec3⟩
  · simp at hrecursorLength
  rcases rec3 with _ | ⟨wrapMinor, recTail⟩
  · simp at hrecursorLength
  have hrecTail : recTail = [] :=
    List.eq_nil_of_length_eq_zero (by simpa using hrecursorLength)
  subst recTail

  rcases constructorArguments with _ | ⟨field, ctorTail⟩
  · simp at hconstructorLength
  have hctorTail : ctorTail = [] :=
    List.eq_nil_of_length_eq_zero (by simpa using hconstructorLength)
  subst ctorTail

  have hcapMotiveTree := hrecCaptures ⟨0, by omega⟩
  have hcapMotiveBox := hrecCaptures ⟨1, by omega⟩
  have hcapNodeMinor := hrecCaptures ⟨2, by omega⟩
  have hcapWrapMinor := hrecCaptures ⟨3, by omega⟩
  have hcapField := hconstructorCaptures ⟨0, by omega⟩
  simp at hcapMotiveTree hcapMotiveBox hcapNodeMinor hcapWrapMinor hcapField

  rw [hmatched] at htype
  obtain ⟨majorDomain, majorBody, hrecursorApplied,
    hconstructorApplied⟩ := htype.app_inv hfutureWF.ordered hGamma

  obtain ⟨recursorHeadType, hrecursorHeadTyped⟩ :=
    Lean4Lean.VEnv.HasType.appN_head hfutureWF hGamma hrecursorApplied
  obtain ⟨recursorConstant, hrecursorLookup, hlevelsWF, hlevelsArity⟩ :=
    hrecursorHeadTyped.const_inv hfutureWF.ordered hGamma
  have hcertifiedRecursorLookup :=
    hfuture.constants semanticTreeTransactionFacts.primaryRecursor
  have hrecursorConstant :
      recursorConstant = semanticTreeRec.toVConstant :=
    Option.some.inj
      (hrecursorLookup.symm.trans hcertifiedRecursorLookup)
  subst recursorConstant
  have hlevelsLength : levels.length = 1 := by
    calc
      levels.length = semanticTreeRec.toVConstant.uvars := hlevelsArity
      _ = 1 := rfl
  rcases levels with _ | ⟨u, levelTail⟩
  · simp at hlevelsLength
  have hlevelTail : levelTail = [] :=
    List.eq_nil_of_length_eq_zero (by simpa using hlevelsLength)
  subst levelTail

  obtain ⟨constructorHeadType, hconstructorHeadTyped⟩ :=
    Lean4Lean.VEnv.HasType.appN_head hfutureWF hGamma hconstructorApplied
  obtain ⟨constructorConstant, hconstructorLookup, constructorLevelsWF,
    hconstructorLevelsArity⟩ :=
    hconstructorHeadTyped.const_inv hfutureWF.ordered hGamma
  have hcertifiedConstructorLookup :=
    hfuture.constants semanticTreeTransactionFacts.sourceConstructor
  have hconstructorConstant :
      constructorConstant = semanticTreeNode.toVConstant :=
    Option.some.inj
      (hconstructorLookup.symm.trans hcertifiedConstructorLookup)
  subst constructorConstant
  have hconstructorLevelsLength : constructorLevels.length = 0 := by
    calc
      constructorLevels.length = semanticTreeNode.toVConstant.uvars :=
        hconstructorLevelsArity
      _ = 0 := rfl
  have hconstructorLevels : constructorLevels = [] :=
    List.eq_nil_of_length_eq_zero hconstructorLevelsLength
  subst constructorLevels

  have hequation : future.IsDefEq uvars Gamma
      (semanticTreeNodeRule.lhs.instL [u])
      (semanticTreeNodeRule.rhs.instL [u])
      (semanticTreeNodeRule.type.instL [u]) :=
    .extra (hfuture.defeqs semanticTreeTransactionFacts.sourceRule)
      hlevelsWF (by rfl)

  have hrecursorConstantTyped : future.HasType uvars Gamma
      (.const ``LeanTree.rec [u]) (semanticTreeRec.type.instL [u]) := by
    simpa using (Lean4Lean.VEnv.HasType.const (Γ := Gamma)
      hcertifiedRecursorLookup hlevelsWF hlevelsArity)
  have hrecursorCommonType : future.HasType uvars Gamma
      (.const ``LeanTree.rec [u])
      (VExpr.forallN (commonBinders.map (VExpr.instL [u]))
        (VExpr.dropN 4 (semanticTreeRec.type.instL [u]))) := by
    rw [← nodeRecTypeCommon]
    exact hrecursorConstantTyped
  have hequationLhsCommonType : future.HasType uvars Gamma
      (semanticTreeNodeRule.lhs.instL [u])
      (VExpr.forallN (commonBinders.map (VExpr.instL [u]))
        (VExpr.dropN 4 (semanticTreeNodeRule.type.instL [u]))) := by
    rw [← nodeRuleTypeCommon]
    exact hequation.hasType.1
  have hcommonLength :
      [motiveTree, motiveBox, nodeMinor, wrapMinor].length =
        (commonBinders.map (VExpr.instL [u])).length := by
    simpa only [List.length_cons, List.length_nil, List.length_map] using
      commonBindersLength.symm
  have hequationLhsCommonApplied : future.HasType uvars Gamma
      (VExpr.appN (semanticTreeNodeRule.lhs.instL [u])
        [motiveTree, motiveBox, nodeMinor, wrapMinor])
      (nodeEquationFieldType u motiveTree motiveBox nodeMinor wrapMinor) :=
    Lean4Lean.VEnv.HasType.transfer_appN_telescope_instRev
      hfutureWF hGamma hcommonLength hrecursorApplied
      hrecursorCommonType hequationLhsCommonType

  have hconstructorConstantTyped : future.HasType uvars Gamma
      (.const ``LeanTree.node []) nodeConstructorFieldType := by
    have htyped := Lean4Lean.VEnv.HasType.const (Γ := Gamma)
      hcertifiedConstructorLookup constructorLevelsWF
        hconstructorLevelsArity
    rw [nodeConstructorTypeInstLNil] at htyped
    exact htyped
  have hconstructorFieldHead : future.HasType uvars Gamma
      (.const ``LeanTree.node [])
      (VExpr.forallN (VExpr.telN 1 nodeConstructorFieldType)
        (VExpr.dropN 1 nodeConstructorFieldType)) := by
    rw [← VExpr.forallN_telN_dropN 1 nodeConstructorFieldType]
    exact hconstructorConstantTyped
  have hequationFieldHead : future.HasType uvars Gamma
      (VExpr.appN (semanticTreeNodeRule.lhs.instL [u])
        [motiveTree, motiveBox, nodeMinor, wrapMinor])
      (VExpr.forallN
        (VExpr.telN 1
          (nodeEquationFieldType u motiveTree motiveBox nodeMinor wrapMinor))
        (VExpr.dropN 1
          (nodeEquationFieldType u motiveTree motiveBox nodeMinor
            wrapMinor))) := by
    rw [← VExpr.forallN_telN_dropN 1
      (nodeEquationFieldType u motiveTree motiveBox nodeMinor wrapMinor)]
    exact hequationLhsCommonApplied
  have hconstructorFieldHead' : future.HasType uvars Gamma
      (.const ``LeanTree.node [])
      (VExpr.forallN
        (VExpr.telN 1
          (nodeEquationFieldType u motiveTree motiveBox nodeMinor wrapMinor))
        (VExpr.dropN 1 nodeConstructorFieldType)) := by
    rw [nodeFieldBindersEq]
    exact hconstructorFieldHead
  have hfieldLength :
      [field].length =
        (VExpr.telN 1
          (nodeEquationFieldType u motiveTree motiveBox nodeMinor wrapMinor)).length := by
    rw [nodeFieldBindersEq]
    rfl
  have hequationLhsFieldsApplied :=
    Lean4Lean.VEnv.HasType.transfer_appN_telescope_instRev
      hfutureWF hGamma hfieldLength hconstructorApplied
      hconstructorFieldHead' hequationFieldHead
  have hequationLhsApplied : future.HasType uvars Gamma
      (VExpr.appN (semanticTreeNodeRule.lhs.instL [u])
        [motiveTree, motiveBox, nodeMinor, wrapMinor, field])
      (VExpr.instRev
        (VExpr.dropN 1
          (nodeEquationFieldType u motiveTree motiveBox nodeMinor wrapMinor))
        [field]) := by
    rw [show [motiveTree, motiveBox, nodeMinor, wrapMinor, field] =
      [motiveTree, motiveBox, nodeMinor, wrapMinor] ++ [field] by rfl,
      VExpr.appN_append]
    exact hequationLhsFieldsApplied
  have hequationApplied :=
    Lean4Lean.VEnv.IsDefEq.appN_same hfutureWF hGamma hequation
      hequationLhsApplied

  have hequationLhsApplied' := hequationLhsApplied
  rw [nodeRuleLhsShape, VExpr.instL_lamN] at hequationLhsApplied'
  have hruleArgsLength :
      [motiveTree, motiveBox, nodeMinor, wrapMinor, field].length =
        (nodeRuleBinders.map (VExpr.instL [u])).length := by
    simpa only [List.length_cons, List.length_nil, List.length_map] using
      nodeRuleBindersLength.symm
  have hlhsBeta := Lean4Lean.VEnv.HasType.lamN_appN_beta
    hfutureWF hGamma hruleArgsLength hequationLhsApplied'
  rw [nodeLhsBodyOpen] at hlhsBeta
  have hlhsBeta' : future.IsDefEqU uvars Gamma
      (VExpr.appN (semanticTreeNodeRule.lhs.instL [u])
        [motiveTree, motiveBox, nodeMinor, wrapMinor, field])
      (.app
        (VExpr.appN (.const ``LeanTree.rec [u])
          [motiveTree, motiveBox, nodeMinor, wrapMinor])
        (.app (.const ``LeanTree.node []) field)) := by
    rw [nodeRuleLhsShape, VExpr.instL_lamN]
    exact hlhsBeta

  have hgenerated :=
    hlhsBeta'.symm.trans hfutureWF hGamma hequationApplied
  rw [hmatched]
  change future.IsDefEqU uvars Gamma
    (.app
      (VExpr.appN (.const ``LeanTree.rec [u])
        [motiveTree, motiveBox, nodeMinor, wrapMinor])
      (.app (.const ``LeanTree.node []) field))
    (treeNodePattern.rhs.apply [u] captures)
  rw [treeNodePattern_rhs_apply]
  simpa [hcapMotiveTree, hcapMotiveBox, hcapNodeMinor, hcapWrapMinor,
    hcapField] using hgenerated

/-! ## Stored `LeanBox.wrap` dependency rule -/

theorem treeWrapPatternSound : treeWrapPattern.Sound semanticTreeEnv := by
  unfold RecursorRulePattern.Sound
  simp [treeWrapPattern]
  intro future hfuture hfutureWF uvars Gamma matched levels captures A
    hGamma hmatches htype hchecks
  change Pattern.Matches
      (RecursorIotaPattern ``LeanTree.rec_1 4 ``LeanBox.wrap 2)
      matched levels captures at hmatches
  obtain ⟨recursorArguments, constructorLevels, constructorArguments,
    hrecursorLength, hconstructorLength, hmatched, hrecCaptures,
    hconstructorCaptures⟩ :=
    RecursorIotaPattern.matches_spines_full hmatches

  rcases recursorArguments with _ | ⟨motiveTree, rec1⟩
  · simp at hrecursorLength
  rcases rec1 with _ | ⟨motiveBox, rec2⟩
  · simp at hrecursorLength
  rcases rec2 with _ | ⟨nodeMinor, rec3⟩
  · simp at hrecursorLength
  rcases rec3 with _ | ⟨wrapMinor, recTail⟩
  · simp at hrecursorLength
  have hrecTail : recTail = [] :=
    List.eq_nil_of_length_eq_zero (by simpa using hrecursorLength)
  subst recTail

  rcases constructorArguments with _ | ⟨constructorAlpha, ctor1⟩
  · simp at hconstructorLength
  rcases ctor1 with _ | ⟨field, ctorTail⟩
  · simp at hconstructorLength
  have hctorTail : ctorTail = [] :=
    List.eq_nil_of_length_eq_zero (by simpa using hconstructorLength)
  subst ctorTail

  have hcapMotiveTree := hrecCaptures ⟨0, by omega⟩
  have hcapMotiveBox := hrecCaptures ⟨1, by omega⟩
  have hcapNodeMinor := hrecCaptures ⟨2, by omega⟩
  have hcapWrapMinor := hrecCaptures ⟨3, by omega⟩
  have hcapConstructorAlpha := hconstructorCaptures ⟨0, by omega⟩
  have hcapField := hconstructorCaptures ⟨1, by omega⟩
  simp at hcapMotiveTree hcapMotiveBox hcapNodeMinor hcapWrapMinor
  simp at hcapConstructorAlpha hcapField

  have hparameterEq : future.IsDefEqU uvars Gamma
      constructorAlpha (.const ``LeanTree []) := by
    have hchecked := treeWrapPattern_checks_ok
      (future.IsDefEqU uvars Gamma) levels captures hchecks
    rw [hcapConstructorAlpha]
    simpa using hchecked

  rw [hmatched] at htype
  obtain ⟨majorDomain, majorBody, hrecursorApplied,
    hconstructorApplied⟩ := htype.app_inv hfutureWF.ordered hGamma

  obtain ⟨recursorHeadType, hrecursorHeadTyped⟩ :=
    Lean4Lean.VEnv.HasType.appN_head hfutureWF hGamma hrecursorApplied
  obtain ⟨recursorConstant, hrecursorLookup, hlevelsWF, hlevelsArity⟩ :=
    hrecursorHeadTyped.const_inv hfutureWF.ordered hGamma
  have hcertifiedRecursorLookup :=
    hfuture.constants semanticTreeTransactionFacts.dependencyRecursor
  have hrecursorConstant :
      recursorConstant = semanticTreeRecOne.toVConstant :=
    Option.some.inj
      (hrecursorLookup.symm.trans hcertifiedRecursorLookup)
  subst recursorConstant
  have hlevelsLength : levels.length = 1 := by
    calc
      levels.length = semanticTreeRecOne.toVConstant.uvars := hlevelsArity
      _ = 1 := rfl
  rcases levels with _ | ⟨u, levelTail⟩
  · simp at hlevelsLength
  have hlevelTail : levelTail = [] :=
    List.eq_nil_of_length_eq_zero (by simpa using hlevelsLength)
  subst levelTail

  obtain ⟨constructorHeadType, hconstructorHeadTyped⟩ :=
    Lean4Lean.VEnv.HasType.appN_head hfutureWF hGamma hconstructorApplied
  obtain ⟨constructorConstant, hconstructorLookup, constructorLevelsWF,
    hconstructorLevelsArity⟩ :=
    hconstructorHeadTyped.const_inv hfutureWF.ordered hGamma
  have hcertifiedConstructorLookup :=
    hfuture.constants semanticTreeWrapLookup
  have hconstructorConstant :
      constructorConstant = semanticBoxWrap.toVConstant :=
    Option.some.inj
      (hconstructorLookup.symm.trans hcertifiedConstructorLookup)
  subst constructorConstant
  have hconstructorLevelsLength : constructorLevels.length = 0 := by
    calc
      constructorLevels.length = semanticBoxWrap.toVConstant.uvars :=
        hconstructorLevelsArity
      _ = 0 := rfl
  have hconstructorLevels : constructorLevels = [] :=
    List.eq_nil_of_length_eq_zero hconstructorLevelsLength
  subst constructorLevels

  have hrecursorConstantTyped : future.HasType uvars Gamma
      (.const ``LeanTree.rec_1 [u])
      (semanticTreeRecOne.type.instL [u]) := by
    simpa using (Lean4Lean.VEnv.HasType.const (Γ := Gamma)
      hcertifiedRecursorLookup hlevelsWF hlevelsArity)
  have hconstructorConstantTyped : future.HasType uvars Gamma
      (.const ``LeanBox.wrap []) semanticBoxWrap.type := by
    have htyped := Lean4Lean.VEnv.HasType.const (Γ := Gamma)
      hcertifiedConstructorLookup constructorLevelsWF
        hconstructorLevelsArity
    rw [wrapConstructorTypeInstLNil] at htyped
    exact htyped
  have hconstructorParameterHead : future.HasType uvars Gamma
      (.const ``LeanBox.wrap [])
      (.forallE (.sort (.succ .zero))
        (VExpr.dropN 1 semanticBoxWrap.type)) := by
    rw [← wrapConstructorTypeParameter]
    exact hconstructorConstantTyped
  have hconstructorAppliedSplit : future.HasType uvars Gamma
      (VExpr.appN (.const ``LeanBox.wrap [])
        ([constructorAlpha] ++ [field])) majorDomain := by
    simpa using hconstructorApplied
  obtain ⟨constructorParameterResult, hconstructorParameterApplied⟩ :=
    Lean4Lean.VEnv.HasType.appN_prefix hfutureWF hGamma
      (prefixArgs := [constructorAlpha]) (suffixArgs := [field])
      hconstructorAppliedSplit
  have hconstructorAlpha : future.HasType uvars Gamma constructorAlpha
      (.sort (.succ .zero)) :=
    Lean4Lean.VEnv.HasType.app_argument_of_head hfutureWF hGamma
      hconstructorParameterApplied hconstructorParameterHead
  have hparameterAtConstructor : future.IsDefEq uvars Gamma
      constructorAlpha (.const ``LeanTree []) (.sort (.succ .zero)) :=
    hparameterEq.of_l hfutureWF hGamma hconstructorAlpha
  have hconstructorPrefixEq : future.IsDefEqU uvars Gamma
      (.app (.const ``LeanBox.wrap []) constructorAlpha)
      (.app (.const ``LeanBox.wrap []) (.const ``LeanTree [])) :=
    ⟨_, .appDF hconstructorConstantTyped hparameterAtConstructor⟩
  obtain ⟨fieldDomain, fieldBody, hconstructorAlphaHead, hfieldTyped⟩ :=
    hconstructorApplied.app_inv hfutureWF.ordered hGamma
  have hconstructorPrefixEqTyped : future.IsDefEq uvars Gamma
      (.app (.const ``LeanBox.wrap []) constructorAlpha)
      (.app (.const ``LeanBox.wrap []) (.const ``LeanTree []))
      (.forallE fieldDomain fieldBody) :=
    hconstructorPrefixEq.of_l hfutureWF hGamma hconstructorAlphaHead
  have hconstructorAppliedFromPrefix : future.HasType uvars Gamma
      (VExpr.appN
        (.app (.const ``LeanBox.wrap []) constructorAlpha) [field])
      majorDomain := by
    simpa only [VExpr.appN] using hconstructorApplied
  have hconstructorEq : future.IsDefEqU uvars Gamma
      (VExpr.appN (.const ``LeanBox.wrap []) [constructorAlpha, field])
      (VExpr.appN (.const ``LeanBox.wrap [])
        [.const ``LeanTree [], field]) := by
    simpa only [VExpr.appN] using
      (Lean4Lean.VEnv.IsDefEq.appN_same hfutureWF hGamma
        hconstructorPrefixEqTyped hconstructorAppliedFromPrefix)
  have hconstructorEqTyped : future.IsDefEq uvars Gamma
      (VExpr.appN (.const ``LeanBox.wrap []) [constructorAlpha, field])
      (VExpr.appN (.const ``LeanBox.wrap [])
        [.const ``LeanTree [], field]) majorDomain :=
    hconstructorEq.of_l hfutureWF hGamma hconstructorApplied
  have hredex : future.IsDefEqU uvars Gamma
      (.app
        (VExpr.appN (.const ``LeanTree.rec_1 [u])
          [motiveTree, motiveBox, nodeMinor, wrapMinor])
        (VExpr.appN (.const ``LeanBox.wrap []) [constructorAlpha, field]))
      (.app
        (VExpr.appN (.const ``LeanTree.rec_1 [u])
          [motiveTree, motiveBox, nodeMinor, wrapMinor])
        (VExpr.appN (.const ``LeanBox.wrap [])
          [.const ``LeanTree [], field])) :=
    ⟨_, .appDF hrecursorApplied hconstructorEqTyped⟩

  have hequation : future.IsDefEq uvars Gamma
      (semanticTreeWrapRule.lhs.instL [u])
      (semanticTreeWrapRule.rhs.instL [u])
      (semanticTreeWrapRule.type.instL [u]) :=
    .extra (hfuture.defeqs semanticTreeTransactionFacts.dependencyRule)
      hlevelsWF (by rfl)

  have hrecursorCommonType : future.HasType uvars Gamma
      (.const ``LeanTree.rec_1 [u])
      (VExpr.forallN (commonBinders.map (VExpr.instL [u]))
        (VExpr.dropN 4 (semanticTreeRecOne.type.instL [u]))) := by
    rw [← recOneTypeCommon]
    exact hrecursorConstantTyped
  have hequationLhsCommonType : future.HasType uvars Gamma
      (semanticTreeWrapRule.lhs.instL [u])
      (VExpr.forallN (commonBinders.map (VExpr.instL [u]))
        (VExpr.dropN 4 (semanticTreeWrapRule.type.instL [u]))) := by
    rw [← wrapRuleTypeCommon]
    exact hequation.hasType.1
  have hcommonLength :
      [motiveTree, motiveBox, nodeMinor, wrapMinor].length =
        (commonBinders.map (VExpr.instL [u])).length := by
    simpa only [List.length_cons, List.length_nil, List.length_map] using
      commonBindersLength.symm
  have hequationLhsCommonApplied : future.HasType uvars Gamma
      (VExpr.appN (semanticTreeWrapRule.lhs.instL [u])
        [motiveTree, motiveBox, nodeMinor, wrapMinor])
      (wrapEquationFieldType u motiveTree motiveBox nodeMinor wrapMinor) :=
    Lean4Lean.VEnv.HasType.transfer_appN_telescope_instRev
      hfutureWF hGamma hcommonLength hrecursorApplied
      hrecursorCommonType hequationLhsCommonType

  have hcertifiedTreeLookup :=
    hfuture.constants semanticTreeTransactionFacts.sourceFamily
  have htreeConstantTyped : future.HasType uvars Gamma
      (.const ``LeanTree []) (.sort (.succ .zero)) := by
    have htyped := Lean4Lean.VEnv.HasType.const (U := uvars)
      (Γ := Gamma) (ls := []) hcertifiedTreeLookup (by simp) (by rfl)
    rw [treeFamilyTypeInstLNil, treeFamilyTypeShape] at htyped
    exact htyped
  have hcanonicalConstructorPrefix : future.HasType uvars Gamma
      (.app (.const ``LeanBox.wrap []) (.const ``LeanTree []))
      wrapConstructorFieldType := by
    have happ := Lean4Lean.VEnv.HasType.app
      hconstructorParameterHead htreeConstantTyped
    change future.HasType uvars Gamma
      (.app (.const ``LeanBox.wrap []) (.const ``LeanTree []))
      wrapConstructorFieldType
    exact happ
  have hcanonicalConstructorApplied : future.HasType uvars Gamma
      (VExpr.appN
        (.app (.const ``LeanBox.wrap []) (.const ``LeanTree [])) [field])
      majorDomain := by
    have htyped := hconstructorEqTyped.hasType.2
    simpa only [VExpr.appN] using htyped

  have hequationFieldHead : future.HasType uvars Gamma
      (VExpr.appN (semanticTreeWrapRule.lhs.instL [u])
        [motiveTree, motiveBox, nodeMinor, wrapMinor])
      (VExpr.forallN
        (VExpr.telN 1
          (wrapEquationFieldType u motiveTree motiveBox nodeMinor wrapMinor))
        (VExpr.dropN 1
          (wrapEquationFieldType u motiveTree motiveBox nodeMinor
            wrapMinor))) := by
    rw [← VExpr.forallN_telN_dropN 1
      (wrapEquationFieldType u motiveTree motiveBox nodeMinor wrapMinor)]
    exact hequationLhsCommonApplied
  have hconstructorFieldHead : future.HasType uvars Gamma
      (.app (.const ``LeanBox.wrap []) (.const ``LeanTree []))
      (VExpr.forallN (VExpr.telN 1 wrapConstructorFieldType)
        (VExpr.dropN 1 wrapConstructorFieldType)) := by
    rw [← VExpr.forallN_telN_dropN 1 wrapConstructorFieldType]
    exact hcanonicalConstructorPrefix
  have hconstructorFieldHead' : future.HasType uvars Gamma
      (.app (.const ``LeanBox.wrap []) (.const ``LeanTree []))
      (VExpr.forallN
        (VExpr.telN 1
          (wrapEquationFieldType u motiveTree motiveBox nodeMinor wrapMinor))
        (VExpr.dropN 1 wrapConstructorFieldType)) := by
    rw [wrapFieldBindersEq]
    exact hconstructorFieldHead
  have hfieldLength :
      [field].length =
        (VExpr.telN 1
          (wrapEquationFieldType u motiveTree motiveBox nodeMinor
            wrapMinor)).length := by
    rw [wrapFieldBindersEq]
    rfl
  have hequationLhsFieldsApplied :=
    Lean4Lean.VEnv.HasType.transfer_appN_telescope_instRev
      hfutureWF hGamma hfieldLength hcanonicalConstructorApplied
      hconstructorFieldHead' hequationFieldHead
  have hequationLhsApplied : future.HasType uvars Gamma
      (VExpr.appN (semanticTreeWrapRule.lhs.instL [u])
        [motiveTree, motiveBox, nodeMinor, wrapMinor, field])
      (VExpr.instRev
        (VExpr.dropN 1
          (wrapEquationFieldType u motiveTree motiveBox nodeMinor wrapMinor))
        [field]) := by
    rw [show [motiveTree, motiveBox, nodeMinor, wrapMinor, field] =
      [motiveTree, motiveBox, nodeMinor, wrapMinor] ++ [field] by rfl,
      VExpr.appN_append]
    exact hequationLhsFieldsApplied
  have hequationApplied :=
    Lean4Lean.VEnv.IsDefEq.appN_same hfutureWF hGamma hequation
      hequationLhsApplied

  have hequationLhsApplied' := hequationLhsApplied
  rw [wrapRuleLhsShape, VExpr.instL_lamN] at hequationLhsApplied'
  have hruleArgsLength :
      [motiveTree, motiveBox, nodeMinor, wrapMinor, field].length =
        (wrapRuleBinders.map (VExpr.instL [u])).length := by
    simpa only [List.length_cons, List.length_nil, List.length_map] using
      wrapRuleBindersLength.symm
  have hlhsBeta := Lean4Lean.VEnv.HasType.lamN_appN_beta
    hfutureWF hGamma hruleArgsLength hequationLhsApplied'
  rw [wrapLhsBodyOpen] at hlhsBeta
  have hlhsBeta' : future.IsDefEqU uvars Gamma
      (VExpr.appN (semanticTreeWrapRule.lhs.instL [u])
        [motiveTree, motiveBox, nodeMinor, wrapMinor, field])
      (.app
        (VExpr.appN (.const ``LeanTree.rec_1 [u])
          [motiveTree, motiveBox, nodeMinor, wrapMinor])
        (VExpr.appN (.const ``LeanBox.wrap [])
          [.const ``LeanTree [], field])) := by
    rw [wrapRuleLhsShape, VExpr.instL_lamN]
    exact hlhsBeta

  have hgenerated :=
    hlhsBeta'.symm.trans hfutureWF hGamma hequationApplied
  have hresult := hredex.trans hfutureWF hGamma hgenerated
  rw [hmatched]
  change future.IsDefEqU uvars Gamma
    (.app
      (VExpr.appN (.const ``LeanTree.rec_1 [u])
        [motiveTree, motiveBox, nodeMinor, wrapMinor])
      (VExpr.appN (.const ``LeanBox.wrap []) [constructorAlpha, field]))
    (treeWrapPattern.rhs.apply [u] captures)
  rw [treeWrapPattern_rhs_apply]
  simpa [hcapMotiveTree, hcapMotiveBox, hcapNodeMinor, hcapWrapMinor,
    hcapField] using hresult

/-- Both restored nested equations are sound in their completed semantic
environment. -/
theorem nestedRestoredPatternSound : NestedRestoredPatternSound where
  node := treeNodePatternSound
  wrap := treeWrapPatternSound

theorem treeNodePatternRel :
    RawRecursorRulePatternRel semanticTreeEnv nestedRecursorCatalog
      nestedRecursorNameOf treeRecId treeRecConcrete treeNodeRecRule
      treeNodePattern :=
  RawRecursorRulePatternRel.of_metadata_sound treeNodePatternMetadata
    treeNodePatternSound

theorem treeWrapPatternRel :
    RawRecursorRulePatternRel semanticTreeEnv nestedRecursorCatalog
      nestedRecursorNameOf treeRecOneId treeRecOneConcrete treeWrapRecRule
      treeWrapPattern :=
  RawRecursorRulePatternRel.of_metadata_sound treeWrapPatternMetadata
    treeWrapPatternSound

end Ix.Tc.NestedRecursiveFixture
