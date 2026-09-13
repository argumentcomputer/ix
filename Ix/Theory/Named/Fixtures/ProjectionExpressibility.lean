/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Meta
import Ix.Theory.Named.Projection
import Ix.Theory.Named.Typing.InductiveLemmas

open Ix.Theory (VLevel)

/-!
# Projection expressibility fixtures

The main fixture is simultaneously parameterized, universe-polymorphic, and
dependent: the final field type mentions the preceding projection.  It is
small enough that the complete recursor encoding remains definitionally
inspectable.
-/

namespace Ix.Theory.Named.Tests.ProjectionExpressibility

open Ix.Theory.Named VInductDecl

universe u v

structure DependentRecord (α : Type u) (family : α → Type v) where
  key : α
  value : family key

def dependentRecordCtor : VConstVal :=
  ⟨vconst(type_of% @DependentRecord.mk), ``DependentRecord.mk⟩

def dependentRecordType : VInductiveType where
  name := ``DependentRecord
  uvars := 2
  type := vconst(type_of% @DependentRecord).type
  ctors := [dependentRecordCtor]

def dependentRecordDecl : VInductDecl :=
  ⟨2, 2, [dependentRecordType]⟩

example : dependentRecordDecl.checked?.isSome = true := rfl

def dependentRecordChecked : dependentRecordDecl.Checked :=
  dependentRecordDecl.checked?.get (by decide)

def dependentRecordGeneration : dependentRecordDecl.GenerationChecked :=
  dependentRecordChecked.identityGeneration

def dependentRecordView : VStructureView where
  source := dependentRecordDecl
  generation := dependentRecordGeneration
  constructor := dependentRecordGeneration.block.ctorPairs[0]
  constructor_eq := rfl
  raw_indices_eq := rfl
  checked_indices_eq := rfl
  recursive_eq := rfl
  fieldSorts := [.succ (.param 0), .succ (.param 1)]
  fieldSorts_length := rfl

def dependentRecordEnv : VEnv :=
  (VEnv.empty.addInductGeneration dependentRecordGeneration).get (by decide)

theorem dependentRecord_add :
    VEnv.empty.addInductGeneration dependentRecordGeneration =
      some dependentRecordEnv := rfl

theorem dependentRecord_trace :
    Nonempty (VEnv.AddInductGenerationTrace VEnv.empty
      dependentRecordEnv dependentRecordGeneration) :=
  VEnv.addInductGeneration_trace dependentRecord_add

theorem dependentRecordDecl_wf :
    dependentRecordDecl.WF VEnv.empty := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = dependentRecordType :=
    List.mem_singleton.1 (by simpa [dependentRecordDecl] using hty)
  subst ty
  refine ⟨?_, ?_⟩
  · exact ⟨⟨_, by type_tac⟩, ⟨⟨_, by type_tac⟩, trivial⟩⟩
  · intro c hc
    have hc' : c = dependentRecordCtor := by
      simpa [dependentRecordType] using hc
    subst c
    constructor
    · simp [dependentRecordDecl, dependentRecordType,
        dependentRecordCtor, VInductDecl.fieldsWF,
        VInductDecl.ctorFields, VInductDecl.isRecField,
        VInductDecl.recArg?, VInductDecl.recTarget?,
        VInductDecl.recFieldIdxs, VInductDecl.sortLevel,
        VExpr.dropN, VExpr.resultOf, VExpr.appHead,
        VExpr.appArgs]
      exact ⟨
        ⟨VLevel.succ (.param 0), by type_tac, VLevel.le_max_left⟩,
        ⟨VLevel.succ (.param 1), by type_tac, VLevel.le_max_right⟩⟩
    · simp [dependentRecordDecl, dependentRecordType,
        dependentRecordCtor, VInductDecl.ctorFields,
        VInductDecl.recFieldIdxs, VInductDecl.sortLevel,
        VExpr.dropN, VExpr.resultOf, VExpr.forallN,
        VExpr.liftTelN, VExpr.appArgs]
      exact .nil

theorem dependentRecordGeneration_wf :
    dependentRecordGeneration.WF VEnv.empty :=
  (dependentRecordChecked.wf_of_decl
    dependentRecordDecl_wf).identityGeneration .empty

theorem dependentRecordEnv_ordered : dependentRecordEnv.Ordered :=
  VEnv.addInductGeneration_WF .empty dependentRecordGeneration_wf
    dependentRecord_add

theorem dependentRecordEnv_wf : dependentRecordEnv.WF :=
  ⟨[.induct dependentRecordDecl],
    .decl (.induct dependentRecordGeneration_wf dependentRecord_add) .empty⟩

theorem dependentRecord_generation_semantics :
    dependentRecordView.GenerationSemantics dependentRecordEnv := by
  rcases dependentRecord_trace with ⟨trace⟩
  exact .ofGenerationTrace dependentRecordGeneration_wf trace

theorem dependentRecord_registered :
    dependentRecordView.Registered dependentRecordEnv := by
  rcases dependentRecord_trace with ⟨trace⟩
  refine {
    family := trace.family_lookup
    constructor := ?_
    recursor := trace.rec_lookup
    rules := fun _ h => trace.rule_mem h }
  apply trace.ctor_lookup
  rw [← dependentRecordGeneration.rawCtors_eq]
  exact List.mem_map.2 ⟨dependentRecordView.constructor,
    by
      change dependentRecordView.constructor ∈
        dependentRecordView.generation.block.ctorPairs
      rw [dependentRecordView.constructor_eq]
      simp,
    rfl⟩

theorem dependentRecord_view_wf :
    dependentRecordView.WF dependentRecordEnv := by
  refine {
    toRegistered := dependentRecord_registered
    generationSemantics := dependentRecord_generation_semantics
    parameters := ?_
    parameters_length := rfl
    fieldTelescope := ?_
    smallFields := ?_ }
  · exact ⟨⟨_, by type_tac⟩, ⟨⟨_, by type_tac⟩, trivial⟩⟩
  · exact .cons (by type_tac) (.cons (by type_tac) .nil)
  · intro h
    change VInductDecl.ElimMode.large = .small at h
    contradiction

/-- The checked artifact retains both parameters and exactly the two
dependent fields from the real kernel declaration. -/
example : dependentRecordGeneration.block.rawParams =
    [.sort (.succ (.param 0)),
      .forallE (.bvar 0) (.sort (.succ (.param 1)))] := rfl

example : dependentRecordView.fields =
    [.bvar 1, .app (.bvar 1) (.bvar 0)] := rfl

example : dependentRecordGeneration.elimination = .large := rfl

private def permC (ci : VConstant) (levels : List VLevel) : VConstant :=
  ⟨ci.uvars, ci.type.instL levels⟩

example : dependentRecordGeneration.recursor =
    permC (vconst(type_of% @DependentRecord.rec))
      [.param 1, .param 2, .param 0] := rfl

def symbolicLevels : List VLevel := [.param 0, .param 1]

/-- Parameters in the context `[family, α]`, outermost first. -/
def symbolicParams : List VExpr := [.bvar 1, .bvar 0]

def symbolicStructureType : VExpr :=
  dependentRecordView.structureType symbolicLevels symbolicParams

example : dependentRecordView.specializedFields symbolicLevels symbolicParams =
    [.bvar 1, .app (.bvar 1) (.bvar 0)] := rfl

def keyCode : VStructureView.ProjectionCode :=
  (dependentRecordView.projectionCodes symbolicLevels symbolicParams)[0]

def valueCode : VStructureView.ProjectionCode :=
  (dependentRecordView.projectionCodes symbolicLevels symbolicParams)[1]

/-- Constructor reduction selects the first field for `key`. -/
example : keyCode.minor =
    .lam (.bvar 1)
      (.lam (.app (.bvar 1) (.bvar 0)) (.bvar 1)) := rfl

/-- Constructor reduction selects the second field for `value`. -/
example : valueCode.minor =
    .lam (.bvar 1)
      (.lam (.app (.bvar 1) (.bvar 0)) (.bvar 0)) := rfl

/-- The first field type is `α`. -/
example : keyCode.typeFn =
    .lam symbolicStructureType (.bvar 2) := rfl

/-- The dependent second field type is `family (key major)`: the earlier
projection program occurs in the later motive, rather than being supplied by
an unconstrained witness. -/
example : valueCode.typeFn =
    .lam symbolicStructureType
      (.app (.bvar 1) (.app keyCode.projector.lift (.bvar 0))) := rfl

example : dependentRecordView.projectionLevels keyCode.fieldSort symbolicLevels =
    [.succ (.param 0), .param 0, .param 1] := rfl

example : dependentRecordView.projectionLevels valueCode.fieldSort symbolicLevels =
    [.succ (.param 1), .param 0, .param 1] := rfl

example : dependentRecordView.project? symbolicLevels symbolicParams 2 (.bvar 0) =
    none := rfl

/-- Eta reconstruction uses every generated projector in constructor-field
order, including the projector whose motive depends on the earlier field. -/
example : dependentRecordView.etaRebuild symbolicLevels symbolicParams
    (.bvar 0) =
      VExpr.appN (.const ``DependentRecord.mk symbolicLevels)
        (symbolicParams ++
          [.app keyCode.projector (.bvar 0),
            .app valueCode.projector (.bvar 0)]) := rfl

/-! A fully constrained `VEnv.TrProj` witness in a universe-polymorphic
local context. -/

def symbolicAlphaType : VExpr := .sort (.succ (.param 0))

def symbolicFamilyType : VExpr :=
  .forallE (.bvar 0) (.sort (.succ (.param 1)))

/-- The major binder type is written over `[family, α]`. -/
def symbolicMajorBinderType : VExpr :=
  dependentRecordView.structureType symbolicLevels [.bvar 1, .bvar 0]

def symbolicContext : List VExpr :=
  [symbolicMajorBinderType, symbolicFamilyType, symbolicAlphaType]

/-- The same parameters as seen under the major binder. -/
def symbolicMajorParams : List VExpr := [.bvar 2, .bvar 1]

def symbolicMajor : VExpr := .bvar 0

theorem symbolicLevels_wf :
    ∀ level ∈ symbolicLevels, level.WF 2 := by
  simp [symbolicLevels, VLevel.WF]

theorem symbolicParams_spine :
    ∃ resultLevel, dependentRecordEnv.SpineWF 2 symbolicContext
      (dependentRecordView.familyType.instL symbolicLevels)
      symbolicMajorParams (.sort resultLevel) := by
  refine ⟨.max (.succ (.param 0)) (.succ (.param 1)),
    .cons (by type_tac) ?_⟩
  exact .cons (by type_tac) .nil

theorem symbolicMajor_hasType :
    dependentRecordEnv.HasType 2 symbolicContext symbolicMajor
      (dependentRecordView.structureType symbolicLevels symbolicMajorParams) := by
  exact .bvar .zero

def symbolicKeyCode : VStructureView.ProjectionCode :=
  (dependentRecordView.projectionCodes symbolicLevels symbolicMajorParams)[0]

def symbolicValueCode : VStructureView.ProjectionCode :=
  (dependentRecordView.projectionCodes symbolicLevels symbolicMajorParams)[1]

def symbolicFieldContext : List VExpr :=
  [.app (.bvar 3) (.bvar 0), .bvar 3,
    dependentRecordView.structureType symbolicLevels symbolicMajorParams] ++
    symbolicContext

def symbolicConstructorApp : VExpr :=
  dependentRecordView.projectionConstructorApp symbolicLevels
    (symbolicMajorParams.map (VExpr.liftN 1))
    [.bvar 3, .app (.bvar 3) (.bvar 0)]

def symbolicInnerStructureType : VExpr :=
  dependentRecordView.structureType symbolicLevels [.bvar 5, .bvar 4]

theorem symbolicConstructor_hasType :
    dependentRecordEnv.HasType 2 symbolicFieldContext symbolicConstructorApp
      symbolicInnerStructureType := by
  have hc := VEnv.HasType.const
    (Γ := symbolicFieldContext) dependentRecord_view_wf.constructor
      symbolicLevels_wf (by rfl)
  have hα : dependentRecordEnv.HasType 2 symbolicFieldContext
      (.bvar 5) (.sort (.succ (.param 0))) := by
    type_tac
  have hFamily : dependentRecordEnv.HasType 2 symbolicFieldContext
      (.bvar 4) (.forallE (.bvar 5) (.sort (.succ (.param 1)))) := by
    type_tac
  have hKey : dependentRecordEnv.HasType 2 symbolicFieldContext
      (.bvar 1) (.bvar 5) := by
    type_tac
  have hValue : dependentRecordEnv.HasType 2 symbolicFieldContext
      (.bvar 0) (.app (.bvar 4) (.bvar 1)) := by
    type_tac
  have hcα := hc.app hα
  have hcFamily := hcα.app hFamily
  have hcKey := hcFamily.app hKey
  have hcValue := hcKey.app hValue
  change dependentRecordEnv.HasType 2 symbolicFieldContext
    symbolicConstructorApp symbolicInnerStructureType at hcValue
  exact hcValue

private def takeLamDomains : Nat → VExpr → List VExpr
  | 0, _ => []
  | n + 1, .lam A body => A :: takeLamDomains n body
  | _ + 1, _ => []

private def dropLamBody : Nat → VExpr → VExpr
  | 0, e => e
  | n + 1, .lam _ body => dropLamBody n body
  | _ + 1, e => e

private def dropForallBody : Nat → VExpr → VExpr
  | 0, e => e
  | n + 1, .forallE _ body => dropForallBody n body
  | _ + 1, e => e

theorem symbolicStructure_isType : dependentRecordEnv.IsType 2 symbolicContext
    (dependentRecordView.structureType symbolicLevels symbolicMajorParams) := by
  obtain ⟨resultLevel, hspine⟩ := symbolicParams_spine
  have hfamily := VEnv.HasType.const
    (Γ := symbolicContext) dependentRecord_view_wf.family
      symbolicLevels_wf (by rfl)
  exact ⟨resultLevel, by
    simpa [VStructureView.structureType] using hspine.hasType_appN hfamily⟩

theorem symbolicMajorBinder_isType : dependentRecordEnv.IsType 2
    [symbolicFamilyType, symbolicAlphaType] symbolicMajorBinderType := by
  let resultLevel := VLevel.max (.succ (.param 0)) (.succ (.param 1))
  have hspine : dependentRecordEnv.SpineWF 2
      [symbolicFamilyType, symbolicAlphaType]
      (dependentRecordView.familyType.instL symbolicLevels)
      [.bvar 1, .bvar 0] (.sort resultLevel) := by
    refine .cons (by type_tac) ?_
    exact .cons (by type_tac) .nil
  have hfamily := VEnv.HasType.const
    (Γ := [symbolicFamilyType, symbolicAlphaType])
      dependentRecord_view_wf.family symbolicLevels_wf (by rfl)
  exact ⟨resultLevel, by
    simpa [symbolicMajorBinderType, VStructureView.structureType] using
      hspine.hasType_appN hfamily⟩

theorem symbolicFieldContext_wf :
    OnCtx symbolicFieldContext (dependentRecordEnv.IsType 2) := by
  refine ⟨?_, ⟨_, by type_tac⟩⟩
  refine ⟨?_, ⟨_, by type_tac⟩⟩
  refine ⟨?_, symbolicStructure_isType⟩
  refine ⟨?_, symbolicMajorBinder_isType⟩
  refine ⟨?_, ⟨_, by type_tac⟩⟩
  exact ⟨trivial, ⟨_, by type_tac⟩⟩

def symbolicKeyMotive : VExpr := symbolicKeyCode.typeFn.liftN 3

def symbolicKeyMinor : VExpr := symbolicKeyCode.minor.liftN 3

def symbolicKeyRuleLevels : List VLevel :=
  dependentRecordView.projectionLevels symbolicKeyCode.fieldSort symbolicLevels

def symbolicKeyRule : VDefEq := dependentRecordGeneration.generatedRules[0]

def symbolicKeyRuleType : VExpr :=
  .forallE (.sort (.succ (.param 0)))
    (.forallE (.forallE (.bvar 0) (.sort (.succ (.param 1))))
      (.forallE
        (.forallE
          (dependentRecordView.structureType symbolicLevels [.bvar 1, .bvar 0])
          (.sort (.succ (.param 0))))
        (.forallE
          (.forallE (.bvar 2)
            (.forallE (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 2)
                (.app
                  (.app
                    (.app
                      (.app (.const ``DependentRecord.mk symbolicLevels)
                        (.bvar 4))
                      (.bvar 3))
                    (.bvar 1))
                  (.bvar 0)))))
          (.forallE (.bvar 3)
            (.forallE (.app (.bvar 3) (.bvar 0))
              (.app (.bvar 3)
                (.app
                  (.app
                    (.app
                      (.app (.const ``DependentRecord.mk symbolicLevels)
                        (.bvar 5))
                      (.bvar 4))
                    (.bvar 1))
                  (.bvar 0))))))))

theorem symbolicKeyRuleType_eq :
    symbolicKeyRule.type.instL symbolicKeyRuleLevels =
      symbolicKeyRuleType := rfl

def symbolicKeyRuleArgs : List VExpr :=
  [.bvar 5, .bvar 4, symbolicKeyMotive, symbolicKeyMinor,
    .bvar 1, .bvar 0]

def symbolicKeyRuleResult : VExpr :=
  VExpr.instRev (dropForallBody 6 symbolicKeyRuleType) symbolicKeyRuleArgs

theorem symbolicKeyRule_spine :
    dependentRecordEnv.SpineWF 2 symbolicFieldContext
      (symbolicKeyRule.type.instL symbolicKeyRuleLevels)
      symbolicKeyRuleArgs symbolicKeyRuleResult := by
  rw [symbolicKeyRuleType_eq]
  unfold symbolicKeyRuleArgs symbolicKeyRuleResult
  refine .cons (by type_tac) ?_
  refine .cons (by type_tac) ?_
  refine .cons ?_ ?_
  · have hMotiveShape : symbolicKeyMotive =
        .lam
          ((dependentRecordView.structureType symbolicLevels
            symbolicMajorParams).liftN 3)
          (.bvar 6) := rfl
    rw [hMotiveShape]
    obtain ⟨structureLevel, hstructure⟩ :=
      symbolicStructure_isType.weakN dependentRecordEnv_ordered
        (Ctx.LiftN.zero
          [.app (.bvar 3) (.bvar 0), .bvar 3,
            dependentRecordView.structureType symbolicLevels
              symbolicMajorParams])
    exact VEnv.HasType.lam (u := structureLevel) hstructure (by type_tac)
  · refine .cons ?_ ?_
    · change dependentRecordEnv.HasType 2 symbolicFieldContext
        symbolicKeyMinor
        (.forallE (.bvar 5)
          (.forallE (.app (.bvar 5) (.bvar 0))
            (.app (symbolicKeyMotive.liftN 2)
              (.app
                (.app
                  (.app
                    (.app (.const ``DependentRecord.mk symbolicLevels)
                      (.bvar 7))
                    (.bvar 6))
                  (.bvar 1))
                (.bvar 0)))))
      have hMinorShape : symbolicKeyMinor =
          .lam (.bvar 5)
            (.lam (.app (.bvar 5) (.bvar 0)) (.bvar 1)) := rfl
      rw [hMinorShape]
      refine .lam (by type_tac) ?_
      refine .lam (by type_tac) ?_
      have hMotiveLiftShape : symbolicKeyMotive.liftN 2 =
          .lam
            (dependentRecordView.structureType symbolicLevels
              [.bvar 7, .bvar 6])
            (.bvar 8) := rfl
      rw [hMotiveLiftShape]
      let innerCtor : VExpr :=
        .app
          (.app
            (.app
              (.app (.const ``DependentRecord.mk symbolicLevels) (.bvar 7))
              (.bvar 6))
            (.bvar 1))
          (.bvar 0)
      let innerStructure : VExpr :=
        dependentRecordView.structureType symbolicLevels [.bvar 7, .bvar 6]
      have hkey : dependentRecordEnv.HasType 2
          ((.app (.bvar 5) (.bvar 0)) :: .bvar 5 :: symbolicFieldContext)
          (.bvar 1) (.bvar 7) := by
        type_tac
      have hctor : dependentRecordEnv.HasType 2
          ((.app (.bvar 5) (.bvar 0)) :: .bvar 5 :: symbolicFieldContext)
          innerCtor innerStructure := by
        have hc := VEnv.HasType.const
          (Γ := ((.app (.bvar 5) (.bvar 0)) :: .bvar 5 ::
            symbolicFieldContext))
          dependentRecord_view_wf.constructor symbolicLevels_wf (by rfl)
        have hα : dependentRecordEnv.HasType 2
            ((.app (.bvar 5) (.bvar 0)) :: .bvar 5 :: symbolicFieldContext)
            (.bvar 7) (.sort (.succ (.param 0))) := by
          type_tac
        have hFamily : dependentRecordEnv.HasType 2
            ((.app (.bvar 5) (.bvar 0)) :: .bvar 5 :: symbolicFieldContext)
            (.bvar 6)
            (.forallE (.bvar 7) (.sort (.succ (.param 1)))) := by
          type_tac
        have hValue : dependentRecordEnv.HasType 2
            ((.app (.bvar 5) (.bvar 0)) :: .bvar 5 :: symbolicFieldContext)
            (.bvar 0) (.app (.bvar 6) (.bvar 1)) := by
          type_tac
        have hcValue := (((hc.app hα).app hFamily).app hkey).app hValue
        change dependentRecordEnv.HasType 2
          ((.app (.bvar 5) (.bvar 0)) :: .bvar 5 :: symbolicFieldContext)
          innerCtor innerStructure at hcValue
        exact hcValue
      have hbody : dependentRecordEnv.HasType 2
          (innerStructure :: (.app (.bvar 5) (.bvar 0)) :: .bvar 5 ::
            symbolicFieldContext)
          (.bvar 8) (.sort (.succ (.param 0))) := by
        dsimp [innerStructure]
        type_tac
      have hbetaRaw := VEnv.IsDefEq.beta hbody hctor
      have hbeta : dependentRecordEnv.IsDefEq 2
          ((.app (.bvar 5) (.bvar 0)) :: .bvar 5 :: symbolicFieldContext)
          (.app (.lam innerStructure (.bvar 8)) innerCtor)
          (.bvar 7) (.sort (.succ (.param 0))) := by
        simpa [innerCtor, innerStructure, VExpr.inst, VExpr.instVar] using hbetaRaw
      exact hbeta.symm.defeq hkey
    · refine .cons (by type_tac) ?_
      exact .cons (by type_tac) .nil

def symbolicKeyRuleBinders : List VExpr :=
  takeLamDomains 6 (symbolicKeyRule.lhs.instL symbolicKeyRuleLevels)

def symbolicKeyRuleLhsBody : VExpr :=
  dropLamBody 6 (symbolicKeyRule.lhs.instL symbolicKeyRuleLevels)

def symbolicKeyRuleRhsBody : VExpr :=
  dropLamBody 6 (symbolicKeyRule.rhs.instL symbolicKeyRuleLevels)

def symbolicKeyRuleTypeBody : VExpr :=
  dropForallBody 6 (symbolicKeyRule.type.instL symbolicKeyRuleLevels)

theorem symbolicKeyRule_lhs_shape :
    symbolicKeyRule.lhs.instL symbolicKeyRuleLevels =
      VExpr.lamN symbolicKeyRuleBinders symbolicKeyRuleLhsBody := rfl

theorem symbolicKeyRule_rhs_shape :
    symbolicKeyRule.rhs.instL symbolicKeyRuleLevels =
      VExpr.lamN symbolicKeyRuleBinders symbolicKeyRuleRhsBody := rfl

theorem symbolicKeyRule_type_shape :
    symbolicKeyRule.type.instL symbolicKeyRuleLevels =
      VExpr.forallN symbolicKeyRuleBinders symbolicKeyRuleTypeBody := rfl

theorem symbolicKeyRuleBinders_length : symbolicKeyRuleBinders.length = 6 := rfl

theorem symbolicKeyRuleArgs_length : symbolicKeyRuleArgs.length = 6 := rfl

theorem symbolicKeyRule_registered : dependentRecordEnv.defeqs symbolicKeyRule := by
  apply dependentRecord_view_wf.rules
  decide

theorem symbolicKeyRule_levels_wf :
    ∀ level ∈ symbolicKeyRuleLevels, level.WF 2 := by
  decide

theorem symbolicKeyRule_levels_length :
    symbolicKeyRuleLevels.length = symbolicKeyRule.uvars := by
  decide

theorem symbolicKeyRule_reduces : dependentRecordEnv.IsDefEqU 2
    symbolicFieldContext
    (VExpr.instRev symbolicKeyRuleLhsBody symbolicKeyRuleArgs)
    (VExpr.instRev symbolicKeyRuleRhsBody symbolicKeyRuleArgs) := by
  have hextra : dependentRecordEnv.IsDefEq 2 symbolicFieldContext
      (symbolicKeyRule.lhs.instL symbolicKeyRuleLevels)
      (symbolicKeyRule.rhs.instL symbolicKeyRuleLevels)
      (symbolicKeyRule.type.instL symbolicKeyRuleLevels) :=
    .extra symbolicKeyRule_registered symbolicKeyRule_levels_wf
      symbolicKeyRule_levels_length
  have happlied := hextra.appN_congr symbolicKeyRule_spine
  have hlhsType := hextra.hasType.1
  rw [symbolicKeyRule_lhs_shape] at hlhsType
  obtain ⟨hlhsTel, lhsType, hlhsBody⟩ := VEnv.HasType.lamN_wf
    dependentRecordEnv_ordered symbolicFieldContext_wf hlhsType
  have hlhsSpine := symbolicKeyRule_spine
  rw [symbolicKeyRule_type_shape] at hlhsSpine
  have hlhsRetarget := hlhsSpine.retarget
    (symbolicKeyRuleArgs_length.trans symbolicKeyRuleBinders_length.symm)
    lhsType
  have hcollapseL := VEnv.IsDefEq.appN_lamN dependentRecordEnv_ordered
    hlhsTel hlhsBody hlhsRetarget
      (symbolicKeyRuleArgs_length.trans symbolicKeyRuleBinders_length.symm)
  have hrhsType := hextra.hasType.2
  rw [symbolicKeyRule_rhs_shape] at hrhsType
  obtain ⟨hrhsTel, rhsType, hrhsBody⟩ := VEnv.HasType.lamN_wf
    dependentRecordEnv_ordered symbolicFieldContext_wf hrhsType
  have hrhsSpine := symbolicKeyRule_spine
  rw [symbolicKeyRule_type_shape] at hrhsSpine
  have hrhsRetarget := hrhsSpine.retarget
    (symbolicKeyRuleArgs_length.trans symbolicKeyRuleBinders_length.symm)
    rhsType
  have hcollapseR := VEnv.IsDefEq.appN_lamN dependentRecordEnv_ordered
    hrhsTel hrhsBody hrhsRetarget
      (symbolicKeyRuleArgs_length.trans symbolicKeyRuleBinders_length.symm)
  rw [symbolicKeyRule_lhs_shape, symbolicKeyRule_rhs_shape] at happlied
  exact VEnv.IsDefEqU.trans dependentRecordEnv_wf symbolicFieldContext_wf
    ⟨_, hcollapseL.symm⟩
    (VEnv.IsDefEqU.trans dependentRecordEnv_wf symbolicFieldContext_wf
      ⟨_, happlied⟩ ⟨_, hcollapseR⟩)

theorem symbolicKeyProjector_hasType :
    dependentRecordEnv.HasType 2 symbolicContext symbolicKeyCode.projector
      (.forallE
        (dependentRecordView.structureType symbolicLevels symbolicMajorParams)
        (.app symbolicKeyCode.typeFn.lift (.bvar 0))) := by
  obtain ⟨resultLevel, hspine⟩ := symbolicParams_spine
  have hfamily := VEnv.HasType.const
    (Γ := symbolicContext) dependentRecord_view_wf.family
      symbolicLevels_wf (by rfl)
  have hstructure : dependentRecordEnv.HasType 2 symbolicContext
      (dependentRecordView.structureType symbolicLevels symbolicMajorParams)
      (.sort resultLevel) := by
    simpa [VStructureView.structureType] using hspine.hasType_appN hfamily
  have W : Ctx.LiftN 1 0 symbolicContext
      (dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
        symbolicContext) := .one
  change dependentRecordEnv.HasType 2 symbolicContext (.lam _ _)
    (.forallE _ _)
  refine .lam hstructure ?_
  change dependentRecordEnv.HasType 2
    (dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
      symbolicContext)
    (VExpr.appN
      (.const dependentRecordView.recursorName
        (dependentRecordView.projectionLevels
          symbolicKeyCode.fieldSort symbolicLevels))
      (symbolicMajorParams.map (VExpr.liftN 1) ++
        [symbolicKeyCode.typeFn.lift, symbolicKeyCode.minor.lift,
          .bvar 0]))
    (.app symbolicKeyCode.typeFn.lift (.bvar 0))
  apply dependentRecord_view_wf.recursorProjection_hasType
    dependentRecordEnv_ordered symbolicLevels symbolicLevels_wf rfl
    (symbolicMajorParams.map (VExpr.liftN 1)) (by rfl)
    (fieldSort := symbolicKeyCode.fieldSort)
  · refine ⟨resultLevel, ?_⟩
    have hfamilyClosed :
        (dependentRecordView.familyType.instL symbolicLevels).ClosedN 0 := by
      simpa using
        (dependentRecordEnv_ordered.closedC
          dependentRecord_view_wf.family).instL
    have hspine' := hspine.weakN dependentRecordEnv_ordered W
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at hspine'
    simpa [VExpr.liftN] using hspine'
  · change VLevel.WF 2 (.succ (.param 0))
    decide
  · rfl
  · exact ⟨resultLevel, by
      simpa [VExpr.liftN] using hstructure.weakN dependentRecordEnv_ordered W⟩
  · change dependentRecordEnv.HasType 2
      (dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
        symbolicContext)
      (.lam
        (dependentRecordView.structureType symbolicLevels
          (symbolicMajorParams.map (VExpr.liftN 1)))
        (.bvar 4))
      (.forallE
        (dependentRecordView.structureType symbolicLevels
          (symbolicMajorParams.map (VExpr.liftN 1)))
        (.sort (.succ (.param 0))))
    refine VEnv.HasType.lam (u := resultLevel) ?_ (by type_tac)
    simpa [VExpr.liftN] using
      hstructure.weakN dependentRecordEnv_ordered W
  · change dependentRecordEnv.HasType 2
      (dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
        symbolicContext)
      (.lam (.bvar 3)
        (.lam (.app (.bvar 3) (.bvar 0)) (.bvar 1)))
      (.forallE (.bvar 3)
        (.forallE (.app (.bvar 3) (.bvar 0))
          (.app
            (.lam
              (.app
                (.app (.const ``DependentRecord symbolicLevels) (.bvar 5))
                (.bvar 4))
              (.bvar 6))
            (.app
              (.app
                (.app
                  (.app (.const ``DependentRecord.mk symbolicLevels)
                    (.bvar 5))
                  (.bvar 4))
                (.bvar 1))
              (.bvar 0)))))
    refine .lam (by type_tac) ?_
    refine .lam (by type_tac) ?_
    have hkey : dependentRecordEnv.HasType 2
        ((.app (.bvar 3) (.bvar 0)) :: .bvar 3 ::
          dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
          symbolicContext)
        (.bvar 1) (.bvar 5) := by
      type_tac
    apply (show dependentRecordEnv.IsDefEq 2
      ((.app (.bvar 3) (.bvar 0)) :: .bvar 3 ::
        dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
        symbolicContext)
      (.bvar 5)
      (.app
        (.lam
          (.app
            (.app (.const ``DependentRecord symbolicLevels) (.bvar 5))
            (.bvar 4))
          (.bvar 6))
        (.app
          (.app
            (.app
              (.app (.const ``DependentRecord.mk symbolicLevels) (.bvar 5))
              (.bvar 4))
            (.bvar 1))
          (.bvar 0)))
      (.sort (.succ (.param 0))) from ?_).defeq hkey
    let S : VExpr :=
      .app
        (.app (.const ``DependentRecord symbolicLevels) (.bvar 5))
        (.bvar 4)
    let ctorApp : VExpr :=
      .app
        (.app
          (.app
            (.app (.const ``DependentRecord.mk symbolicLevels) (.bvar 5))
            (.bvar 4))
          (.bvar 1))
        (.bvar 0)
    have hbody : dependentRecordEnv.HasType 2
        (S :: (.app (.bvar 3) (.bvar 0)) :: .bvar 3 ::
          dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
          symbolicContext)
        (.bvar 6) (.sort (.succ (.param 0))) := by
      dsimp [S]
      type_tac
    have hctor : dependentRecordEnv.HasType 2
        ((.app (.bvar 3) (.bvar 0)) :: .bvar 3 ::
          dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
          symbolicContext)
        ctorApp S := by
      have hc := VEnv.HasType.const
        (Γ := ((.app (.bvar 3) (.bvar 0)) :: .bvar 3 ::
          dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
          symbolicContext))
        dependentRecord_view_wf.constructor symbolicLevels_wf (by rfl)
      have hα : dependentRecordEnv.HasType 2
          ((.app (.bvar 3) (.bvar 0)) :: .bvar 3 ::
            dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
            symbolicContext)
          (.bvar 5) (.sort (.succ (.param 0))) := by
        type_tac
      have hFamily : dependentRecordEnv.HasType 2
          ((.app (.bvar 3) (.bvar 0)) :: .bvar 3 ::
            dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
            symbolicContext)
          (.bvar 4)
          (.forallE (.bvar 5) (.sort (.succ (.param 1)))) := by
        type_tac
      have hKey : dependentRecordEnv.HasType 2
          ((.app (.bvar 3) (.bvar 0)) :: .bvar 3 ::
            dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
            symbolicContext)
          (.bvar 1) (.bvar 5) := by
        type_tac
      have hValue : dependentRecordEnv.HasType 2
          ((.app (.bvar 3) (.bvar 0)) :: .bvar 3 ::
            dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
            symbolicContext)
          (.bvar 0) (.app (.bvar 4) (.bvar 1)) := by
        type_tac
      have hcα := hc.app hα
      have hcFamily := hcα.app hFamily
      have hcKey := hcFamily.app hKey
      have hcValue := hcKey.app hValue
      change dependentRecordEnv.HasType 2
        ((.app (.bvar 3) (.bvar 0)) :: .bvar 3 ::
          dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
          symbolicContext)
        ctorApp S at hcValue
      exact hcValue
    have hbeta := VEnv.IsDefEq.beta hbody hctor
    simpa [S, ctorApp, VExpr.inst, VExpr.instVar] using hbeta.symm
  · exact .bvar .zero

def symbolicKeyProjectorBody : VExpr :=
  match symbolicKeyCode.projector.liftN 3 with
  | .lam _ body => body
  | expression => expression

theorem symbolicKeyProjector_lift_shape :
    symbolicKeyCode.projector.liftN 3 =
      .lam symbolicInnerStructureType symbolicKeyProjectorBody := by
  decide

theorem symbolicKeyProjector_beta_shape :
    symbolicKeyProjectorBody.inst symbolicConstructorApp =
      VExpr.instRev symbolicKeyRuleLhsBody symbolicKeyRuleArgs := by
  decide

theorem symbolicKeyRule_rhs_result_shape :
    VExpr.instRev symbolicKeyRuleRhsBody symbolicKeyRuleArgs =
      .app (.app symbolicKeyMinor (.bvar 1)) (.bvar 0) := by
  decide

/-- The generated key projector computes on the generated constructor by
the registered recursor iota rule. -/
theorem symbolicKey_constructor_defeq : dependentRecordEnv.IsDefEq 2
    symbolicFieldContext
    (.app (symbolicKeyCode.projector.liftN 3) symbolicConstructorApp)
    (.bvar 1) (.bvar 5) := by
  have W3 : Ctx.LiftN 3 0 symbolicContext symbolicFieldContext :=
    .zero [.app (.bvar 3) (.bvar 0), .bvar 3,
      dependentRecordView.structureType symbolicLevels symbolicMajorParams]
  have hprojector := symbolicKeyProjector_hasType.weakN
    dependentRecordEnv_ordered W3
  rw [symbolicKeyProjector_lift_shape] at hprojector
  obtain ⟨_, ⟨projectorBodyType, hprojectorBody⟩⟩ :=
    hprojector.lam_inv dependentRecordEnv_ordered symbolicFieldContext_wf
  have hprojectorBeta := VEnv.IsDefEq.beta hprojectorBody
    symbolicConstructor_hasType
  rw [← symbolicKeyProjector_lift_shape,
    symbolicKeyProjector_beta_shape] at hprojectorBeta
  have hprojectorToRule : dependentRecordEnv.IsDefEqU 2
      symbolicFieldContext
      (.app (symbolicKeyCode.projector.liftN 3) symbolicConstructorApp)
      (VExpr.instRev symbolicKeyRuleLhsBody symbolicKeyRuleArgs) :=
    ⟨projectorBodyType.inst symbolicConstructorApp, hprojectorBeta⟩

  have houterBody : dependentRecordEnv.HasType 2
      ((.bvar 5) :: symbolicFieldContext)
      (.lam (.app (.bvar 5) (.bvar 0)) (.bvar 1))
      (.forallE (.app (.bvar 5) (.bvar 0)) (.bvar 7)) := by
    refine .lam (by type_tac) (by type_tac)
  have hkey : dependentRecordEnv.HasType 2 symbolicFieldContext
      (.bvar 1) (.bvar 5) := by
    type_tac
  have houterBeta := VEnv.IsDefEq.beta houterBody hkey
  change dependentRecordEnv.IsDefEq 2 symbolicFieldContext
    (.app symbolicKeyMinor (.bvar 1)) _ _ at houterBeta
  have hvalue : dependentRecordEnv.HasType 2 symbolicFieldContext
      (.bvar 0) (.app (.bvar 4) (.bvar 1)) := by
    type_tac
  have houterApplied := VEnv.IsDefEq.appDF houterBeta hvalue
  have hinnerBody : dependentRecordEnv.HasType 2
      ((.app (.bvar 4) (.bvar 1)) :: symbolicFieldContext)
      (.bvar 2) (.bvar 6) := by
    type_tac
  have hinnerBeta := VEnv.IsDefEq.beta hinnerBody hvalue
  have hminorToKey := houterApplied.trans hinnerBeta
  rw [← symbolicKeyRule_rhs_result_shape] at hminorToKey
  have hresult := VEnv.IsDefEqU.trans dependentRecordEnv_wf
    symbolicFieldContext_wf hprojectorToRule
    (VEnv.IsDefEqU.trans dependentRecordEnv_wf symbolicFieldContext_wf
      symbolicKeyRule_reduces ⟨_, hminorToKey⟩)
  exact hresult.of_r dependentRecordEnv_wf symbolicFieldContext_wf hkey

def symbolicValueTypeFnBody : VExpr :=
  .app (.bvar 5)
    (.app (symbolicKeyCode.projector.liftN 4) (.bvar 0))

theorem symbolicValueTypeFn_lift_shape :
    symbolicValueCode.typeFn.lift.liftN 2 =
      .lam symbolicInnerStructureType symbolicValueTypeFnBody := by
  decide

theorem symbolicValueTypeFn_beta_shape :
    symbolicValueTypeFnBody.inst symbolicConstructorApp =
      .app (.bvar 4)
        (.app (symbolicKeyCode.projector.liftN 3)
          symbolicConstructorApp) := by
  decide

theorem symbolicValueTypeFnBody_hasType : dependentRecordEnv.HasType 2
    (symbolicInnerStructureType :: symbolicFieldContext)
    symbolicValueTypeFnBody (.sort (.succ (.param 1))) := by
  have W4 : Ctx.LiftN 4 0 symbolicContext
      (symbolicInnerStructureType :: symbolicFieldContext) :=
    .zero [symbolicInnerStructureType,
      .app (.bvar 3) (.bvar 0), .bvar 3,
      dependentRecordView.structureType symbolicLevels symbolicMajorParams]
  have hkeyProjector := symbolicKeyProjector_hasType.weakN
    dependentRecordEnv_ordered W4
  have hkeyAtMajor := hkeyProjector.app (VEnv.HasType.bvar (.zero))
  change dependentRecordEnv.HasType 2
    (symbolicInnerStructureType :: symbolicFieldContext) _
    (.app
      (.lam
        (dependentRecordView.structureType symbolicLevels
          [.bvar 6, .bvar 5])
        (.bvar 7))
      (.bvar 0)) at hkeyAtMajor
  have hkeyBetaRaw : dependentRecordEnv.IsDefEq 2
      (symbolicInnerStructureType :: symbolicFieldContext)
      (.app
        (.lam
          (dependentRecordView.structureType symbolicLevels
            [.bvar 6, .bvar 5])
          (.bvar 7))
        (.bvar 0))
      ((VExpr.bvar 7).inst (.bvar 0))
      ((VExpr.sort (.succ (.param 0))).inst (.bvar 0)) := by
    apply VEnv.IsDefEq.beta
    · type_tac
    · exact .bvar .zero
  have hkeyBeta : dependentRecordEnv.IsDefEq 2
      (symbolicInnerStructureType :: symbolicFieldContext)
      (.app
        (.lam
          (dependentRecordView.structureType symbolicLevels
            [.bvar 6, .bvar 5])
          (.bvar 7))
        (.bvar 0))
      (.bvar 6) (.sort (.succ (.param 0))) := by
    simpa [VExpr.inst, VExpr.instVar] using hkeyBetaRaw
  have hkeyAtMajor' := hkeyBeta.defeq hkeyAtMajor
  have hfamily : dependentRecordEnv.HasType 2
      (symbolicInnerStructureType :: symbolicFieldContext)
      (.bvar 5)
      (.forallE (.bvar 6) (.sort (.succ (.param 1)))) := by
    type_tac
  exact hfamily.app hkeyAtMajor'

theorem symbolicValueProjector_hasType :
    dependentRecordEnv.HasType 2 symbolicContext symbolicValueCode.projector
      (.forallE
        (dependentRecordView.structureType symbolicLevels symbolicMajorParams)
        (.app symbolicValueCode.typeFn.lift (.bvar 0))) := by
  obtain ⟨resultLevel, hspine⟩ := symbolicParams_spine
  have hfamily := VEnv.HasType.const
    (Γ := symbolicContext) dependentRecord_view_wf.family
      symbolicLevels_wf (by rfl)
  have hstructure : dependentRecordEnv.HasType 2 symbolicContext
      (dependentRecordView.structureType symbolicLevels symbolicMajorParams)
      (.sort resultLevel) := by
    simpa [VStructureView.structureType] using hspine.hasType_appN hfamily
  have W : Ctx.LiftN 1 0 symbolicContext
      (dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
        symbolicContext) := .one
  change dependentRecordEnv.HasType 2 symbolicContext (.lam _ _)
    (.forallE _ _)
  refine .lam hstructure ?_
  change dependentRecordEnv.HasType 2
    (dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
      symbolicContext)
    (VExpr.appN
      (.const dependentRecordView.recursorName
        (dependentRecordView.projectionLevels
          symbolicValueCode.fieldSort symbolicLevels))
      (symbolicMajorParams.map (VExpr.liftN 1) ++
        [symbolicValueCode.typeFn.lift, symbolicValueCode.minor.lift,
          .bvar 0]))
    (.app symbolicValueCode.typeFn.lift (.bvar 0))
  apply dependentRecord_view_wf.recursorProjection_hasType
    dependentRecordEnv_ordered symbolicLevels symbolicLevels_wf rfl
    (symbolicMajorParams.map (VExpr.liftN 1)) (by rfl)
    (fieldSort := symbolicValueCode.fieldSort)
  · refine ⟨resultLevel, ?_⟩
    have hfamilyClosed :
        (dependentRecordView.familyType.instL symbolicLevels).ClosedN 0 := by
      simpa using
        (dependentRecordEnv_ordered.closedC
          dependentRecord_view_wf.family).instL
    have hspine' := hspine.weakN dependentRecordEnv_ordered W
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at hspine'
    simpa [VExpr.liftN] using hspine'
  · change VLevel.WF 2 (.succ (.param 1))
    decide
  · rfl
  · exact ⟨resultLevel, by
      simpa [VExpr.liftN] using hstructure.weakN dependentRecordEnv_ordered W⟩
  · change dependentRecordEnv.HasType 2
      (dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
        symbolicContext)
      symbolicValueCode.typeFn.lift
      (.forallE
        (dependentRecordView.structureType symbolicLevels
          (symbolicMajorParams.map (VExpr.liftN 1)))
        (.sort (.succ (.param 1))))
    change dependentRecordEnv.HasType 2
      (dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
        symbolicContext)
      (.lam
        (dependentRecordView.structureType symbolicLevels
          (symbolicMajorParams.map (VExpr.liftN 1)))
        (.app (.bvar 3)
          (.app (symbolicKeyCode.projector.lift.liftN 1 1) (.bvar 0))))
      (.forallE
        (dependentRecordView.structureType symbolicLevels
          (symbolicMajorParams.map (VExpr.liftN 1)))
        (.sort (.succ (.param 1))))
    refine VEnv.HasType.lam (u := resultLevel) ?_ ?_
    · simpa [VExpr.liftN] using
        hstructure.weakN dependentRecordEnv_ordered W
    · have Wbody : Ctx.LiftN 1 0
          (dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
            symbolicContext)
          (dependentRecordView.structureType symbolicLevels
              (symbolicMajorParams.map (VExpr.liftN 1)) ::
            dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
            symbolicContext) := .one
      have hkeyProjector :=
        (symbolicKeyProjector_hasType.weakN dependentRecordEnv_ordered W).weakN
          dependentRecordEnv_ordered Wbody
      have hkeyAtMajor := hkeyProjector.app (VEnv.HasType.bvar (.zero))
      have hkeyTypeFn : symbolicKeyCode.typeFn =
          .lam
            (dependentRecordView.structureType symbolicLevels symbolicMajorParams)
            (.bvar 3) := rfl
      rw [hkeyTypeFn] at hkeyAtMajor
      change dependentRecordEnv.HasType 2
        (dependentRecordView.structureType symbolicLevels
            (symbolicMajorParams.map (VExpr.liftN 1)) ::
          dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
          symbolicContext)
        _
        (.app
          (.lam
            (dependentRecordView.structureType symbolicLevels
              [.bvar 4, .bvar 3])
            (.bvar 5))
          (.bvar 0)) at hkeyAtMajor
      have hkeyBetaRaw : dependentRecordEnv.IsDefEq 2
          (dependentRecordView.structureType symbolicLevels
              (symbolicMajorParams.map (VExpr.liftN 1)) ::
            dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
            symbolicContext)
          (.app
            (.lam
              (dependentRecordView.structureType symbolicLevels
                [.bvar 4, .bvar 3])
              (.bvar 5))
            (.bvar 0))
          ((VExpr.bvar 5).inst (.bvar 0))
          ((VExpr.sort (.succ (.param 0))).inst (.bvar 0)) := by
        apply VEnv.IsDefEq.beta
        · type_tac
        · exact .bvar .zero
      have hkeyBeta : dependentRecordEnv.IsDefEq 2
          (dependentRecordView.structureType symbolicLevels
              (symbolicMajorParams.map (VExpr.liftN 1)) ::
            dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
            symbolicContext)
          (.app
            (.lam
              (dependentRecordView.structureType symbolicLevels
                [.bvar 4, .bvar 3])
              (.bvar 5))
            (.bvar 0))
          (.bvar 4) (.sort (.succ (.param 0))) := by
        simpa [VExpr.inst, VExpr.instVar] using hkeyBetaRaw
      have hkeyAtMajor' := hkeyBeta.defeq hkeyAtMajor
      have hprojectorLift :
          VExpr.liftN 1 (VExpr.liftN 1 symbolicKeyCode.projector) =
          symbolicKeyCode.projector.lift.liftN 1 1 := rfl
      rw [hprojectorLift] at hkeyAtMajor'
      have hfamilyAtMajor : dependentRecordEnv.HasType 2
          (dependentRecordView.structureType symbolicLevels
              (symbolicMajorParams.map (VExpr.liftN 1)) ::
            dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
            symbolicContext)
          (.bvar 3)
          (.forallE (.bvar 4) (.sort (.succ (.param 1)))) := by
        type_tac
      exact hfamilyAtMajor.app hkeyAtMajor'
  · change dependentRecordEnv.HasType 2
      (dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
        symbolicContext)
      (.lam (.bvar 3)
        (.lam (.app (.bvar 3) (.bvar 0)) (.bvar 0)))
      (dependentRecordView.projectionMinorType symbolicLevels
        (symbolicMajorParams.map (VExpr.liftN 1))
        (dependentRecordView.specializedFields symbolicLevels
          (symbolicMajorParams.map (VExpr.liftN 1)))
        symbolicValueCode.typeFn.lift)
    have hfields : dependentRecordView.specializedFields symbolicLevels
        (symbolicMajorParams.map (VExpr.liftN 1)) =
        [.bvar 3, .app (.bvar 3) (.bvar 0)] := rfl
    rw [hfields]
    change dependentRecordEnv.HasType 2
      (dependentRecordView.structureType symbolicLevels symbolicMajorParams ::
        symbolicContext)
      (.lam (.bvar 3)
        (.lam (.app (.bvar 3) (.bvar 0)) (.bvar 0)))
      (.forallE (.bvar 3)
        (.forallE (.app (.bvar 3) (.bvar 0))
          (.app (symbolicValueCode.typeFn.lift.liftN 2)
            (dependentRecordView.projectionConstructorApp symbolicLevels
              (symbolicMajorParams.map (VExpr.liftN 1))
              [.bvar 3, .app (.bvar 3) (.bvar 0)]))))
    refine .lam (by type_tac) ?_
    refine .lam (by type_tac) ?_
    have htargetBeta := VEnv.IsDefEq.beta
      symbolicValueTypeFnBody_hasType symbolicConstructor_hasType
    rw [← symbolicValueTypeFn_lift_shape,
      symbolicValueTypeFn_beta_shape] at htargetBeta
    have hfamily : dependentRecordEnv.HasType 2 symbolicFieldContext
        (.bvar 4)
        (.forallE (.bvar 5) (.sort (.succ (.param 1)))) := by
      type_tac
    have htargetToNatural := htargetBeta.trans
      (VEnv.IsDefEq.appDF hfamily symbolicKey_constructor_defeq)
    have hvalue : dependentRecordEnv.HasType 2 symbolicFieldContext
        (.bvar 0) (.app (.bvar 4) (.bvar 1)) := by
      type_tac
    exact htargetToNatural.defeq' hvalue
  · exact .bvar .zero

def symbolicKeyResult : VExpr :=
  .app symbolicKeyCode.projector symbolicMajor

def symbolicValueResult : VExpr :=
  .app symbolicValueCode.projector symbolicMajor

theorem key_representable :
    dependentRecordEnv.TrProj 2 symbolicContext dependentRecordView
      symbolicLevels symbolicMajorParams 0 symbolicMajor symbolicKeyResult := by
  refine {
    viewWF := dependentRecord_view_wf
    levelsWF := symbolicLevels_wf
    levels_length := rfl
    params_length := rfl
    paramsSpine := symbolicParams_spine
    majorType := symbolicMajor_hasType
    program := ⟨symbolicKeyCode, rfl, rfl,
      symbolicKeyProjector_hasType⟩ }

theorem value_representable :
    dependentRecordEnv.TrProj 2 symbolicContext dependentRecordView
      symbolicLevels symbolicMajorParams 1 symbolicMajor symbolicValueResult := by
  refine {
    viewWF := dependentRecord_view_wf
    levelsWF := symbolicLevels_wf
    levels_length := rfl
    params_length := rfl
    paramsSpine := symbolicParams_spine
    majorType := symbolicMajor_hasType
    program := ⟨symbolicValueCode, rfl, rfl,
      symbolicValueProjector_hasType⟩ }

/-- The one generated iota equation used by both projection programs is
actually registered in the final Theory environment. -/
example : dependentRecordGeneration.generatedRules.length = 1 := rfl

theorem dependentRecord_rules_registered :
    ∀ rule ∈ dependentRecordGeneration.generatedRules,
      dependentRecordEnv.defeqs rule :=
  dependentRecord_view_wf.rules

/-! ## Frozen legacy surface

The seven fields below preserve the exact pre-Spec-13 theorem shapes.  They
are intentionally only statement data: constructing this bundle would
reintroduce the old proof obligations.  In particular, `wf` permits
unrelated contexts, `uniq` permits unrelated structure names, and every
field omits the environment, universe instantiation, and parameter spine. -/

abbrev LegacyTrProj :=
  List VExpr → Name → Nat → VExpr → VExpr → Prop

structure LegacyProjectionLaws (R : LegacyTrProj) : Prop where
  weak : ∀ {n Γ Γ' s i e e'},
    Ctx.Lift' n Γ Γ' → R Γ s i e e' →
      R Γ' s i (e.lift' n) (e'.lift' n)
  inverseWeakening : ∀ {env U l Γ Γ' s i e e'},
    VEnv.WF env → OnCtx Γ' (env.IsType U) → Ctx.Lift' l Γ Γ' →
      R Γ' s i (e.lift' l) e' → ∃ result, R Γ s i e result
  contextDefEq : ∀ {env U Γ₁ Γ₂ s i e₁ e₂ result},
    VEnv.WF env → env.IsDefEqCtx U [] Γ₁ Γ₂ →
      env.IsDefEqU U Γ₁ e₁ e₂ → R Γ₁ s i e₁ result →
        ∃ result', R Γ₂ s i e₂ result'
  wellFormed : ∀ {env U Δ Γ s i e result},
    R Δ s i e result → VExpr.WF env U Γ e →
      VExpr.WF env U Γ result
  unique : ∀ {env U Γ₁ Γ₂ s₁ s₂ i e₁ e₂ result₁ result₂},
    VEnv.WF env → env.IsDefEqCtx U [] Γ₁ Γ₂ →
      R Γ₁ s₁ i e₁ result₁ → R Γ₂ s₂ i e₂ result₂ →
        env.IsDefEqU U Γ₁ e₁ e₂ →
          env.IsDefEqU U Γ₁ result₁ result₂
  termSubstitution : ∀ {Γ₀ Γ₁ Γ s i e e' e₀ A₀ k},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → R Γ₁ s i e e' →
      R Γ s i (e.inst e₀ k) (e'.inst e₀ k)
  universeInstantiation : ∀ {U' Γ s i e e'} {ls : List VLevel},
    (∀ level ∈ ls, level.WF U') → R Γ s i e e' →
      R (Γ.map (VExpr.instL ls)) s i (e.instL ls) (e'.instL ls)

/-! ## Zero-field behavior -/

universe w

structure EmptyRecord (α : Type w) where

def emptyRecordCtor : VConstVal :=
  ⟨vconst(type_of% @EmptyRecord.mk), ``EmptyRecord.mk⟩

def emptyRecordType : VInductiveType where
  name := ``EmptyRecord
  uvars := 1
  type := vconst(type_of% @EmptyRecord).type
  ctors := [emptyRecordCtor]

def emptyRecordDecl : VInductDecl :=
  ⟨1, 1, [emptyRecordType]⟩

example : emptyRecordDecl.checked?.isSome = true := rfl

def emptyRecordChecked : emptyRecordDecl.Checked :=
  emptyRecordDecl.checked?.get (by decide)

def emptyRecordGeneration : emptyRecordDecl.GenerationChecked :=
  emptyRecordChecked.identityGeneration

def emptyRecordView : VStructureView where
  source := emptyRecordDecl
  generation := emptyRecordGeneration
  constructor := emptyRecordGeneration.block.ctorPairs[0]
  constructor_eq := rfl
  raw_indices_eq := rfl
  checked_indices_eq := rfl
  recursive_eq := rfl
  fieldSorts := []
  fieldSorts_length := rfl

def emptyRecordEnv : VEnv :=
  (VEnv.empty.addInductGeneration emptyRecordGeneration).get (by decide)

theorem emptyRecord_add :
    VEnv.empty.addInductGeneration emptyRecordGeneration =
      some emptyRecordEnv := rfl

theorem emptyRecord_trace :
    Nonempty (VEnv.AddInductGenerationTrace VEnv.empty
      emptyRecordEnv emptyRecordGeneration) :=
  VEnv.addInductGeneration_trace emptyRecord_add

theorem emptyRecordDecl_wf : emptyRecordDecl.WF VEnv.empty := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = emptyRecordType :=
    List.mem_singleton.1 (by simpa [emptyRecordDecl] using hty)
  subst ty
  refine ⟨⟨⟨_, by type_tac⟩, trivial⟩, ?_⟩
  intro c hc
  have hc' : c = emptyRecordCtor := by
    simpa [emptyRecordType] using hc
  subst c
  constructor
  · simp [emptyRecordDecl, emptyRecordType, emptyRecordCtor,
      VInductDecl.fieldsWF, VInductDecl.ctorFields,
      VExpr.dropN]
  · simp [emptyRecordDecl, emptyRecordType, emptyRecordCtor,
      VInductDecl.ctorFields, VInductDecl.recFieldIdxs,
      VInductDecl.sortLevel, VExpr.dropN, VExpr.resultOf,
      VExpr.forallN, VExpr.liftTelN, VExpr.appArgs]
    exact .nil

theorem emptyRecordGeneration_wf :
    emptyRecordGeneration.WF VEnv.empty :=
  (emptyRecordChecked.wf_of_decl
    emptyRecordDecl_wf).identityGeneration .empty

theorem emptyRecord_generation_semantics :
    emptyRecordView.GenerationSemantics emptyRecordEnv := by
  rcases emptyRecord_trace with ⟨trace⟩
  exact .ofGenerationTrace emptyRecordGeneration_wf trace

theorem emptyRecord_registered : emptyRecordView.Registered emptyRecordEnv := by
  rcases emptyRecord_trace with ⟨trace⟩
  refine {
    family := trace.family_lookup
    constructor := ?_
    recursor := trace.rec_lookup
    rules := fun _ h => trace.rule_mem h }
  apply trace.ctor_lookup
  rw [← emptyRecordGeneration.rawCtors_eq]
  exact List.mem_map.2 ⟨emptyRecordView.constructor,
    by
      change emptyRecordView.constructor ∈
        emptyRecordView.generation.block.ctorPairs
      rw [emptyRecordView.constructor_eq]
      simp,
    rfl⟩

theorem emptyRecord_view_wf : emptyRecordView.WF emptyRecordEnv := by
  refine {
    toRegistered := emptyRecord_registered
    generationSemantics := emptyRecord_generation_semantics
    parameters := ⟨⟨_, by type_tac⟩, trivial⟩
    parameters_length := rfl
    fieldTelescope := .nil
    smallFields := ?_ }
  intro _ level hlevel
  change level ∈ ([] : List VLevel) at hlevel
  contradiction

example : emptyRecordView.fields = [] := rfl

example : emptyRecordView.projectionCodes [.param 0] [.bvar 0] = [] := rfl

theorem emptyRecord_project_none (idx : Nat) (major : VExpr) :
    emptyRecordView.project? [.param 0] [.bvar 0] idx major = none := by
  simp [VStructureView.project?, show
    emptyRecordView.projectionCodes [.param 0] [.bvar 0] = [] from rfl]

#guard_named_axioms Ix.Theory.Named.Tests.ProjectionExpressibility.dependentRecord_view_wf [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.Tests.ProjectionExpressibility.key_representable [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.Tests.ProjectionExpressibility.value_representable [
  propext,
  sorryAx,
  Classical.choice,
  Quot.sound]

#guard_named_axioms Ix.Theory.Named.Tests.ProjectionExpressibility.emptyRecord_project_none [propext, Classical.choice, Quot.sound]

end Ix.Theory.Named.Tests.ProjectionExpressibility
