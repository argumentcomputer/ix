/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Kernel.Verify.Audit.AxiomAudit
import Ix.Theory.Named.Verify.Environment.SingletonParityMatrix

open Ix.Theory (VLevel)

/-!
# Singleton environment replay inventory

This module is the sole public environment-facing inventory for singleton
parity.  A row packages the actual implementation map, the Theory input and
output environments, input alignment/order, and the proof-carrying inductive
transaction.  Consequently every row exposes final alignment and orderedness;
mere Theory generation is not enough to inhabit this structure.
-/

namespace Ix.Theory.Named.InductiveReplayFixtures

open Lean
open Ix.Theory.Named.InductiveFixtures

local instance instInhabitedVEnvParityReplay : Inhabited VEnv := ⟨.empty⟩

structure SingletonReplayArtifact where
  label : Name
  source : VInductDecl
  inputMap : ConstMap
  inputEnv : VEnv
  inputMapWF : inputMap.WF
  outputMap : ConstMap
  outputEnv : VEnv
  inputOrdered : inputEnv.Ordered
  transaction : AddInduct inputMap inputEnv source outputMap outputEnv
  aligned : Aligned .safe outputMap outputEnv

namespace SingletonReplayArtifact

theorem outputAligned (artifact : SingletonReplayArtifact) :
    Aligned .safe artifact.outputMap artifact.outputEnv := artifact.aligned

theorem outputOrdered (artifact : SingletonReplayArtifact) :
    artifact.outputEnv.Ordered := by
  obtain ⟨generation, generation_wf, transaction⟩ :=
    artifact.transaction.to_addInduct
  exact VEnv.addInductGeneration_WF artifact.inputOrdered generation_wf
    transaction

end SingletonReplayArtifact

/-! ## Reusable staging facts for fixed-family replays -/

/-- The raw family constant retained by a generation certificate is a type in
the replay input environment. -/
theorem replayRawFamilyWF07
    {source : VInductDecl} {generation : source.GenerationChecked}
    {inputEnv : VEnv} (generationWF : generation.WF inputEnv) :
    generation.block.sourceType.toVConstant.WF inputEnv := by
  show inputEnv.IsType generation.block.sourceType.uvars []
    generation.block.sourceType.type
  rw [generation.block.sourceType_uvars_eq]
  exact generationWF.rawFamily_isType

/-- The raw family insertion preserves ordering whenever the retained
generation certificate is well formed in the replay input environment. -/
theorem replayTypeEnv_ordered07
    {source : VInductDecl} {generation : source.GenerationChecked}
    {inputEnv typeEnv : VEnv}
    (inputOrdered : inputEnv.Ordered)
    (generationWF : generation.WF inputEnv)
    (addType : inputEnv.addConst generation.block.sourceType.name
      generation.block.sourceType.toVConstant = some typeEnv) :
    typeEnv.Ordered := by
  refine .const inputOrdered ?_ addType
  show inputEnv.IsType generation.block.sourceType.uvars []
    generation.block.sourceType.type
  rw [generation.block.sourceType_uvars_eq]
  exact generationWF.rawFamily_isType

/-- Each stored raw constructor is well formed immediately after the raw
family insertion.  Later constructor stages use monotonicity to transport
this certificate across earlier constructor insertions. -/
theorem replayRawCtorWF07
    {source : VInductDecl} {generation : source.GenerationChecked}
    {inputEnv typeEnv : VEnv}
    (generationWF : generation.WF inputEnv)
    (addType : inputEnv.addConst generation.block.sourceType.name
      generation.block.sourceType.toVConstant = some typeEnv)
    (raw : VConstVal) (hraw : raw ∈ generation.block.sourceType.ctors) :
    raw.toVConstant.WF typeEnv := by
  have hraw' : raw ∈ generation.block.ctorPairs.map (·.raw) := by
    rw [generation.rawCtors_eq]
    exact hraw
  obtain ⟨ctor, hctor, rfl⟩ := List.mem_map.1 hraw'
  show typeEnv.IsType ctor.raw.uvars [] ctor.raw.type
  rw [generation.ctor_uvars_eq hctor]
  exact generationWF.rawCtor_isType addType hctor

/-- The complete raw-constructor fold preserves ordering.  This includes the
zero-constructor case, where the fold is the identity. -/
theorem replayCtorEnv_ordered07
    {source : VInductDecl} {generation : source.GenerationChecked}
    {inputEnv typeEnv ctorEnv : VEnv}
    (generationWF : generation.WF inputEnv)
    (addType : inputEnv.addConst generation.block.sourceType.name
      generation.block.sourceType.toVConstant = some typeEnv)
    (typeOrdered : typeEnv.Ordered)
    (addCtors : List.foldlM
      (fun env (ctor : VConstVal) =>
        env.addConst ctor.name ctor.toVConstant)
      typeEnv generation.block.sourceType.ctors = some ctorEnv) :
    ctorEnv.Ordered := by
  have ctorWF : ∀ ctor ∈ generation.block.sourceType.ctors,
      ctor.toVConstant.WF typeEnv := by
    intro raw hraw
    exact replayRawCtorWF07 generationWF addType raw hraw
  exact VInductDecl.constFold_ordered
    generation.block.sourceType.ctors typeOrdered ctorWF addCtors

/-- Reconstruct the precise mixed-generation environment after the family and
constructor constants have been inserted.  Its recursor certificate is what
turns exact kernel recursor metadata into a `TrConstVal`. -/
theorem replayGenerationEnv07
    {source : VInductDecl} {generation : source.GenerationChecked}
    {inputEnv typeEnv ctorEnv : VEnv}
    (generationWF : generation.WF inputEnv)
    (addType : inputEnv.addConst generation.block.sourceType.name
      generation.block.sourceType.toVConstant = some typeEnv)
    (addCtors : List.foldlM
      (fun env (ctor : VConstVal) =>
        env.addConst ctor.name ctor.toVConstant)
      typeEnv generation.block.sourceType.ctors = some ctorEnv)
    (ctorOrdered : ctorEnv.Ordered) :
    VInductDecl.GenerationEnv generation ctorEnv := by
  obtain ⟨typeToCtor, ctorLookup, -⟩ :=
    VInductDecl.ctorFold_spec generation.block.sourceType.ctors addCtors
  have inputToType := VEnv.addConst_le addType
  have inputToCtor := inputToType.trans typeToCtor
  have familyLookup : ctorEnv.constants
      generation.block.sourceType.name =
      some generation.block.sourceType.toVConstant :=
    typeToCtor.constants (VEnv.addConst_self addType)
  have constructorsLookup : ∀ ctor ∈ generation.block.ctorPairs,
      ctorEnv.constants ctor.raw.name = some ctor.raw.toVConstant := by
    intro ctor hctor
    apply ctorLookup ctor.raw
    rw [← generation.rawCtors_eq]
    exact List.mem_map.2 ⟨ctor, hctor, rfl⟩
  exact generationWF.toGenerationEnv addType inputToCtor typeToCtor
    ctorOrdered familyLookup constructorsLookup

/-! ## Replays already established by the completed singleton pipeline -/

def natReplay07 : SingletonReplayArtifact where
  label := ``Nat
  source := natDecl
  inputMap := {}
  inputEnv := .empty
  inputMapWF := SMap.WF.empty
  outputMap := natMap
  outputEnv := natFinalEnv
  inputOrdered := .empty
  transaction := nat_addInduct
  aligned := nat_aligned

def eqReplay07 : SingletonReplayArtifact where
  label := ``Eq
  source := eqDecl
  inputMap := {}
  inputEnv := .empty
  inputMapWF := SMap.WF.empty
  outputMap := eqMap
  outputEnv := eqFinalEnv
  inputOrdered := .empty
  transaction := eq_addInduct
  aligned := eq_aligned

def accReplay07 : SingletonReplayArtifact where
  label := ``Acc
  source := accDecl
  inputMap := {}
  inputEnv := .empty
  inputMapWF := SMap.WF.empty
  outputMap := accMap
  outputEnv := accFinalEnv
  inputOrdered := .empty
  transaction := acc_addInduct
  aligned := acc_aligned

def aliasFormerReplay07 : SingletonReplayArtifact where
  label := ``AliasFormer
  source := aliasFormerRawDecl
  inputMap := typeFamilyAliasMap
  inputEnv := typeFamilyAliasEnv
  inputMapWF := typeFamilyAliasMap_wf
  outputMap := aliasFormerMap
  outputEnv := aliasFormerFinalEnv
  inputOrdered := typeFamilyAliasEnv_ordered
  transaction := aliasFormer_addInduct_checked
  aligned := aliasFormer_aligned_checked

def aliasRecReplay07 : SingletonReplayArtifact where
  label := ``AliasRec
  source := aliasRecRawDecl
  inputMap := recAliasMap
  inputEnv := recAliasEnv
  inputMapWF := recAliasMap_wf
  outputMap := aliasRecMap
  outputEnv := aliasRecFinalEnv
  inputOrdered := recAliasEnv_ordered
  transaction := aliasRec_addInduct_checked
  aligned := aliasRec_aligned_checked

def normalizationMatrixReplay07 : SingletonReplayArtifact where
  label := ``NormalizationMatrix
  source := normalizationMatrixRawDecl
  inputMap := matrixAliasMap
  inputEnv := normalizationMatrixAliasEnv
  inputMapWF := matrixAliasMap_wf
  outputMap := normalizationMatrixMap
  outputEnv := normalizationMatrixFinalEnv
  inputOrdered := normalizationMatrixAliasEnv_ordered
  transaction := normalizationMatrix_addInduct
  aligned := normalizationMatrix_aligned

def annotatedPiReplay07 : SingletonReplayArtifact where
  label := ``AnnotatedPi
  source := annotatedPiRawDecl
  inputMap := _
  inputEnv := outParamEnv
  inputMapWF := annotatedReplayInputMap_wf
  outputMap := _
  outputEnv := annotatedPiFinalEnv
  inputOrdered := outParamEnv_ordered
  transaction := annotatedPi_addInduct_checked
  aligned := annotatedPi_aligned_checked

def annotatedParamReplay07 : SingletonReplayArtifact where
  label := ``AnnotatedParam
  source := annotatedParamRawDecl
  inputMap := _
  inputEnv := outParamEnv
  inputMapWF := annotatedReplayInputMap_wf
  outputMap := _
  outputEnv := annotatedParamFinalEnv
  inputOrdered := outParamEnv_ordered
  transaction := annotatedParam_addInduct_checked
  aligned := annotatedParam_aligned_checked

/-! ## Fixed-family replays -/

/-! ### Bool -/

theorem boolDeclWF07 : boolDecl.WF VEnv.empty := by
  refine ⟨rfl, ?_⟩
  intro type htype
  have htype' : type = boolType :=
    List.mem_singleton.1 (by simpa [boolDecl] using htype)
  subst type
  refine ⟨?_, ?_⟩
  · change True
    trivial
  · intro ctor hctor
    rcases List.mem_cons.1 hctor with rfl | hctor
    · constructor
      · change True
        trivial
      · exact .nil
    · have hctor' := List.mem_singleton.1 hctor
      subst ctor
      constructor
      · change True
        trivial
      · exact .nil

theorem boolGenerationWF07 : boolGenerationChecked.WF VEnv.empty := by
  exact (boolChecked.wf_of_decl boolDeclWF07).identityGeneration .empty

def boolTypeEnv07 : VEnv :=
  (VEnv.empty.addConst boolType.name boolType.toVConstant).get!

def boolFalseEnv07 : VEnv :=
  (boolTypeEnv07.addConst boolType.ctors[0].name
    boolType.ctors[0].toVConstant).get!

def boolCtorEnv07 : VEnv :=
  (boolFalseEnv07.addConst boolType.ctors[1].name
    boolType.ctors[1].toVConstant).get!

def boolRecEnv07 : VEnv :=
  (boolCtorEnv07.addConst ``Bool.rec
    (inductGenerationRecVal boolGenerationChecked).toVConstant).get!

def boolFinalEnv07 : VEnv :=
  boolGenerationChecked.generatedRules.foldl VEnv.addDefEq boolRecEnv07

def boolTypeMap07 : ConstMap :=
  ({} : ConstMap).insert ``Bool boolInfo07

def boolFalseMap07 : ConstMap :=
  boolTypeMap07.insert ``Bool.false boolFalseInfo07

def boolCtorMap07 : ConstMap :=
  boolFalseMap07.insert ``Bool.true boolTrueInfo07

def boolMap07 : ConstMap :=
  boolCtorMap07.insert ``Bool.rec boolRecInfo07

theorem boolTypeEnv_ordered07 : boolTypeEnv07.Ordered :=
  replayTypeEnv_ordered07 .empty boolGenerationWF07 rfl

theorem boolCtorEnv_ordered07 : boolCtorEnv07.Ordered :=
  replayCtorEnv_ordered07 boolGenerationWF07 rfl
    boolTypeEnv_ordered07 rfl

theorem boolGenerationEnv07 :
    VInductDecl.GenerationEnv boolGenerationChecked boolCtorEnv07 :=
  replayGenerationEnv07 boolGenerationWF07 rfl rfl
    boolCtorEnv_ordered07

theorem boolInfoTr07 :
    TrConstVal .safe VEnv.empty boolInfo07 boolType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  exact .sort rfl

theorem boolFalseInfoTr07 :
    TrConstVal .safe boolTypeEnv07 boolFalseInfo07 boolType.ctors[0] := by
  have hBool : boolTypeEnv07.constants ``Bool =
      some boolType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr boolTypeEnv07 boolFalseInfo07.levelParams []
      boolFalseInfo07.type boolType.ctors[0].type := by
    tr_type_expr_tac
  exact shape.to_trExprS boolTypeEnv_ordered07 trivial
    ⟨.sort (.succ .zero), by type_tac⟩

theorem boolTrueInfoTr07 :
    TrConstVal .safe boolFalseEnv07 boolTrueInfo07 boolType.ctors[1] := by
  have hBool : boolFalseEnv07.constants ``Bool =
      some boolType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr boolFalseEnv07 boolTrueInfo07.levelParams []
      boolTrueInfo07.type boolType.ctors[1].type := by
    tr_type_expr_tac
  have falseOrdered : boolFalseEnv07.Ordered := by
    refine .const (n := boolType.ctors[0].name)
      (ci := boolType.ctors[0].toVConstant) boolTypeEnv_ordered07 ?_ rfl
    exact ⟨.succ .zero, by type_tac⟩
  exact shape.to_trExprS falseOrdered trivial
    ⟨.sort (.succ .zero), by type_tac⟩

theorem boolRecInfoTr07 :
    TrConstVal .safe boolCtorEnv07 boolRecInfo07
      (inductGenerationRecVal boolGenerationChecked) := by
  have hBool : boolCtorEnv07.constants ``Bool =
      some boolType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr boolCtorEnv07 boolRecInfo07.levelParams []
      boolRecInfo07.type
      (inductGenerationRecVal boolGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨sort, recursorType⟩ := boolGenerationEnv07.recursor_wf
  exact shape.to_trExprS boolCtorEnv_ordered07 trivial
    ⟨.sort sort, recursorType⟩

theorem boolTypeFresh07 : ({} : ConstMap).find? ``Bool = none := by
  simp [SMap.find?]

theorem boolTypeMapWF07 : boolTypeMap07.WF :=
  SMap.WF.empty.insert _ _ boolTypeFresh07

theorem boolFalseFresh07 : boolTypeMap07.find? ``Bool.false = none := by
  rw [boolTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem boolFalseMapWF07 : boolFalseMap07.WF :=
  boolTypeMapWF07.insert _ _ boolFalseFresh07

theorem boolTrueFresh07 : boolFalseMap07.find? ``Bool.true = none := by
  rw [boolFalseMap07, boolTypeMapWF07.find?_insert, boolTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem boolCtorMapWF07 : boolCtorMap07.WF :=
  boolFalseMapWF07.insert _ _ boolTrueFresh07

theorem boolRecFresh07 : boolCtorMap07.find? ``Bool.rec = none := by
  rw [boolCtorMap07, boolFalseMapWF07.find?_insert, boolFalseMap07,
    boolTypeMapWF07.find?_insert, boolTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem boolAddInduct07 : AddInduct ({} : ConstMap) VEnv.empty boolDecl
    boolMap07 boolFinalEnv07 := by
  refine ⟨{
    generation := boolGenerationChecked
    generation_wf := boolGenerationWF07
    typeMap := boolTypeMap07
    typeEnv := boolTypeEnv07
    ctorMap := boolCtorMap07
    ctorEnv := boolCtorEnv07
    recEnv := boolRecEnv07
    addType := {
      info := boolInfo07
      kind_eq := by simp [boolInfo07, InductConstantKind.Matches]
      tr := boolInfoTr07
      map_fresh := boolTypeFresh07
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := boolRecInfo07
      kind_eq := by simp [boolRecInfo07, InductConstantKind.Matches]
      tr := boolRecInfoTr07
      map_fresh := boolRecFresh07
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
      info := boolFalseInfo07
      kind_eq := by simp [boolFalseInfo07, InductConstantKind.Matches]
      tr := boolFalseInfoTr07
      map_fresh := by simpa [boolType] using boolFalseFresh07
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := boolTrueInfo07
      kind_eq := by simp [boolTrueInfo07, InductConstantKind.Matches]
      tr := boolTrueInfoTr07
      map_fresh := by
        change boolFalseMap07.find? ``Bool.true = none
        exact boolTrueFresh07
      env_add := rfl
      map_add := rfl } .nil)

theorem boolAligned07 : Aligned .safe boolMap07 boolFinalEnv07 :=
  Aligned.addInduct boolAddInduct07 .empty

def boolReplay07 : SingletonReplayArtifact where
  label := ``Bool
  source := boolDecl
  inputMap := {}
  inputEnv := .empty
  inputMapWF := SMap.WF.empty
  outputMap := boolMap07
  outputEnv := boolFinalEnv07
  inputOrdered := .empty
  transaction := boolAddInduct07
  aligned := boolAligned07

/-! ### List -/

theorem listCheckedWF07 : listChecked.WF VEnv.empty := by
  constructor
  · change VEnv.empty.OnTel 1 [] [.sort (.succ (.param 0))]
    exact ⟨⟨.succ (.succ (.param 0)), VEnv.HasType.sort (by decide)⟩,
      trivial⟩
  · intro ctor hctor
    rcases List.mem_cons.1 hctor with rfl | hctor
    · constructor
      · change True
        trivial
      · exact .nil
    · have hctor' := List.mem_singleton.1 hctor
      subst ctor
      constructor
      · change VInductDecl.fieldsWF 1 ``List 1 VEnv.empty
          (.succ (.param 0)) [] [.sort (.succ (.param 0))] 0
          [.bvar 0,
            .app (.const ``List [.param 0]) (.bvar 1)]
        constructor
        · exact .inr (.inr ⟨rfl, .succ (.param 0), by type_tac,
            .inr (VLevel.le_refl _)⟩)
        constructor
        · intro recursive
          contradiction
        constructor
        · exact .inl rfl
        constructor
        · intro _
          exact .nil
        · trivial
      · exact .nil

theorem listGenerationWF07 : listGenerationChecked.WF VEnv.empty := by
  exact listCheckedWF07.identityGeneration .empty

def listTypeEnv07 : VEnv :=
  (VEnv.empty.addConst listType.name listType.toVConstant).get!

def listNilEnv07 : VEnv :=
  (listTypeEnv07.addConst listType.ctors[0].name
    listType.ctors[0].toVConstant).get!

def listCtorEnv07 : VEnv :=
  (listNilEnv07.addConst listType.ctors[1].name
    listType.ctors[1].toVConstant).get!

def listRecEnv07 : VEnv :=
  (listCtorEnv07.addConst ``List.rec
    (inductGenerationRecVal listGenerationChecked).toVConstant).get!

def listFinalEnv07 : VEnv :=
  listGenerationChecked.generatedRules.foldl VEnv.addDefEq listRecEnv07

def listTypeMap07 : ConstMap :=
  ({} : ConstMap).insert ``List listInfo07

def listNilMap07 : ConstMap :=
  listTypeMap07.insert ``List.nil listNilInfo07

def listCtorMap07 : ConstMap :=
  listNilMap07.insert ``List.cons listConsInfo07

def listMap07 : ConstMap :=
  listCtorMap07.insert ``List.rec listRecInfo07

theorem listTypeEnv_ordered07 : listTypeEnv07.Ordered :=
  replayTypeEnv_ordered07 .empty listGenerationWF07 rfl

theorem listNilEnv_ordered07 : listNilEnv07.Ordered := by
  refine .const (n := listType.ctors[0].name)
    (ci := listType.ctors[0].toVConstant) listTypeEnv_ordered07 ?_ rfl
  exact replayRawCtorWF07 listGenerationWF07 rfl listType.ctors[0]
    (.head _)

theorem listCtorEnv_ordered07 : listCtorEnv07.Ordered :=
  replayCtorEnv_ordered07 listGenerationWF07 rfl
    listTypeEnv_ordered07 rfl

theorem listGenerationEnv07 :
    VInductDecl.GenerationEnv listGenerationChecked listCtorEnv07 :=
  replayGenerationEnv07 listGenerationWF07 rfl rfl
    listCtorEnv_ordered07

theorem listInfoTr07 :
    TrConstVal .safe VEnv.empty listInfo07 listType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr VEnv.empty listInfo07.levelParams []
      listInfo07.type listType.type := by
    tr_type_expr_tac
  obtain ⟨sort, familyType⟩ := replayRawFamilyWF07 listGenerationWF07
  exact shape.to_trExprS .empty trivial ⟨.sort sort, familyType⟩

theorem listNilInfoTr07 :
    TrConstVal .safe listTypeEnv07 listNilInfo07 listType.ctors[0] := by
  have hList : listTypeEnv07.constants ``List =
      some listType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr listTypeEnv07 listNilInfo07.levelParams []
      listNilInfo07.type listType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨sort, ctorType⟩ := replayRawCtorWF07 listGenerationWF07 rfl
    listType.ctors[0] (.head _)
  exact shape.to_trExprS listTypeEnv_ordered07 trivial
    ⟨.sort sort, ctorType⟩

theorem listConsInfoTr07 :
    TrConstVal .safe listNilEnv07 listConsInfo07 listType.ctors[1] := by
  have hList : listNilEnv07.constants ``List =
      some listType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr listNilEnv07 listConsInfo07.levelParams []
      listConsInfo07.type listType.ctors[1].type := by
    tr_type_expr_tac
  obtain ⟨sort, ctorType⟩ := replayRawCtorWF07 listGenerationWF07 rfl
    listType.ctors[1] (.tail _ (.head _))
  have typeToNil : listTypeEnv07 ≤ listNilEnv07 :=
    VEnv.addConst_le (show listTypeEnv07.addConst
      listType.ctors[0].name listType.ctors[0].toVConstant =
        some listNilEnv07 from rfl)
  exact shape.to_trExprS listNilEnv_ordered07 trivial
    ⟨.sort sort, ctorType.mono typeToNil⟩

theorem listRecInfoTr07 :
    TrConstVal .safe listCtorEnv07 listRecInfo07
      (inductGenerationRecVal listGenerationChecked) := by
  have hList : listCtorEnv07.constants ``List =
      some listType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr listCtorEnv07 listRecInfo07.levelParams []
      listRecInfo07.type
      (inductGenerationRecVal listGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨sort, recursorType⟩ := listGenerationEnv07.recursor_wf
  exact shape.to_trExprS listCtorEnv_ordered07 trivial
    ⟨.sort sort, recursorType⟩

theorem listTypeFresh07 : ({} : ConstMap).find? ``List = none := by
  simp [SMap.find?]

theorem listTypeMapWF07 : listTypeMap07.WF :=
  SMap.WF.empty.insert _ _ listTypeFresh07

theorem listNilFresh07 : listTypeMap07.find? ``List.nil = none := by
  rw [listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem listNilMapWF07 : listNilMap07.WF :=
  listTypeMapWF07.insert _ _ listNilFresh07

theorem listConsFresh07 : listNilMap07.find? ``List.cons = none := by
  rw [listNilMap07, listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem listCtorMapWF07 : listCtorMap07.WF :=
  listNilMapWF07.insert _ _ listConsFresh07

theorem listRecFresh07 : listCtorMap07.find? ``List.rec = none := by
  rw [listCtorMap07, listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem listAddInduct07 : AddInduct ({} : ConstMap) VEnv.empty listDecl
    listMap07 listFinalEnv07 := by
  refine ⟨{
    generation := listGenerationChecked
    generation_wf := listGenerationWF07
    typeMap := listTypeMap07
    typeEnv := listTypeEnv07
    ctorMap := listCtorMap07
    ctorEnv := listCtorEnv07
    recEnv := listRecEnv07
    addType := {
      info := listInfo07
      kind_eq := by simp [listInfo07, InductConstantKind.Matches]
      tr := listInfoTr07
      map_fresh := listTypeFresh07
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := listRecInfo07
      kind_eq := by simp [listRecInfo07, InductConstantKind.Matches]
      tr := listRecInfoTr07
      map_fresh := listRecFresh07
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
      info := listNilInfo07
      kind_eq := by simp [listNilInfo07, InductConstantKind.Matches]
      tr := listNilInfoTr07
      map_fresh := by simpa [listType] using listNilFresh07
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := listConsInfo07
      kind_eq := by simp [listConsInfo07, InductConstantKind.Matches]
      tr := listConsInfoTr07
      map_fresh := by
        change listNilMap07.find? ``List.cons = none
        exact listConsFresh07
      env_add := rfl
      map_add := rfl } .nil)

theorem listAligned07 : Aligned .safe listMap07 listFinalEnv07 :=
  Aligned.addInduct listAddInduct07 .empty

def listReplay07 : SingletonReplayArtifact where
  label := ``List
  source := listDecl
  inputMap := {}
  inputEnv := .empty
  inputMapWF := SMap.WF.empty
  outputMap := listMap07
  outputEnv := listFinalEnv07
  inputOrdered := .empty
  transaction := listAddInduct07
  aligned := listAligned07

/-! ### Option -/

theorem optionDeclWF07 : optionDecl.WF VEnv.empty := by
  refine ⟨rfl, ?_⟩
  intro type htype
  have htype' : type = optionType :=
    List.mem_singleton.1 (by simpa [optionDecl] using htype)
  subst type
  refine ⟨?_, ?_⟩
  · change VEnv.empty.OnTel 1 [] [.sort (.succ (.param 0))]
    exact ⟨⟨.succ (.succ (.param 0)), VEnv.HasType.sort (by decide)⟩,
      trivial⟩
  · intro ctor hctor
    rcases List.mem_cons.1 hctor with rfl | hctor
    · constructor
      · change True
        trivial
      · exact .nil
    · have hctor' := List.mem_singleton.1 hctor
      subst ctor
      constructor
      · change VInductDecl.fieldsWF 1 ``Option 1 VEnv.empty
          (.succ (.param 0)) [] [.sort (.succ (.param 0))] 0 [.bvar 0]
        constructor
        · exact .inr (.inr ⟨rfl, .succ (.param 0), by type_tac,
            .inr (VLevel.le_refl _)⟩)
        constructor
        · intro recursive
          contradiction
        · trivial
      · exact .nil

theorem optionGenerationWF07 : optionGenerationChecked.WF VEnv.empty := by
  exact (optionChecked.wf_of_decl optionDeclWF07).identityGeneration .empty

def optionTypeEnv07 : VEnv :=
  (VEnv.empty.addConst optionType.name optionType.toVConstant).get!

def optionNoneEnv07 : VEnv :=
  (optionTypeEnv07.addConst optionType.ctors[0].name
    optionType.ctors[0].toVConstant).get!

def optionCtorEnv07 : VEnv :=
  (optionNoneEnv07.addConst optionType.ctors[1].name
    optionType.ctors[1].toVConstant).get!

def optionRecEnv07 : VEnv :=
  (optionCtorEnv07.addConst ``Option.rec
    (inductGenerationRecVal optionGenerationChecked).toVConstant).get!

def optionFinalEnv07 : VEnv :=
  optionGenerationChecked.generatedRules.foldl VEnv.addDefEq optionRecEnv07

def optionTypeMap07 : ConstMap :=
  ({} : ConstMap).insert ``Option optionInfo07

def optionNoneMap07 : ConstMap :=
  optionTypeMap07.insert ``Option.none optionNoneInfo07

def optionCtorMap07 : ConstMap :=
  optionNoneMap07.insert ``Option.some optionSomeInfo07

def optionMap07 : ConstMap :=
  optionCtorMap07.insert ``Option.rec optionRecInfo07

theorem optionTypeEnv_ordered07 : optionTypeEnv07.Ordered :=
  replayTypeEnv_ordered07 .empty optionGenerationWF07 rfl

theorem optionNoneEnv_ordered07 : optionNoneEnv07.Ordered := by
  refine .const (n := optionType.ctors[0].name)
    (ci := optionType.ctors[0].toVConstant) optionTypeEnv_ordered07 ?_ rfl
  exact replayRawCtorWF07 optionGenerationWF07 rfl optionType.ctors[0]
    (.head _)

theorem optionCtorEnv_ordered07 : optionCtorEnv07.Ordered :=
  replayCtorEnv_ordered07 optionGenerationWF07 rfl
    optionTypeEnv_ordered07 rfl

theorem optionGenerationEnv07 :
    VInductDecl.GenerationEnv optionGenerationChecked optionCtorEnv07 :=
  replayGenerationEnv07 optionGenerationWF07 rfl rfl
    optionCtorEnv_ordered07

theorem optionInfoTr07 :
    TrConstVal .safe VEnv.empty optionInfo07 optionType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr VEnv.empty optionInfo07.levelParams []
      optionInfo07.type optionType.type := by
    tr_type_expr_tac
  obtain ⟨sort, familyType⟩ := replayRawFamilyWF07 optionGenerationWF07
  exact shape.to_trExprS .empty trivial ⟨.sort sort, familyType⟩

theorem optionNoneInfoTr07 :
    TrConstVal .safe optionTypeEnv07 optionNoneInfo07 optionType.ctors[0] := by
  have hOption : optionTypeEnv07.constants ``Option =
      some optionType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr optionTypeEnv07 optionNoneInfo07.levelParams []
      optionNoneInfo07.type optionType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨sort, ctorType⟩ := replayRawCtorWF07 optionGenerationWF07 rfl
    optionType.ctors[0] (.head _)
  exact shape.to_trExprS optionTypeEnv_ordered07 trivial
    ⟨.sort sort, ctorType⟩

theorem optionSomeInfoTr07 :
    TrConstVal .safe optionNoneEnv07 optionSomeInfo07 optionType.ctors[1] := by
  have hOption : optionNoneEnv07.constants ``Option =
      some optionType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr optionNoneEnv07 optionSomeInfo07.levelParams []
      optionSomeInfo07.type optionType.ctors[1].type := by
    tr_type_expr_tac
  obtain ⟨sort, ctorType⟩ := replayRawCtorWF07 optionGenerationWF07 rfl
    optionType.ctors[1] (.tail _ (.head _))
  have typeToNone : optionTypeEnv07 ≤ optionNoneEnv07 :=
    VEnv.addConst_le (show optionTypeEnv07.addConst
      optionType.ctors[0].name optionType.ctors[0].toVConstant =
        some optionNoneEnv07 from rfl)
  exact shape.to_trExprS optionNoneEnv_ordered07 trivial
    ⟨.sort sort, ctorType.mono typeToNone⟩

theorem optionRecInfoTr07 :
    TrConstVal .safe optionCtorEnv07 optionRecInfo07
      (inductGenerationRecVal optionGenerationChecked) := by
  have hOption : optionCtorEnv07.constants ``Option =
      some optionType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr optionCtorEnv07 optionRecInfo07.levelParams []
      optionRecInfo07.type
      (inductGenerationRecVal optionGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨sort, recursorType⟩ := optionGenerationEnv07.recursor_wf
  exact shape.to_trExprS optionCtorEnv_ordered07 trivial
    ⟨.sort sort, recursorType⟩

theorem optionTypeFresh07 : ({} : ConstMap).find? ``Option = none := by
  simp [SMap.find?]

theorem optionTypeMapWF07 : optionTypeMap07.WF :=
  SMap.WF.empty.insert _ _ optionTypeFresh07

theorem optionNoneFresh07 : optionTypeMap07.find? ``Option.none = none := by
  rw [optionTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem optionNoneMapWF07 : optionNoneMap07.WF :=
  optionTypeMapWF07.insert _ _ optionNoneFresh07

theorem optionSomeFresh07 : optionNoneMap07.find? ``Option.some = none := by
  rw [optionNoneMap07, optionTypeMapWF07.find?_insert, optionTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem optionCtorMapWF07 : optionCtorMap07.WF :=
  optionNoneMapWF07.insert _ _ optionSomeFresh07

theorem optionRecFresh07 : optionCtorMap07.find? ``Option.rec = none := by
  rw [optionCtorMap07, optionNoneMapWF07.find?_insert, optionNoneMap07,
    optionTypeMapWF07.find?_insert, optionTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem optionAddInduct07 : AddInduct ({} : ConstMap) VEnv.empty optionDecl
    optionMap07 optionFinalEnv07 := by
  refine ⟨{
    generation := optionGenerationChecked
    generation_wf := optionGenerationWF07
    typeMap := optionTypeMap07
    typeEnv := optionTypeEnv07
    ctorMap := optionCtorMap07
    ctorEnv := optionCtorEnv07
    recEnv := optionRecEnv07
    addType := {
      info := optionInfo07
      kind_eq := by simp [optionInfo07, InductConstantKind.Matches]
      tr := optionInfoTr07
      map_fresh := optionTypeFresh07
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := optionRecInfo07
      kind_eq := by simp [optionRecInfo07, InductConstantKind.Matches]
      tr := optionRecInfoTr07
      map_fresh := optionRecFresh07
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
      info := optionNoneInfo07
      kind_eq := by simp [optionNoneInfo07, InductConstantKind.Matches]
      tr := optionNoneInfoTr07
      map_fresh := by simpa [optionType] using optionNoneFresh07
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := optionSomeInfo07
      kind_eq := by simp [optionSomeInfo07, InductConstantKind.Matches]
      tr := optionSomeInfoTr07
      map_fresh := by
        change optionNoneMap07.find? ``Option.some = none
        exact optionSomeFresh07
      env_add := rfl
      map_add := rfl } .nil)

theorem optionAligned07 : Aligned .safe optionMap07 optionFinalEnv07 :=
  Aligned.addInduct optionAddInduct07 .empty

def optionReplay07 : SingletonReplayArtifact where
  label := ``Option
  source := optionDecl
  inputMap := {}
  inputEnv := .empty
  inputMapWF := SMap.WF.empty
  outputMap := optionMap07
  outputEnv := optionFinalEnv07
  inputOrdered := .empty
  transaction := optionAddInduct07
  aligned := optionAligned07

/-! ### Prod -/

theorem prodCheckedWF07 : prodChecked.WF VEnv.empty := by
  constructor
  · change VEnv.empty.OnTel 2 []
      [.sort (.succ (.param 0)), .sort (.succ (.param 1))]
    exact ⟨⟨.succ (.succ (.param 0)), VEnv.HasType.sort (by decide)⟩,
      ⟨⟨.succ (.succ (.param 1)), VEnv.HasType.sort (by decide)⟩,
        trivial⟩⟩
  · intro ctor hctor
    have hctor' := List.mem_singleton.1 hctor
    subst ctor
    constructor
    · change VInductDecl.fieldsWF 2 ``Prod 2 VEnv.empty
        (.max (.succ (.param 0)) (.succ (.param 1))) []
        [.sort (.succ (.param 1)), .sort (.succ (.param 0))] 0
        [.bvar 1, .bvar 1]
      constructor
      · exact .inr (.inr ⟨rfl, .succ (.param 0), by type_tac,
          .inr VLevel.le_max_left⟩)
      constructor
      · intro recursive
        contradiction
      constructor
      · exact .inr (.inr ⟨rfl, .succ (.param 1), by type_tac,
          .inr VLevel.le_max_right⟩)
      constructor
      · intro recursive
        contradiction
      · trivial
    · exact .nil

theorem prodGenerationWF07 : prodGenerationChecked.WF VEnv.empty := by
  exact prodCheckedWF07.identityGeneration .empty

def prodTypeEnv07 : VEnv :=
  (VEnv.empty.addConst prodType.name prodType.toVConstant).get!

def prodCtorEnv07 : VEnv :=
  (prodTypeEnv07.addConst prodType.ctors[0].name
    prodType.ctors[0].toVConstant).get!

def prodRecEnv07 : VEnv :=
  (prodCtorEnv07.addConst ``Prod.rec
    (inductGenerationRecVal prodGenerationChecked).toVConstant).get!

def prodFinalEnv07 : VEnv :=
  prodGenerationChecked.generatedRules.foldl VEnv.addDefEq prodRecEnv07

def prodTypeMap07 : ConstMap :=
  ({} : ConstMap).insert ``Prod prodInfo07

def prodCtorMap07 : ConstMap :=
  prodTypeMap07.insert ``Prod.mk prodMkInfo07

def prodMap07 : ConstMap :=
  prodCtorMap07.insert ``Prod.rec prodRecInfo07

theorem prodTypeEnv_ordered07 : prodTypeEnv07.Ordered :=
  replayTypeEnv_ordered07 .empty prodGenerationWF07 rfl

theorem prodCtorEnv_ordered07 : prodCtorEnv07.Ordered :=
  replayCtorEnv_ordered07 prodGenerationWF07 rfl
    prodTypeEnv_ordered07 rfl

theorem prodGenerationEnv07 :
    VInductDecl.GenerationEnv prodGenerationChecked prodCtorEnv07 :=
  replayGenerationEnv07 prodGenerationWF07 rfl rfl
    prodCtorEnv_ordered07

theorem prodInfoTr07 :
    TrConstVal .safe VEnv.empty prodInfo07 prodType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr VEnv.empty prodInfo07.levelParams []
      prodInfo07.type prodType.type := by
    tr_type_expr_tac
  obtain ⟨sort, familyType⟩ := replayRawFamilyWF07 prodGenerationWF07
  exact shape.to_trExprS .empty trivial ⟨.sort sort, familyType⟩

theorem prodCtorInfoTr07 :
    TrConstVal .safe prodTypeEnv07 prodMkInfo07 prodType.ctors[0] := by
  have hProd : prodTypeEnv07.constants ``Prod =
      some prodType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr prodTypeEnv07 prodMkInfo07.levelParams []
      prodMkInfo07.type prodType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨sort, ctorType⟩ := replayRawCtorWF07 prodGenerationWF07 rfl
    prodType.ctors[0] (.head _)
  exact shape.to_trExprS prodTypeEnv_ordered07 trivial
    ⟨.sort sort, ctorType⟩

theorem prodRecInfoTr07 :
    TrConstVal .safe prodCtorEnv07 prodRecInfo07
      (inductGenerationRecVal prodGenerationChecked) := by
  have hProd : prodCtorEnv07.constants ``Prod =
      some prodType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr prodCtorEnv07 prodRecInfo07.levelParams []
      prodRecInfo07.type
      (inductGenerationRecVal prodGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨sort, recursorType⟩ := prodGenerationEnv07.recursor_wf
  exact shape.to_trExprS prodCtorEnv_ordered07 trivial
    ⟨.sort sort, recursorType⟩

theorem prodTypeFresh07 : ({} : ConstMap).find? ``Prod = none := by
  simp [SMap.find?]

theorem prodTypeMapWF07 : prodTypeMap07.WF :=
  SMap.WF.empty.insert _ _ prodTypeFresh07

theorem prodCtorFresh07 : prodTypeMap07.find? ``Prod.mk = none := by
  rw [prodTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem prodCtorMapWF07 : prodCtorMap07.WF :=
  prodTypeMapWF07.insert _ _ prodCtorFresh07

theorem prodRecFresh07 : prodCtorMap07.find? ``Prod.rec = none := by
  rw [prodCtorMap07, prodTypeMapWF07.find?_insert, prodTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem prodAddInduct07 : AddInduct ({} : ConstMap) VEnv.empty prodDecl
    prodMap07 prodFinalEnv07 := by
  refine ⟨{
    generation := prodGenerationChecked
    generation_wf := prodGenerationWF07
    typeMap := prodTypeMap07
    typeEnv := prodTypeEnv07
    ctorMap := prodCtorMap07
    ctorEnv := prodCtorEnv07
    recEnv := prodRecEnv07
    addType := {
      info := prodInfo07
      kind_eq := by simp [prodInfo07, InductConstantKind.Matches]
      tr := prodInfoTr07
      map_fresh := prodTypeFresh07
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := prodRecInfo07
      kind_eq := by simp [prodRecInfo07, InductConstantKind.Matches]
      tr := prodRecInfoTr07
      map_fresh := prodRecFresh07
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
    info := prodMkInfo07
    kind_eq := by simp [prodMkInfo07, InductConstantKind.Matches]
    tr := prodCtorInfoTr07
    map_fresh := by simpa [prodType] using prodCtorFresh07
    env_add := rfl
    map_add := rfl } .nil

theorem prodAligned07 : Aligned .safe prodMap07 prodFinalEnv07 :=
  Aligned.addInduct prodAddInduct07 .empty

def prodReplay07 : SingletonReplayArtifact where
  label := ``Prod
  source := prodDecl
  inputMap := {}
  inputEnv := .empty
  inputMapWF := SMap.WF.empty
  outputMap := prodMap07
  outputEnv := prodFinalEnv07
  inputOrdered := .empty
  transaction := prodAddInduct07
  aligned := prodAligned07

/-! ### And -/

theorem andCheckedWF07 : andChecked.WF VEnv.empty := by
  constructor
  · change VEnv.empty.OnTel 0 [] [.sort .zero, .sort .zero]
    exact ⟨⟨.succ .zero, VEnv.HasType.sort trivial⟩,
      ⟨⟨.succ .zero, VEnv.HasType.sort trivial⟩, trivial⟩⟩
  · intro ctor hctor
    have hctor' := List.mem_singleton.1 hctor
    subst ctor
    constructor
    · change VInductDecl.fieldsWF 0 ``And 2 VEnv.empty .zero []
        [.sort .zero, .sort .zero] 0 [.bvar 1, .bvar 1]
      constructor
      · exact .inr (.inr ⟨rfl, .zero, by type_tac, .inl rfl⟩)
      constructor
      · intro recursive
        contradiction
      constructor
      · exact .inr (.inr ⟨rfl, .zero, by type_tac, .inl rfl⟩)
      constructor
      · intro recursive
        contradiction
      · trivial
    · exact .nil

theorem andGenerationWF07 : andGenerationChecked.WF VEnv.empty := by
  exact andCheckedWF07.identityGeneration .empty

def andTypeEnv07 : VEnv :=
  (VEnv.empty.addConst andType.name andType.toVConstant).get!

def andCtorEnv07 : VEnv :=
  (andTypeEnv07.addConst andType.ctors[0].name
    andType.ctors[0].toVConstant).get!

def andRecEnv07 : VEnv :=
  (andCtorEnv07.addConst ``And.rec
    (inductGenerationRecVal andGenerationChecked).toVConstant).get!

def andFinalEnv07 : VEnv :=
  andGenerationChecked.generatedRules.foldl VEnv.addDefEq andRecEnv07

def andTypeMap07 : ConstMap :=
  ({} : ConstMap).insert ``And andInfo06

def andCtorMap07 : ConstMap :=
  andTypeMap07.insert ``And.intro andIntroInfo06

def andMap07 : ConstMap :=
  andCtorMap07.insert ``And.rec andRecInfo06

theorem andTypeEnv_ordered07 : andTypeEnv07.Ordered :=
  replayTypeEnv_ordered07 .empty andGenerationWF07 rfl

theorem andCtorEnv_ordered07 : andCtorEnv07.Ordered :=
  replayCtorEnv_ordered07 andGenerationWF07 rfl
    andTypeEnv_ordered07 rfl

theorem andGenerationEnv07 :
    VInductDecl.GenerationEnv andGenerationChecked andCtorEnv07 :=
  replayGenerationEnv07 andGenerationWF07 rfl rfl
    andCtorEnv_ordered07

theorem andInfoTr07 :
    TrConstVal .safe VEnv.empty andInfo06 andType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr VEnv.empty andInfo06.levelParams []
      andInfo06.type andType.type := by
    tr_type_expr_tac
  obtain ⟨sort, familyType⟩ := replayRawFamilyWF07 andGenerationWF07
  exact shape.to_trExprS .empty trivial ⟨.sort sort, familyType⟩

theorem andCtorInfoTr07 :
    TrConstVal .safe andTypeEnv07 andIntroInfo06 andType.ctors[0] := by
  have hAnd : andTypeEnv07.constants ``And =
      some andType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr andTypeEnv07 andIntroInfo06.levelParams []
      andIntroInfo06.type andType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨sort, ctorType⟩ := replayRawCtorWF07 andGenerationWF07 rfl
    andType.ctors[0] (.head _)
  exact shape.to_trExprS andTypeEnv_ordered07 trivial
    ⟨.sort sort, ctorType⟩

theorem andRecInfoTr07 :
    TrConstVal .safe andCtorEnv07 andRecInfo06
      (inductGenerationRecVal andGenerationChecked) := by
  have hAnd : andCtorEnv07.constants ``And =
      some andType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr andCtorEnv07 andRecInfo06.levelParams []
      andRecInfo06.type
      (inductGenerationRecVal andGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨sort, recursorType⟩ := andGenerationEnv07.recursor_wf
  exact shape.to_trExprS andCtorEnv_ordered07 trivial
    ⟨.sort sort, recursorType⟩

theorem andTypeFresh07 : ({} : ConstMap).find? ``And = none := by
  simp [SMap.find?]

theorem andTypeMapWF07 : andTypeMap07.WF :=
  SMap.WF.empty.insert _ _ andTypeFresh07

theorem andCtorFresh07 : andTypeMap07.find? ``And.intro = none := by
  rw [andTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem andCtorMapWF07 : andCtorMap07.WF :=
  andTypeMapWF07.insert _ _ andCtorFresh07

theorem andRecFresh07 : andCtorMap07.find? ``And.rec = none := by
  rw [andCtorMap07, andTypeMapWF07.find?_insert, andTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem andAddInduct07 : AddInduct ({} : ConstMap) VEnv.empty andDecl
    andMap07 andFinalEnv07 := by
  refine ⟨{
    generation := andGenerationChecked
    generation_wf := andGenerationWF07
    typeMap := andTypeMap07
    typeEnv := andTypeEnv07
    ctorMap := andCtorMap07
    ctorEnv := andCtorEnv07
    recEnv := andRecEnv07
    addType := {
      info := andInfo06
      kind_eq := by simp [andInfo06, InductConstantKind.Matches]
      tr := andInfoTr07
      map_fresh := andTypeFresh07
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := andRecInfo06
      kind_eq := by simp [andRecInfo06, InductConstantKind.Matches]
      tr := andRecInfoTr07
      map_fresh := andRecFresh07
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
    info := andIntroInfo06
    kind_eq := by simp [andIntroInfo06, InductConstantKind.Matches]
    tr := andCtorInfoTr07
    map_fresh := by simpa [andType] using andCtorFresh07
    env_add := rfl
    map_add := rfl } .nil

theorem andAligned07 : Aligned .safe andMap07 andFinalEnv07 :=
  Aligned.addInduct andAddInduct07 .empty

def andReplay07 : SingletonReplayArtifact where
  label := ``And
  source := andDecl
  inputMap := {}
  inputEnv := .empty
  inputMapWF := SMap.WF.empty
  outputMap := andMap07
  outputEnv := andFinalEnv07
  inputOrdered := .empty
  transaction := andAddInduct07
  aligned := andAligned07

/-! ### Or -/

theorem orCheckedWF07 : orChecked.WF VEnv.empty := by
  constructor
  · change VEnv.empty.OnTel 0 [] [.sort .zero, .sort .zero]
    exact ⟨⟨.succ .zero, VEnv.HasType.sort trivial⟩,
      ⟨⟨.succ .zero, VEnv.HasType.sort trivial⟩, trivial⟩⟩
  · intro ctor hctor
    rcases List.mem_cons.1 hctor with rfl | hctor
    · constructor
      · change VInductDecl.fieldsWF 0 ``Or 2 VEnv.empty .zero []
          [.sort .zero, .sort .zero] 0 [.bvar 1]
        constructor
        · exact .inr (.inr ⟨rfl, .zero, by type_tac, .inl rfl⟩)
        constructor
        · intro recursive
          contradiction
        · trivial
      · exact .nil
    · have hctor' := List.mem_singleton.1 hctor
      subst ctor
      constructor
      · change VInductDecl.fieldsWF 0 ``Or 2 VEnv.empty .zero []
          [.sort .zero, .sort .zero] 0 [.bvar 0]
        constructor
        · exact .inr (.inr ⟨rfl, .zero, by type_tac, .inl rfl⟩)
        constructor
        · intro recursive
          contradiction
        · trivial
      · exact .nil

theorem orGenerationWF07 : orGenerationChecked.WF VEnv.empty := by
  exact orCheckedWF07.identityGeneration .empty

def orTypeEnv07 : VEnv :=
  (VEnv.empty.addConst orType.name orType.toVConstant).get!

def orInlEnv07 : VEnv :=
  (orTypeEnv07.addConst orType.ctors[0].name
    orType.ctors[0].toVConstant).get!

def orCtorEnv07 : VEnv :=
  (orInlEnv07.addConst orType.ctors[1].name
    orType.ctors[1].toVConstant).get!

def orRecEnv07 : VEnv :=
  (orCtorEnv07.addConst ``Or.rec
    (inductGenerationRecVal orGenerationChecked).toVConstant).get!

def orFinalEnv07 : VEnv :=
  orGenerationChecked.generatedRules.foldl VEnv.addDefEq orRecEnv07

def orTypeMap07 : ConstMap :=
  ({} : ConstMap).insert ``Or orInfo06

def orInlMap07 : ConstMap :=
  orTypeMap07.insert ``Or.inl orInlInfo06

def orCtorMap07 : ConstMap :=
  orInlMap07.insert ``Or.inr orInrInfo06

def orMap07 : ConstMap :=
  orCtorMap07.insert ``Or.rec orRecInfo06

theorem orTypeEnv_ordered07 : orTypeEnv07.Ordered :=
  replayTypeEnv_ordered07 .empty orGenerationWF07 rfl

theorem orInlEnv_ordered07 : orInlEnv07.Ordered := by
  refine .const (n := orType.ctors[0].name)
    (ci := orType.ctors[0].toVConstant) orTypeEnv_ordered07 ?_ rfl
  exact replayRawCtorWF07 orGenerationWF07 rfl orType.ctors[0]
    (.head _)

theorem orCtorEnv_ordered07 : orCtorEnv07.Ordered :=
  replayCtorEnv_ordered07 orGenerationWF07 rfl
    orTypeEnv_ordered07 rfl

theorem orGenerationEnv07 :
    VInductDecl.GenerationEnv orGenerationChecked orCtorEnv07 :=
  replayGenerationEnv07 orGenerationWF07 rfl rfl
    orCtorEnv_ordered07

theorem orInfoTr07 :
    TrConstVal .safe VEnv.empty orInfo06 orType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr VEnv.empty orInfo06.levelParams []
      orInfo06.type orType.type := by
    tr_type_expr_tac
  obtain ⟨sort, familyType⟩ := replayRawFamilyWF07 orGenerationWF07
  exact shape.to_trExprS .empty trivial ⟨.sort sort, familyType⟩

theorem orInlInfoTr07 :
    TrConstVal .safe orTypeEnv07 orInlInfo06 orType.ctors[0] := by
  have hOr : orTypeEnv07.constants ``Or = some orType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr orTypeEnv07 orInlInfo06.levelParams []
      orInlInfo06.type orType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨sort, ctorType⟩ := replayRawCtorWF07 orGenerationWF07 rfl
    orType.ctors[0] (.head _)
  exact shape.to_trExprS orTypeEnv_ordered07 trivial
    ⟨.sort sort, ctorType⟩

theorem orInrInfoTr07 :
    TrConstVal .safe orInlEnv07 orInrInfo06 orType.ctors[1] := by
  have hOr : orInlEnv07.constants ``Or = some orType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr orInlEnv07 orInrInfo06.levelParams []
      orInrInfo06.type orType.ctors[1].type := by
    tr_type_expr_tac
  obtain ⟨sort, ctorType⟩ := replayRawCtorWF07 orGenerationWF07 rfl
    orType.ctors[1] (.tail _ (.head _))
  have typeToInl : orTypeEnv07 ≤ orInlEnv07 :=
    VEnv.addConst_le (show orTypeEnv07.addConst orType.ctors[0].name
      orType.ctors[0].toVConstant = some orInlEnv07 from rfl)
  exact shape.to_trExprS orInlEnv_ordered07 trivial
    ⟨.sort sort, ctorType.mono typeToInl⟩

theorem orRecInfoTr07 :
    TrConstVal .safe orCtorEnv07 orRecInfo06
      (inductGenerationRecVal orGenerationChecked) := by
  have hOr : orCtorEnv07.constants ``Or = some orType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr orCtorEnv07 orRecInfo06.levelParams []
      orRecInfo06.type
      (inductGenerationRecVal orGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨sort, recursorType⟩ := orGenerationEnv07.recursor_wf
  exact shape.to_trExprS orCtorEnv_ordered07 trivial
    ⟨.sort sort, recursorType⟩

theorem orTypeFresh07 : ({} : ConstMap).find? ``Or = none := by
  simp [SMap.find?]

theorem orTypeMapWF07 : orTypeMap07.WF :=
  SMap.WF.empty.insert _ _ orTypeFresh07

theorem orInlFresh07 : orTypeMap07.find? ``Or.inl = none := by
  rw [orTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem orInlMapWF07 : orInlMap07.WF :=
  orTypeMapWF07.insert _ _ orInlFresh07

theorem orInrFresh07 : orInlMap07.find? ``Or.inr = none := by
  rw [orInlMap07, orTypeMapWF07.find?_insert, orTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem orCtorMapWF07 : orCtorMap07.WF :=
  orInlMapWF07.insert _ _ orInrFresh07

theorem orRecFresh07 : orCtorMap07.find? ``Or.rec = none := by
  rw [orCtorMap07, orInlMapWF07.find?_insert, orInlMap07,
    orTypeMapWF07.find?_insert, orTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem orAddInduct07 : AddInduct ({} : ConstMap) VEnv.empty orDecl
    orMap07 orFinalEnv07 := by
  refine ⟨{
    generation := orGenerationChecked
    generation_wf := orGenerationWF07
    typeMap := orTypeMap07
    typeEnv := orTypeEnv07
    ctorMap := orCtorMap07
    ctorEnv := orCtorEnv07
    recEnv := orRecEnv07
    addType := {
      info := orInfo06
      kind_eq := by simp [orInfo06, InductConstantKind.Matches]
      tr := orInfoTr07
      map_fresh := orTypeFresh07
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := orRecInfo06
      kind_eq := by simp [orRecInfo06, InductConstantKind.Matches]
      tr := orRecInfoTr07
      map_fresh := orRecFresh07
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
      info := orInlInfo06
      kind_eq := by simp [orInlInfo06, InductConstantKind.Matches]
      tr := orInlInfoTr07
      map_fresh := by simpa [orType] using orInlFresh07
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := orInrInfo06
      kind_eq := by simp [orInrInfo06, InductConstantKind.Matches]
      tr := orInrInfoTr07
      map_fresh := by
        change orInlMap07.find? ``Or.inr = none
        exact orInrFresh07
      env_add := rfl
      map_add := rfl } .nil)

theorem orAligned07 : Aligned .safe orMap07 orFinalEnv07 :=
  Aligned.addInduct orAddInduct07 .empty

def orReplay07 : SingletonReplayArtifact where
  label := ``Or
  source := orDecl
  inputMap := {}
  inputEnv := .empty
  inputMapWF := SMap.WF.empty
  outputMap := orMap07
  outputEnv := orFinalEnv07
  inputOrdered := .empty
  transaction := orAddInduct07
  aligned := orAligned07

/-! ### HEq -/

theorem heqCheckedWF07 : heqChecked.WF VEnv.empty := by
  constructor
  · change VEnv.empty.OnTel 1 []
      [.sort (.param 0), .bvar 0, .sort (.param 0), .bvar 0]
    exact ⟨⟨.succ (.param 0), VEnv.HasType.sort (by decide)⟩,
      ⟨⟨.param 0, by type_tac⟩,
        ⟨⟨.succ (.param 0), VEnv.HasType.sort (by decide)⟩,
          ⟨⟨.param 0, by type_tac⟩, trivial⟩⟩⟩⟩
  · intro ctor hctor
    have hctor' := List.mem_singleton.1 hctor
    subst ctor
    constructor
    · change True
      trivial
    · change VEnv.empty.SpineWF 1 [.bvar 0, .sort (.param 0)]
        (.forallE (.sort (.param 0))
          (.forallE (.bvar 0) (.sort .zero)))
        [.bvar 1, .bvar 0] (.sort .zero)
      exact .cons (by type_tac) <| .cons (by type_tac) .nil

theorem heqGenerationWF07 : heqGenerationChecked.WF VEnv.empty := by
  exact heqCheckedWF07.identityGeneration .empty

def heqTypeEnv07 : VEnv :=
  (VEnv.empty.addConst heqType.name heqType.toVConstant).get!

def heqCtorEnv07 : VEnv :=
  (heqTypeEnv07.addConst heqType.ctors[0].name
    heqType.ctors[0].toVConstant).get!

def heqRecEnv07 : VEnv :=
  (heqCtorEnv07.addConst ``HEq.rec
    (inductGenerationRecVal heqGenerationChecked).toVConstant).get!

def heqFinalEnv07 : VEnv :=
  heqGenerationChecked.generatedRules.foldl VEnv.addDefEq heqRecEnv07

def heqTypeMap07 : ConstMap :=
  ({} : ConstMap).insert ``HEq heqInfo07

def heqCtorMap07 : ConstMap :=
  heqTypeMap07.insert ``HEq.refl heqReflInfo07

def heqMap07 : ConstMap :=
  heqCtorMap07.insert ``HEq.rec heqRecInfo07

theorem heqTypeEnv_ordered07 : heqTypeEnv07.Ordered :=
  replayTypeEnv_ordered07 .empty heqGenerationWF07 rfl

theorem heqCtorEnv_ordered07 : heqCtorEnv07.Ordered :=
  replayCtorEnv_ordered07 heqGenerationWF07 rfl
    heqTypeEnv_ordered07 rfl

theorem heqGenerationEnv07 :
    VInductDecl.GenerationEnv heqGenerationChecked heqCtorEnv07 :=
  replayGenerationEnv07 heqGenerationWF07 rfl rfl
    heqCtorEnv_ordered07

theorem heqInfoTr07 :
    TrConstVal .safe VEnv.empty heqInfo07 heqType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr VEnv.empty heqInfo07.levelParams []
      heqInfo07.type heqType.type := by
    tr_type_expr_tac
  obtain ⟨sort, familyType⟩ := replayRawFamilyWF07 heqGenerationWF07
  exact shape.to_trExprS .empty trivial ⟨.sort sort, familyType⟩

theorem heqCtorInfoTr07 :
    TrConstVal .safe heqTypeEnv07 heqReflInfo07 heqType.ctors[0] := by
  have hHEq : heqTypeEnv07.constants ``HEq =
      some heqType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr heqTypeEnv07 heqReflInfo07.levelParams []
      heqReflInfo07.type heqType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨sort, ctorType⟩ := replayRawCtorWF07 heqGenerationWF07 rfl
    heqType.ctors[0] (.head _)
  exact shape.to_trExprS heqTypeEnv_ordered07 trivial
    ⟨.sort sort, ctorType⟩

theorem heqRecInfoTr07 :
    TrConstVal .safe heqCtorEnv07 heqRecInfo07
      (inductGenerationRecVal heqGenerationChecked) := by
  have hHEq : heqCtorEnv07.constants ``HEq =
      some heqType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr heqCtorEnv07 heqRecInfo07.levelParams []
      heqRecInfo07.type
      (inductGenerationRecVal heqGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨sort, recursorType⟩ := heqGenerationEnv07.recursor_wf
  exact shape.to_trExprS heqCtorEnv_ordered07 trivial
    ⟨.sort sort, recursorType⟩

theorem heqTypeFresh07 : ({} : ConstMap).find? ``HEq = none := by
  simp [SMap.find?]

theorem heqTypeMapWF07 : heqTypeMap07.WF :=
  SMap.WF.empty.insert _ _ heqTypeFresh07

theorem heqCtorFresh07 : heqTypeMap07.find? ``HEq.refl = none := by
  rw [heqTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem heqCtorMapWF07 : heqCtorMap07.WF :=
  heqTypeMapWF07.insert _ _ heqCtorFresh07

theorem heqRecFresh07 : heqCtorMap07.find? ``HEq.rec = none := by
  rw [heqCtorMap07, heqTypeMapWF07.find?_insert, heqTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem heqAddInduct07 : AddInduct ({} : ConstMap) VEnv.empty heqDecl
    heqMap07 heqFinalEnv07 := by
  refine ⟨{
    generation := heqGenerationChecked
    generation_wf := heqGenerationWF07
    typeMap := heqTypeMap07
    typeEnv := heqTypeEnv07
    ctorMap := heqCtorMap07
    ctorEnv := heqCtorEnv07
    recEnv := heqRecEnv07
    addType := {
      info := heqInfo07
      kind_eq := by simp [heqInfo07, InductConstantKind.Matches]
      tr := heqInfoTr07
      map_fresh := heqTypeFresh07
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := heqRecInfo07
      kind_eq := by simp [heqRecInfo07, InductConstantKind.Matches]
      tr := heqRecInfoTr07
      map_fresh := heqRecFresh07
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
    info := heqReflInfo07
    kind_eq := by simp [heqReflInfo07, InductConstantKind.Matches]
    tr := heqCtorInfoTr07
    map_fresh := by simpa [heqType] using heqCtorFresh07
    env_add := rfl
    map_add := rfl } .nil

theorem heqAligned07 : Aligned .safe heqMap07 heqFinalEnv07 :=
  Aligned.addInduct heqAddInduct07 .empty

def heqReplay07 : SingletonReplayArtifact where
  label := ``HEq
  source := heqDecl
  inputMap := {}
  inputEnv := .empty
  inputMapWF := SMap.WF.empty
  outputMap := heqMap07
  outputEnv := heqFinalEnv07
  inputOrdered := .empty
  transaction := heqAddInduct07
  aligned := heqAligned07

/-! ### Fin dependency environment -/

def finLTInfo07 : ConstantInfo := kernelInductInfo% LT
def finLTMkInfo07 : ConstantInfo := kernelCtorInfo% LT.mk
def finLTLtInfo07 : ConstantInfo := .defnInfo (kernelDefVal% LT.lt)
def finInstLTNatInfo07 : ConstantInfo :=
  .defnInfo (kernelDefVal% instLTNat)

def finLTConst07 : VConstVal := ⟨vconst(type_of% @LT), ``LT⟩
def finLTMkConst07 : VConstVal := ⟨vconst(type_of% @LT.mk), ``LT.mk⟩
def finLTLtConst07 : VConstVal := ⟨vconst(type_of% @LT.lt), ``LT.lt⟩
def finInstLTNatConst07 : VConstVal :=
  ⟨vconst(type_of% @instLTNat), ``instLTNat⟩

def finLTMap07 : ConstMap := natTypeMap.insert ``LT finLTInfo07
def finLTMkMap07 : ConstMap := finLTMap07.insert ``LT.mk finLTMkInfo07
def finLTLtMap07 : ConstMap := finLTMkMap07.insert ``LT.lt finLTLtInfo07
def finInputMap07 : ConstMap :=
  finLTLtMap07.insert ``instLTNat finInstLTNatInfo07

def finLTEnv07 : VEnv :=
  (natTypeEnv.addConst ``LT finLTConst07.toVConstant).get!

def finLTMkEnv07 : VEnv :=
  (finLTEnv07.addConst ``LT.mk finLTMkConst07.toVConstant).get!

def finLTLtEnv07 : VEnv :=
  (finLTMkEnv07.addConst ``LT.lt finLTLtConst07.toVConstant).get!

def finInputEnv07 : VEnv :=
  (finLTLtEnv07.addConst ``instLTNat
    finInstLTNatConst07.toVConstant).get!

theorem natTypeAligned07 : Aligned .safe natTypeMap natTypeEnv := by
  exact Aligned.const .empty natType_fresh natInfo_tr.1 rfl natInfo_tr.2

theorem finLTConstWF07 : finLTConst07.toVConstant.WF natTypeEnv := by
  change natTypeEnv.IsType finLTConst07.uvars [] finLTConst07.type
  dsimp [finLTConst07]
  refine ⟨.imax (.succ (.succ (.param 0)))
    (.succ (.succ (.param 0))), ?_⟩
  refine VEnv.HasType.forallE
    (u := .succ (.succ (.param 0)))
    (v := .succ (.succ (.param 0))) ?_ ?_
  · exact VEnv.HasType.sort (by decide)
  · exact VEnv.HasType.sort (by decide)

theorem finLTInfoTr07 :
    TrConstVal .safe natTypeEnv finLTInfo07 finLTConst07 := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr natTypeEnv finLTInfo07.levelParams []
      finLTInfo07.type finLTConst07.type := by
    tr_type_expr_tac
  obtain ⟨sort, familyType⟩ := finLTConstWF07
  exact shape.to_trExprS natTypeEnv_ordered trivial
    ⟨.sort sort, familyType⟩

theorem finLTFresh07 : natTypeMap.find? ``LT = none := by
  rw [natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem finLTMapWF07 : finLTMap07.WF :=
  natTypeMap_wf.insert _ _ finLTFresh07

theorem finLTEnv_ordered07 : finLTEnv07.Ordered :=
  .const (n := ``LT) (ci := finLTConst07.toVConstant)
    natTypeEnv_ordered finLTConstWF07 rfl

theorem finLTAligned07 : Aligned .safe finLTMap07 finLTEnv07 :=
  Aligned.const natTypeAligned07 finLTFresh07 finLTInfoTr07.1 rfl
    finLTInfoTr07.2

theorem finLTMkConstWF07 : finLTMkConst07.toVConstant.WF finLTEnv07 := by
  have hLT : finLTEnv07.constants ``LT =
      some finLTConst07.toVConstant := rfl
  change finLTEnv07.IsType finLTMkConst07.uvars [] finLTMkConst07.type
  dsimp [finLTMkConst07]
  refine ⟨.imax (.succ (.succ (.param 0)))
    (.imax
      (.imax (.succ (.param 0))
        (.imax (.succ (.param 0)) (.succ .zero)))
      (.succ (.param 0))), ?_⟩
  refine VEnv.HasType.forallE
    (u := .succ (.succ (.param 0)))
    (v := .imax
      (.imax (.succ (.param 0))
        (.imax (.succ (.param 0)) (.succ .zero)))
      (.succ (.param 0))) ?_ ?_
  · exact VEnv.HasType.sort (by decide)
  · refine VEnv.HasType.forallE
      (u := .imax (.succ (.param 0))
        (.imax (.succ (.param 0)) (.succ .zero)))
      (v := .succ (.param 0)) ?_ ?_
    · refine VEnv.HasType.forallE
        (u := .succ (.param 0))
        (v := .imax (.succ (.param 0)) (.succ .zero)) ?_ ?_
      · type_tac
      · refine VEnv.HasType.forallE
          (u := .succ (.param 0)) (v := .succ .zero) ?_ ?_
        · type_tac
        · exact VEnv.HasType.sort (by decide)
    · type_tac

theorem finLTMkInfoTr07 :
    TrConstVal .safe finLTEnv07 finLTMkInfo07 finLTMkConst07 := by
  have hLT : finLTEnv07.constants ``LT =
      some finLTConst07.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr finLTEnv07 finLTMkInfo07.levelParams []
      finLTMkInfo07.type finLTMkConst07.type := by
    tr_type_expr_tac
  obtain ⟨sort, ctorType⟩ := finLTMkConstWF07
  exact shape.to_trExprS finLTEnv_ordered07 trivial
    ⟨.sort sort, ctorType⟩

theorem finLTMkFresh07 : finLTMap07.find? ``LT.mk = none := by
  rw [finLTMap07, natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem finLTMkMapWF07 : finLTMkMap07.WF :=
  finLTMapWF07.insert _ _ finLTMkFresh07

theorem finLTMkEnv_ordered07 : finLTMkEnv07.Ordered :=
  .const (n := ``LT.mk) (ci := finLTMkConst07.toVConstant)
    finLTEnv_ordered07 finLTMkConstWF07 rfl

theorem finLTMkAligned07 : Aligned .safe finLTMkMap07 finLTMkEnv07 :=
  Aligned.const finLTAligned07 finLTMkFresh07 finLTMkInfoTr07.1 rfl
    finLTMkInfoTr07.2

theorem finLTLtConstWF07 : finLTLtConst07.toVConstant.WF finLTMkEnv07 := by
  have hLT : finLTMkEnv07.constants ``LT =
      some finLTConst07.toVConstant := rfl
  change finLTMkEnv07.IsType finLTLtConst07.uvars [] finLTLtConst07.type
  dsimp [finLTLtConst07]
  refine ⟨.imax (.succ (.succ (.param 0)))
    (.imax (.succ (.param 0))
      (.imax (.succ (.param 0))
        (.imax (.succ (.param 0)) (.succ .zero)))), ?_⟩
  refine VEnv.HasType.forallE
    (u := .succ (.succ (.param 0)))
    (v := .imax (.succ (.param 0))
      (.imax (.succ (.param 0))
        (.imax (.succ (.param 0)) (.succ .zero)))) ?_ ?_
  · exact VEnv.HasType.sort (by decide)
  · refine VEnv.HasType.forallE
      (u := .succ (.param 0))
      (v := .imax (.succ (.param 0))
        (.imax (.succ (.param 0)) (.succ .zero))) ?_ ?_
    · type_tac
    · refine VEnv.HasType.forallE
        (u := .succ (.param 0))
        (v := .imax (.succ (.param 0)) (.succ .zero)) ?_ ?_
      · type_tac
      · refine VEnv.HasType.forallE
          (u := .succ (.param 0)) (v := .succ .zero) ?_ ?_
        · type_tac
        · exact VEnv.HasType.sort (by decide)

theorem finLTLtInfoTr07 :
    TrConstVal .safe finLTMkEnv07 finLTLtInfo07 finLTLtConst07 := by
  have hLT : finLTMkEnv07.constants ``LT =
      some finLTConst07.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr finLTMkEnv07 finLTLtInfo07.levelParams []
      finLTLtInfo07.type finLTLtConst07.type := by
    tr_type_expr_tac
  obtain ⟨sort, projectionType⟩ := finLTLtConstWF07
  exact shape.to_trExprS finLTMkEnv_ordered07 trivial
    ⟨.sort sort, projectionType⟩

theorem finLTLtFresh07 : finLTMkMap07.find? ``LT.lt = none := by
  rw [finLTMkMap07, finLTMapWF07.find?_insert, finLTMap07,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem finLTLtMapWF07 : finLTLtMap07.WF :=
  finLTMkMapWF07.insert _ _ finLTLtFresh07

theorem finLTLtEnv_ordered07 : finLTLtEnv07.Ordered :=
  .const (n := ``LT.lt) (ci := finLTLtConst07.toVConstant)
    finLTMkEnv_ordered07 finLTLtConstWF07 rfl

theorem finLTLtAligned07 : Aligned .safe finLTLtMap07 finLTLtEnv07 :=
  Aligned.const finLTMkAligned07 finLTLtFresh07 finLTLtInfoTr07.1 rfl
    finLTLtInfoTr07.2

theorem finInstLTNatConstWF07 :
    finInstLTNatConst07.toVConstant.WF finLTLtEnv07 := by
  have hNat : finLTLtEnv07.constants ``Nat =
      some natType.toVConstant := rfl
  have hLT : finLTLtEnv07.constants ``LT =
      some finLTConst07.toVConstant := rfl
  change finLTLtEnv07.IsType finInstLTNatConst07.uvars []
    finInstLTNatConst07.type
  dsimp [finInstLTNatConst07]
  refine ⟨.succ .zero, ?_⟩
  type_tac

theorem finInstLTNatInfoTr07 :
    TrConstVal .safe finLTLtEnv07 finInstLTNatInfo07
      finInstLTNatConst07 := by
  have hNat : finLTLtEnv07.constants ``Nat =
      some natType.toVConstant := rfl
  have hLT : finLTLtEnv07.constants ``LT =
      some finLTConst07.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr finLTLtEnv07 finInstLTNatInfo07.levelParams []
      finInstLTNatInfo07.type finInstLTNatConst07.type := by
    tr_type_expr_tac
  obtain ⟨sort, instanceType⟩ := finInstLTNatConstWF07
  exact shape.to_trExprS finLTLtEnv_ordered07 trivial
    ⟨.sort sort, instanceType⟩

theorem finInstLTNatFresh07 :
    finLTLtMap07.find? ``instLTNat = none := by
  rw [finLTLtMap07, finLTMkMapWF07.find?_insert, finLTMkMap07,
    finLTMapWF07.find?_insert, finLTMap07,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem finInputMapWF07 : finInputMap07.WF :=
  finLTLtMapWF07.insert _ _ finInstLTNatFresh07

theorem finInputEnv_ordered07 : finInputEnv07.Ordered :=
  .const (n := ``instLTNat) (ci := finInstLTNatConst07.toVConstant)
    finLTLtEnv_ordered07 finInstLTNatConstWF07 rfl

theorem finInputAligned07 : Aligned .safe finInputMap07 finInputEnv07 :=
  Aligned.const finLTLtAligned07 finInstLTNatFresh07
    finInstLTNatInfoTr07.1 rfl finInstLTNatInfoTr07.2

example : finInputMap07 = finDependencyMap07 := rfl

/-! ### Fin -/

theorem finCheckedWF07 : finChecked.WF finInputEnv07 := by
  constructor
  · change finInputEnv07.OnTel 0 [] [.const ``Nat []]
    have hNat : finInputEnv07.constants ``Nat =
        some natType.toVConstant := rfl
    exact ⟨⟨.succ .zero, by type_tac⟩, trivial⟩
  · intro ctor hctor
    have hctor' := List.mem_singleton.1 hctor
    subst ctor
    constructor
    · change VInductDecl.fieldsWF 0 ``Fin 1 finInputEnv07
        (.succ .zero) [] [.const ``Nat []] 0
        [.const ``Nat [],
          .app
            (.app
              (.app
                (.app (.const ``LT.lt [.zero]) (.const ``Nat []))
                  (.const ``instLTNat []))
                (.bvar 0))
              (.bvar 1)]
      have hNat : finInputEnv07.constants ``Nat =
          some natType.toVConstant := rfl
      have hLT : finInputEnv07.constants ``LT =
          some finLTConst07.toVConstant := rfl
      have hLTLt : finInputEnv07.constants ``LT.lt =
          some finLTLtConst07.toVConstant := rfl
      have hInst : finInputEnv07.constants ``instLTNat =
          some finInstLTNatConst07.toVConstant := rfl
      constructor
      · exact .inr (.inr ⟨rfl, .succ .zero, by type_tac,
          .inr (VLevel.le_refl _)⟩)
      constructor
      · intro recursive
        contradiction
      constructor
      · exact .inr (.inr ⟨rfl, .zero, by type_tac,
          .inr VLevel.zero_le⟩)
      constructor
      · intro recursive
        contradiction
      · trivial
    · exact .nil

theorem finGenerationWF07 : finGenerationChecked.WF finInputEnv07 := by
  exact finCheckedWF07.identityGeneration finInputEnv_ordered07

def finTypeEnv07 : VEnv :=
  (finInputEnv07.addConst finType.name finType.toVConstant).get!

def finCtorEnv07 : VEnv :=
  (finTypeEnv07.addConst finType.ctors[0].name
    finType.ctors[0].toVConstant).get!

def finRecEnv07 : VEnv :=
  (finCtorEnv07.addConst ``Fin.rec
    (inductGenerationRecVal finGenerationChecked).toVConstant).get!

def finFinalEnv07 : VEnv :=
  finGenerationChecked.generatedRules.foldl VEnv.addDefEq finRecEnv07

def finTypeMap07 : ConstMap := finInputMap07.insert ``Fin finInfo07
def finCtorMap07 : ConstMap := finTypeMap07.insert ``Fin.mk finMkInfo07
def finMap07 : ConstMap := finCtorMap07.insert ``Fin.rec finRecInfo07

theorem finTypeEnv_ordered07 : finTypeEnv07.Ordered :=
  replayTypeEnv_ordered07 finInputEnv_ordered07 finGenerationWF07 rfl

theorem finCtorEnv_ordered07 : finCtorEnv07.Ordered :=
  replayCtorEnv_ordered07 finGenerationWF07 rfl finTypeEnv_ordered07 rfl

theorem finGenerationEnv07 :
    VInductDecl.GenerationEnv finGenerationChecked finCtorEnv07 :=
  replayGenerationEnv07 finGenerationWF07 rfl rfl finCtorEnv_ordered07

theorem finInfoTr07 :
    TrConstVal .safe finInputEnv07 finInfo07 finType.toVConstVal := by
  have hNat : finInputEnv07.constants ``Nat =
      some natType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr finInputEnv07 finInfo07.levelParams []
      finInfo07.type finType.type := by
    tr_type_expr_tac
  obtain ⟨sort, familyType⟩ := replayRawFamilyWF07 finGenerationWF07
  exact shape.to_trExprS finInputEnv_ordered07 trivial
    ⟨.sort sort, familyType⟩

theorem finCtorInfoTr07 :
    TrConstVal .safe finTypeEnv07 finMkInfo07 finType.ctors[0] := by
  have hNat : finTypeEnv07.constants ``Nat =
      some natType.toVConstant := rfl
  have hLT : finTypeEnv07.constants ``LT =
      some finLTConst07.toVConstant := rfl
  have hLTLt : finTypeEnv07.constants ``LT.lt =
      some finLTLtConst07.toVConstant := rfl
  have hInst : finTypeEnv07.constants ``instLTNat =
      some finInstLTNatConst07.toVConstant := rfl
  have hFin : finTypeEnv07.constants ``Fin =
      some finType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr finTypeEnv07 finMkInfo07.levelParams []
      finMkInfo07.type finType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨sort, ctorType⟩ := replayRawCtorWF07 finGenerationWF07 rfl
    finType.ctors[0] (.head _)
  exact shape.to_trExprS finTypeEnv_ordered07 trivial
    ⟨.sort sort, ctorType⟩

theorem finRecInfoTr07 :
    TrConstVal .safe finCtorEnv07 finRecInfo07
      (inductGenerationRecVal finGenerationChecked) := by
  have hNat : finCtorEnv07.constants ``Nat =
      some natType.toVConstant := rfl
  have hLT : finCtorEnv07.constants ``LT =
      some finLTConst07.toVConstant := rfl
  have hLTLt : finCtorEnv07.constants ``LT.lt =
      some finLTLtConst07.toVConstant := rfl
  have hInst : finCtorEnv07.constants ``instLTNat =
      some finInstLTNatConst07.toVConstant := rfl
  have hFin : finCtorEnv07.constants ``Fin =
      some finType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr finCtorEnv07 finRecInfo07.levelParams []
      finRecInfo07.type
      (inductGenerationRecVal finGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨sort, recursorType⟩ := finGenerationEnv07.recursor_wf
  exact shape.to_trExprS finCtorEnv_ordered07 trivial
    ⟨.sort sort, recursorType⟩

theorem finTypeFresh07 : finInputMap07.find? ``Fin = none := by
  rw [finInputMap07, finLTLtMapWF07.find?_insert, finLTLtMap07,
    finLTMkMapWF07.find?_insert, finLTMkMap07,
    finLTMapWF07.find?_insert, finLTMap07,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem finTypeMapWF07 : finTypeMap07.WF :=
  finInputMapWF07.insert _ _ finTypeFresh07

theorem finCtorFresh07 : finTypeMap07.find? ``Fin.mk = none := by
  rw [finTypeMap07, finInputMapWF07.find?_insert, finInputMap07,
    finLTLtMapWF07.find?_insert, finLTLtMap07,
    finLTMkMapWF07.find?_insert, finLTMkMap07,
    finLTMapWF07.find?_insert, finLTMap07,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem finCtorMapWF07 : finCtorMap07.WF :=
  finTypeMapWF07.insert _ _ finCtorFresh07

theorem finRecFresh07 : finCtorMap07.find? ``Fin.rec = none := by
  rw [finCtorMap07, finTypeMapWF07.find?_insert, finTypeMap07,
    finInputMapWF07.find?_insert, finInputMap07,
    finLTLtMapWF07.find?_insert, finLTLtMap07,
    finLTMkMapWF07.find?_insert, finLTMkMap07,
    finLTMapWF07.find?_insert, finLTMap07,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem finAddInduct07 : AddInduct finInputMap07 finInputEnv07 finDecl
    finMap07 finFinalEnv07 := by
  refine ⟨{
    generation := finGenerationChecked
    generation_wf := finGenerationWF07
    typeMap := finTypeMap07
    typeEnv := finTypeEnv07
    ctorMap := finCtorMap07
    ctorEnv := finCtorEnv07
    recEnv := finRecEnv07
    addType := {
      info := finInfo07
      kind_eq := by simp [finInfo07, InductConstantKind.Matches]
      tr := finInfoTr07
      map_fresh := finTypeFresh07
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := finRecInfo07
      kind_eq := by simp [finRecInfo07, InductConstantKind.Matches]
      tr := finRecInfoTr07
      map_fresh := finRecFresh07
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
    info := finMkInfo07
    kind_eq := by simp [finMkInfo07, InductConstantKind.Matches]
    tr := finCtorInfoTr07
    map_fresh := by simpa [finType] using finCtorFresh07
    env_add := rfl
    map_add := rfl } .nil

theorem finAligned07 : Aligned .safe finMap07 finFinalEnv07 :=
  Aligned.addInduct finAddInduct07 finInputAligned07

def finReplay07 : SingletonReplayArtifact where
  label := ``Fin
  source := finDecl
  inputMap := finInputMap07
  inputEnv := finInputEnv07
  inputMapWF := finInputMapWF07
  outputMap := finMap07
  outputEnv := finFinalEnv07
  inputOrdered := finInputEnv_ordered07
  transaction := finAddInduct07
  aligned := finAligned07

/-! ### Vector dependency environment -/

def vectorArrayInfo07 : ConstantInfo := kernelInductInfo% Array
def vectorArraySizeInfo07 : ConstantInfo :=
  .defnInfo (kernelDefVal% Array.size)

def vectorArrayConst07 : VConstVal :=
  ⟨vconst(type_of% @Array), ``Array⟩

def vectorArraySizeConst07 : VConstVal :=
  ⟨vconst(type_of% @Array.size), ``Array.size⟩

def vectorEqMap07 : ConstMap := natTypeMap.insert ``Eq eqInfo
def vectorArrayMap07 : ConstMap :=
  vectorEqMap07.insert ``Array vectorArrayInfo07
def vectorInputMap07 : ConstMap :=
  vectorArrayMap07.insert ``Array.size vectorArraySizeInfo07

def vectorEqEnv07 : VEnv :=
  (natTypeEnv.addConst ``Eq eqType.toVConstant).get!

def vectorArrayEnv07 : VEnv :=
  (vectorEqEnv07.addConst ``Array vectorArrayConst07.toVConstant).get!

def vectorInputEnv07 : VEnv :=
  (vectorArrayEnv07.addConst ``Array.size
    vectorArraySizeConst07.toVConstant).get!

theorem empty_le_natTypeEnv07 : VEnv.empty ≤ natTypeEnv :=
  VEnv.addConst_le (show VEnv.empty.addConst natType.name
    natType.toVConstant = some natTypeEnv from rfl)

theorem vectorEqTypeWF07 : eqType.toVConstant.WF natTypeEnv :=
  eqType_wf.mono empty_le_natTypeEnv07

theorem vectorEqInfoTr07 :
    TrConstVal .safe natTypeEnv eqInfo eqType.toVConstVal :=
  eqInfo_tr.mono empty_le_natTypeEnv07

theorem vectorEqFresh07 : natTypeMap.find? ``Eq = none := by
  rw [natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem vectorEqMapWF07 : vectorEqMap07.WF :=
  natTypeMap_wf.insert _ _ vectorEqFresh07

theorem vectorEqEnv_ordered07 : vectorEqEnv07.Ordered :=
  .const (n := ``Eq) (ci := eqType.toVConstant)
    natTypeEnv_ordered vectorEqTypeWF07 rfl

theorem vectorEqAligned07 : Aligned .safe vectorEqMap07 vectorEqEnv07 :=
  Aligned.const natTypeAligned07 vectorEqFresh07 vectorEqInfoTr07.1 rfl
    vectorEqInfoTr07.2

theorem vectorArrayConstWF07 :
    vectorArrayConst07.toVConstant.WF vectorEqEnv07 := by
  change vectorEqEnv07.IsType vectorArrayConst07.uvars []
    vectorArrayConst07.type
  dsimp [vectorArrayConst07]
  refine ⟨.imax (.succ (.succ (.param 0)))
    (.succ (.succ (.param 0))), ?_⟩
  refine VEnv.HasType.forallE
    (u := .succ (.succ (.param 0)))
    (v := .succ (.succ (.param 0))) ?_ ?_
  · exact VEnv.HasType.sort (by decide)
  · exact VEnv.HasType.sort (by decide)

theorem vectorArrayInfoTr07 :
    TrConstVal .safe vectorEqEnv07 vectorArrayInfo07
      vectorArrayConst07 := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr vectorEqEnv07 vectorArrayInfo07.levelParams []
      vectorArrayInfo07.type vectorArrayConst07.type := by
    tr_type_expr_tac
  obtain ⟨sort, arrayType⟩ := vectorArrayConstWF07
  exact shape.to_trExprS vectorEqEnv_ordered07 trivial
    ⟨.sort sort, arrayType⟩

theorem vectorArrayFresh07 : vectorEqMap07.find? ``Array = none := by
  rw [vectorEqMap07, natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem vectorArrayMapWF07 : vectorArrayMap07.WF :=
  vectorEqMapWF07.insert _ _ vectorArrayFresh07

theorem vectorArrayEnv_ordered07 : vectorArrayEnv07.Ordered :=
  .const (n := ``Array) (ci := vectorArrayConst07.toVConstant)
    vectorEqEnv_ordered07 vectorArrayConstWF07 rfl

theorem vectorArrayAligned07 :
    Aligned .safe vectorArrayMap07 vectorArrayEnv07 :=
  Aligned.const vectorEqAligned07 vectorArrayFresh07
    vectorArrayInfoTr07.1 rfl vectorArrayInfoTr07.2

theorem vectorArraySizeConstWF07 :
    vectorArraySizeConst07.toVConstant.WF vectorArrayEnv07 := by
  have hNat : vectorArrayEnv07.constants ``Nat =
      some natType.toVConstant := rfl
  have hArray : vectorArrayEnv07.constants ``Array =
      some vectorArrayConst07.toVConstant := rfl
  change vectorArrayEnv07.IsType vectorArraySizeConst07.uvars []
    vectorArraySizeConst07.type
  dsimp [vectorArraySizeConst07]
  refine ⟨.imax (.succ (.succ (.param 0)))
    (.imax (.succ (.param 0)) (.succ .zero)), ?_⟩
  refine VEnv.HasType.forallE
    (u := .succ (.succ (.param 0)))
    (v := .imax (.succ (.param 0)) (.succ .zero)) ?_ ?_
  · exact VEnv.HasType.sort (by decide)
  · refine VEnv.HasType.forallE
      (u := .succ (.param 0)) (v := .succ .zero) ?_ ?_
    · type_tac
    · type_tac

theorem vectorArraySizeInfoTr07 :
    TrConstVal .safe vectorArrayEnv07 vectorArraySizeInfo07
      vectorArraySizeConst07 := by
  have hNat : vectorArrayEnv07.constants ``Nat =
      some natType.toVConstant := rfl
  have hArray : vectorArrayEnv07.constants ``Array =
      some vectorArrayConst07.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr vectorArrayEnv07
      vectorArraySizeInfo07.levelParams [] vectorArraySizeInfo07.type
      vectorArraySizeConst07.type := by
    tr_type_expr_tac
  obtain ⟨sort, sizeType⟩ := vectorArraySizeConstWF07
  exact shape.to_trExprS vectorArrayEnv_ordered07 trivial
    ⟨.sort sort, sizeType⟩

theorem vectorArraySizeFresh07 :
    vectorArrayMap07.find? ``Array.size = none := by
  rw [vectorArrayMap07, vectorEqMapWF07.find?_insert, vectorEqMap07,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem vectorInputMapWF07 : vectorInputMap07.WF :=
  vectorArrayMapWF07.insert _ _ vectorArraySizeFresh07

theorem vectorInputEnv_ordered07 : vectorInputEnv07.Ordered :=
  .const (n := ``Array.size) (ci := vectorArraySizeConst07.toVConstant)
    vectorArrayEnv_ordered07 vectorArraySizeConstWF07 rfl

theorem vectorInputAligned07 :
    Aligned .safe vectorInputMap07 vectorInputEnv07 :=
  Aligned.const vectorArrayAligned07 vectorArraySizeFresh07
    vectorArraySizeInfoTr07.1 rfl vectorArraySizeInfoTr07.2

example : vectorInputMap07 = vectorDependencyMap07 := rfl

/-! ### Vector -/

theorem vectorCheckedWF07 : vectorChecked.WF vectorInputEnv07 := by
  constructor
  · change vectorInputEnv07.OnTel 1 []
      [.sort (.succ (.param 0)), .const ``Nat []]
    have hNat : vectorInputEnv07.constants ``Nat =
        some natType.toVConstant := rfl
    exact ⟨⟨.succ (.succ (.param 0)), VEnv.HasType.sort (by decide)⟩,
      ⟨⟨.succ .zero, by type_tac⟩, trivial⟩⟩
  · intro ctor hctor
    have hctor' := List.mem_singleton.1 hctor
    subst ctor
    constructor
    · change VInductDecl.fieldsWF 1 ``Vector 2 vectorInputEnv07
        (.succ (.param 0)) []
        [.const ``Nat [], .sort (.succ (.param 0))] 0
        [.app (.const ``Array [.param 0]) (.bvar 1),
          .app
            (.app
              (.app (.const ``Eq [.succ .zero]) (.const ``Nat []))
                (.app
                  (.app (.const ``Array.size [.param 0]) (.bvar 2))
                  (.bvar 0)))
            (.bvar 1)]
      have hNat : vectorInputEnv07.constants ``Nat =
          some natType.toVConstant := rfl
      have hEq : vectorInputEnv07.constants ``Eq =
          some eqType.toVConstant := rfl
      have hArray : vectorInputEnv07.constants ``Array =
          some vectorArrayConst07.toVConstant := rfl
      have hSize : vectorInputEnv07.constants ``Array.size =
          some vectorArraySizeConst07.toVConstant := rfl
      constructor
      · exact .inr (.inr ⟨rfl, .succ (.param 0), by type_tac,
          .inr (VLevel.le_refl _)⟩)
      constructor
      · intro recursive
        contradiction
      constructor
      · exact .inr (.inr ⟨rfl, .zero, by type_tac,
          .inr VLevel.zero_le⟩)
      constructor
      · intro recursive
        contradiction
      · trivial
    · exact .nil

theorem vectorGenerationWF07 :
    vectorGenerationChecked.WF vectorInputEnv07 := by
  exact vectorCheckedWF07.identityGeneration vectorInputEnv_ordered07

def vectorTypeEnv07 : VEnv :=
  (vectorInputEnv07.addConst vectorType.name vectorType.toVConstant).get!

def vectorCtorEnv07 : VEnv :=
  (vectorTypeEnv07.addConst vectorType.ctors[0].name
    vectorType.ctors[0].toVConstant).get!

def vectorRecEnv07 : VEnv :=
  (vectorCtorEnv07.addConst ``Vector.rec
    (inductGenerationRecVal vectorGenerationChecked).toVConstant).get!

def vectorFinalEnv07 : VEnv :=
  vectorGenerationChecked.generatedRules.foldl VEnv.addDefEq vectorRecEnv07

def vectorTypeMap07 : ConstMap :=
  vectorInputMap07.insert ``Vector vectorInfo07
def vectorCtorMap07 : ConstMap :=
  vectorTypeMap07.insert ``Vector.mk vectorMkInfo07
def vectorMap07 : ConstMap :=
  vectorCtorMap07.insert ``Vector.rec vectorRecInfo07

theorem vectorTypeEnv_ordered07 : vectorTypeEnv07.Ordered :=
  replayTypeEnv_ordered07 vectorInputEnv_ordered07 vectorGenerationWF07 rfl

theorem vectorCtorEnv_ordered07 : vectorCtorEnv07.Ordered :=
  replayCtorEnv_ordered07 vectorGenerationWF07 rfl
    vectorTypeEnv_ordered07 rfl

theorem vectorGenerationEnv07 :
    VInductDecl.GenerationEnv vectorGenerationChecked vectorCtorEnv07 :=
  replayGenerationEnv07 vectorGenerationWF07 rfl rfl
    vectorCtorEnv_ordered07

theorem vectorInfoTr07 :
    TrConstVal .safe vectorInputEnv07 vectorInfo07
      vectorType.toVConstVal := by
  have hNat : vectorInputEnv07.constants ``Nat =
      some natType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr vectorInputEnv07 vectorInfo07.levelParams []
      vectorInfo07.type vectorType.type := by
    tr_type_expr_tac
  obtain ⟨sort, familyType⟩ := replayRawFamilyWF07 vectorGenerationWF07
  exact shape.to_trExprS vectorInputEnv_ordered07 trivial
    ⟨.sort sort, familyType⟩

theorem vectorCtorInfoTr07 :
    TrConstVal .safe vectorTypeEnv07 vectorMkInfo07 vectorType.ctors[0] := by
  have hNat : vectorTypeEnv07.constants ``Nat =
      some natType.toVConstant := rfl
  have hEq : vectorTypeEnv07.constants ``Eq =
      some eqType.toVConstant := rfl
  have hArray : vectorTypeEnv07.constants ``Array =
      some vectorArrayConst07.toVConstant := rfl
  have hSize : vectorTypeEnv07.constants ``Array.size =
      some vectorArraySizeConst07.toVConstant := rfl
  have hVector : vectorTypeEnv07.constants ``Vector =
      some vectorType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr vectorTypeEnv07 vectorMkInfo07.levelParams []
      vectorMkInfo07.type vectorType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨sort, ctorType⟩ := replayRawCtorWF07 vectorGenerationWF07 rfl
    vectorType.ctors[0] (.head _)
  exact shape.to_trExprS vectorTypeEnv_ordered07 trivial
    ⟨.sort sort, ctorType⟩

theorem vectorRecInfoTr07 :
    TrConstVal .safe vectorCtorEnv07 vectorRecInfo07
      (inductGenerationRecVal vectorGenerationChecked) := by
  have hNat : vectorCtorEnv07.constants ``Nat =
      some natType.toVConstant := rfl
  have hEq : vectorCtorEnv07.constants ``Eq =
      some eqType.toVConstant := rfl
  have hArray : vectorCtorEnv07.constants ``Array =
      some vectorArrayConst07.toVConstant := rfl
  have hSize : vectorCtorEnv07.constants ``Array.size =
      some vectorArraySizeConst07.toVConstant := rfl
  have hVector : vectorCtorEnv07.constants ``Vector =
      some vectorType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr vectorCtorEnv07 vectorRecInfo07.levelParams []
      vectorRecInfo07.type
      (inductGenerationRecVal vectorGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨sort, recursorType⟩ := vectorGenerationEnv07.recursor_wf
  exact shape.to_trExprS vectorCtorEnv_ordered07 trivial
    ⟨.sort sort, recursorType⟩

theorem vectorTypeFresh07 :
    vectorInputMap07.find? ``Vector = none := by
  rw [vectorInputMap07, vectorArrayMapWF07.find?_insert,
    vectorArrayMap07, vectorEqMapWF07.find?_insert, vectorEqMap07,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem vectorTypeMapWF07 : vectorTypeMap07.WF :=
  vectorInputMapWF07.insert _ _ vectorTypeFresh07

theorem vectorCtorFresh07 :
    vectorTypeMap07.find? ``Vector.mk = none := by
  rw [vectorTypeMap07, vectorInputMapWF07.find?_insert,
    vectorInputMap07, vectorArrayMapWF07.find?_insert,
    vectorArrayMap07, vectorEqMapWF07.find?_insert, vectorEqMap07,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem vectorCtorMapWF07 : vectorCtorMap07.WF :=
  vectorTypeMapWF07.insert _ _ vectorCtorFresh07

theorem vectorRecFresh07 :
    vectorCtorMap07.find? ``Vector.rec = none := by
  rw [vectorCtorMap07, vectorTypeMapWF07.find?_insert,
    vectorTypeMap07, vectorInputMapWF07.find?_insert,
    vectorInputMap07, vectorArrayMapWF07.find?_insert,
    vectorArrayMap07, vectorEqMapWF07.find?_insert, vectorEqMap07,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem vectorAddInduct07 :
    AddInduct vectorInputMap07 vectorInputEnv07 vectorDecl
      vectorMap07 vectorFinalEnv07 := by
  refine ⟨{
    generation := vectorGenerationChecked
    generation_wf := vectorGenerationWF07
    typeMap := vectorTypeMap07
    typeEnv := vectorTypeEnv07
    ctorMap := vectorCtorMap07
    ctorEnv := vectorCtorEnv07
    recEnv := vectorRecEnv07
    addType := {
      info := vectorInfo07
      kind_eq := by simp [vectorInfo07, InductConstantKind.Matches]
      tr := vectorInfoTr07
      map_fresh := vectorTypeFresh07
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := vectorRecInfo07
      kind_eq := by simp [vectorRecInfo07, InductConstantKind.Matches]
      tr := vectorRecInfoTr07
      map_fresh := vectorRecFresh07
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
    info := vectorMkInfo07
    kind_eq := by simp [vectorMkInfo07, InductConstantKind.Matches]
    tr := vectorCtorInfoTr07
    map_fresh := by simpa [vectorType] using vectorCtorFresh07
    env_add := rfl
    map_add := rfl } .nil

theorem vectorAligned07 : Aligned .safe vectorMap07 vectorFinalEnv07 :=
  Aligned.addInduct vectorAddInduct07 vectorInputAligned07

def vectorReplay07 : SingletonReplayArtifact where
  label := ``Vector
  source := vectorDecl
  inputMap := vectorInputMap07
  inputEnv := vectorInputEnv07
  inputMapWF := vectorInputMapWF07
  outputMap := vectorMap07
  outputEnv := vectorFinalEnv07
  inputOrdered := vectorInputEnv_ordered07
  transaction := vectorAddInduct07
  aligned := vectorAligned07

/-! ### Unit/Empty edge cases -/

theorem punitGenerationWF07 : punitGenerationChecked.WF VEnv.empty := by
  exact (punitChecked.wf_of_decl punitDecl_wf).identityGeneration .empty

def punitTypeEnv07 : VEnv :=
  (VEnv.empty.addConst punitType.name punitType.toVConstant).get!

def punitCtorEnv07 : VEnv :=
  (punitTypeEnv07.addConst punitType.ctors[0].name
    punitType.ctors[0].toVConstant).get!

def punitRecEnv07 : VEnv :=
  (punitCtorEnv07.addConst ``PUnit.rec
    (inductGenerationRecVal punitGenerationChecked).toVConstant).get!

def punitFinalEnv07 : VEnv :=
  punitGenerationChecked.generatedRules.foldl VEnv.addDefEq punitRecEnv07

def punitTypeMap07 : ConstMap :=
  ({} : ConstMap).insert ``PUnit punitInfo06C

def punitCtorMap07 : ConstMap :=
  punitTypeMap07.insert ``PUnit.unit punitCtorInfo06C

def punitMap07 : ConstMap :=
  punitCtorMap07.insert ``PUnit.rec punitRecInfo06C

theorem punitTypeEnv_ordered07 : punitTypeEnv07.Ordered :=
  replayTypeEnv_ordered07 .empty punitGenerationWF07 rfl

theorem punitCtorEnv_ordered07 : punitCtorEnv07.Ordered :=
  replayCtorEnv_ordered07 punitGenerationWF07 rfl
    punitTypeEnv_ordered07 rfl

theorem punitGenerationEnv07 :
    VInductDecl.GenerationEnv punitGenerationChecked punitCtorEnv07 :=
  replayGenerationEnv07 punitGenerationWF07 rfl rfl
    punitCtorEnv_ordered07

theorem punitInfoTr07 :
    TrConstVal .safe VEnv.empty punitInfo06C punitType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  exact .sort rfl

theorem punitCtorInfoTr07 :
    TrConstVal .safe punitTypeEnv07 punitCtorInfo06C punitType.ctors[0] := by
  have hPUnit : punitTypeEnv07.constants ``PUnit =
      some punitType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr punitTypeEnv07 punitCtorInfo06C.levelParams []
      punitCtorInfo06C.type punitType.ctors[0].type := by
    tr_type_expr_tac
  exact shape.to_trExprS punitTypeEnv_ordered07 trivial
    ⟨.sort (.param 0), by type_tac⟩

theorem punitRecInfoTr07 :
    TrConstVal .safe punitCtorEnv07 punitRecInfo06C
      (inductGenerationRecVal punitGenerationChecked) := by
  have hPUnit : punitCtorEnv07.constants ``PUnit =
      some punitType.toVConstant := rfl
  have hUnit : punitCtorEnv07.constants ``PUnit.unit =
      some punitType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr punitCtorEnv07 punitRecInfo06C.levelParams []
      punitRecInfo06C.type
      (inductGenerationRecVal punitGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨sort, recursorType⟩ := punitGenerationEnv07.recursor_wf
  exact shape.to_trExprS punitCtorEnv_ordered07 trivial
    ⟨.sort sort, recursorType⟩

theorem punitTypeFresh07 : ({} : ConstMap).find? ``PUnit = none := by
  simp [SMap.find?]

theorem punitTypeMapWF07 : punitTypeMap07.WF :=
  SMap.WF.empty.insert _ _ punitTypeFresh07

theorem punitCtorFresh07 : punitTypeMap07.find? ``PUnit.unit = none := by
  rw [punitTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem punitCtorMapWF07 : punitCtorMap07.WF :=
  punitTypeMapWF07.insert _ _ punitCtorFresh07

theorem punitRecFresh07 : punitCtorMap07.find? ``PUnit.rec = none := by
  rw [punitCtorMap07, punitTypeMapWF07.find?_insert, punitTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem punitAddInduct07 : AddInduct ({} : ConstMap) VEnv.empty punitDecl
    punitMap07 punitFinalEnv07 := by
  refine ⟨{
    generation := punitGenerationChecked
    generation_wf := punitGenerationWF07
    typeMap := punitTypeMap07
    typeEnv := punitTypeEnv07
    ctorMap := punitCtorMap07
    ctorEnv := punitCtorEnv07
    recEnv := punitRecEnv07
    addType := {
      info := punitInfo06C
      kind_eq := by simp [punitInfo06C, InductConstantKind.Matches]
      tr := punitInfoTr07
      map_fresh := punitTypeFresh07
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := punitRecInfo06C
      kind_eq := by simp [punitRecInfo06C, InductConstantKind.Matches]
      tr := punitRecInfoTr07
      map_fresh := punitRecFresh07
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
      info := punitCtorInfo06C
      kind_eq := by simp [punitCtorInfo06C, InductConstantKind.Matches]
      tr := punitCtorInfoTr07
      map_fresh := by simpa [punitType] using punitCtorFresh07
      env_add := rfl
      map_add := rfl } .nil

theorem punitAligned07 : Aligned .safe punitMap07 punitFinalEnv07 :=
  Aligned.addInduct punitAddInduct07 .empty

def punitReplay07 : SingletonReplayArtifact where
  label := ``Unit
  source := punitDecl
  inputMap := {}
  inputEnv := .empty
  inputMapWF := SMap.WF.empty
  outputMap := punitMap07
  outputEnv := punitFinalEnv07
  inputOrdered := .empty
  transaction := punitAddInduct07
  aligned := punitAligned07

theorem emptyGenerationWF07 : emptyGenerationChecked.WF VEnv.empty := by
  exact (emptyChecked.wf_of_decl emptyDecl_wf).identityGeneration .empty

def emptyTypeEnv07 : VEnv :=
  (VEnv.empty.addConst emptyType.name emptyType.toVConstant).get!

def emptyRecEnv07 : VEnv :=
  (emptyTypeEnv07.addConst ``Empty.rec
    (inductGenerationRecVal emptyGenerationChecked).toVConstant).get!

def emptyFinalEnv07 : VEnv :=
  emptyGenerationChecked.generatedRules.foldl VEnv.addDefEq emptyRecEnv07

def emptyTypeMap07 : ConstMap :=
  ({} : ConstMap).insert ``Empty emptyInfo06C

def emptyMap07 : ConstMap :=
  emptyTypeMap07.insert ``Empty.rec emptyRecInfo06C

theorem emptyTypeEnv_ordered07 : emptyTypeEnv07.Ordered :=
  replayTypeEnv_ordered07 .empty emptyGenerationWF07 rfl

theorem emptyGenerationEnv07 :
    VInductDecl.GenerationEnv emptyGenerationChecked emptyTypeEnv07 :=
  replayGenerationEnv07 emptyGenerationWF07 rfl rfl
    emptyTypeEnv_ordered07

theorem emptyInfoTr07 :
    TrConstVal .safe VEnv.empty emptyInfo06C emptyType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  exact .sort rfl

theorem emptyRecInfoTr07 :
    TrConstVal .safe emptyTypeEnv07 emptyRecInfo06C
      (inductGenerationRecVal emptyGenerationChecked) := by
  have hEmpty : emptyTypeEnv07.constants ``Empty =
      some emptyType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr emptyTypeEnv07 emptyRecInfo06C.levelParams []
      emptyRecInfo06C.type
      (inductGenerationRecVal emptyGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨sort, recursorType⟩ := emptyGenerationEnv07.recursor_wf
  exact shape.to_trExprS emptyTypeEnv_ordered07 trivial
    ⟨.sort sort, recursorType⟩

theorem emptyTypeFresh07 : ({} : ConstMap).find? ``Empty = none := by
  simp [SMap.find?]

theorem emptyTypeMapWF07 : emptyTypeMap07.WF :=
  SMap.WF.empty.insert _ _ emptyTypeFresh07

theorem emptyRecFresh07 : emptyTypeMap07.find? ``Empty.rec = none := by
  rw [emptyTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem emptyAddInduct07 : AddInduct ({} : ConstMap) VEnv.empty emptyDecl
    emptyMap07 emptyFinalEnv07 := by
  refine ⟨{
    generation := emptyGenerationChecked
    generation_wf := emptyGenerationWF07
    typeMap := emptyTypeMap07
    typeEnv := emptyTypeEnv07
    ctorMap := emptyTypeMap07
    ctorEnv := emptyTypeEnv07
    recEnv := emptyRecEnv07
    addType := {
      info := emptyInfo06C
      kind_eq := by simp [emptyInfo06C, InductConstantKind.Matches]
      tr := emptyInfoTr07
      map_fresh := emptyTypeFresh07
      env_add := rfl
      map_add := rfl }
    addCtors := .nil
    addRec := {
      info := emptyRecInfo06C
      kind_eq := by simp [emptyRecInfo06C, InductConstantKind.Matches]
      tr := emptyRecInfoTr07
      map_fresh := emptyRecFresh07
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩

theorem emptyAligned07 : Aligned .safe emptyMap07 emptyFinalEnv07 :=
  Aligned.addInduct emptyAddInduct07 .empty

def emptyReplay07 : SingletonReplayArtifact where
  label := ``Empty
  source := emptyDecl
  inputMap := {}
  inputEnv := .empty
  inputMapWF := SMap.WF.empty
  outputMap := emptyMap07
  outputEnv := emptyFinalEnv07
  inputOrdered := .empty
  transaction := emptyAddInduct07
  aligned := emptyAligned07

/-- Every fixed positive row, in exactly the same order as the
Theory/kernel parity matrix.  Each entry carries an actual `ConstantInfo`
transaction and final environment alignment, including the real dependency
environments required by `Fin` and `Vector`. -/
def singletonFixedReplays : List SingletonReplayArtifact :=
  [natReplay07, boolReplay07, listReplay07, optionReplay07, prodReplay07,
    punitReplay07, emptyReplay07, orReplay07, andReplay07, eqReplay07,
    heqReplay07, finReplay07, vectorReplay07, accReplay07]

/-- The focused non-identity normalization rows use the same public replay
artifact as the standard-library matrix. -/
def singletonNormalizationReplays :
    List SingletonReplayArtifact :=
  [aliasFormerReplay07, aliasRecReplay07, normalizationMatrixReplay07,
    annotatedPiReplay07, annotatedParamReplay07]

/-- The public singleton environment replay inventory. -/
def singletonReplayMatrix : List SingletonReplayArtifact :=
  singletonFixedReplays ++ singletonNormalizationReplays

example : singletonFixedReplays.map (·.label) =
    singletonPositiveArtifacts.map (·.label) := rfl

example : singletonFixedReplays.map (·.source) =
    singletonPositiveArtifacts.map (·.source) := rfl

example : singletonNormalizationReplays.map (·.label) =
    singletonNormalizationArtifacts.map (·.label) := rfl

example : singletonNormalizationReplays.map (·.source) =
    singletonNormalizationArtifacts.map (·.source) := rfl

example : singletonReplayMatrix.map (·.source) =
    (singletonPositiveArtifacts ++ singletonNormalizationArtifacts).map
      (·.source) := rfl

example : singletonFixedReplays.length = 14 := rfl
example : singletonNormalizationReplays.length = 5 := rfl
example : singletonReplayMatrix.length = 19 := rfl

/-! ## Exact trust manifests for the public replay seam -/

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.SingletonReplayArtifact.outputOrdered [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.singletonFixedReplays [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.singletonNormalizationReplays [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.singletonReplayMatrix [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

end Ix.Theory.Named.InductiveReplayFixtures
