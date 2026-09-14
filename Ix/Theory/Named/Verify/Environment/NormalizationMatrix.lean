/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Verify.Environment.InductiveFixtures

open Ix.Theory (VLevel)

/-!
# Normalization differential matrix

Executable and semantic replay for normalized inductives. The fixture deliberately
places reducible aliases at every inductive-analysis boundary, including a
Pi-producing alias around a recursive target.  This file observes the actual
kernel declarations, pins the exact analyzer output and its fuel boundary, and
then translates the same declarations into the Theory environment.
-/

namespace Ix.Theory.Named.InductiveReplayFixtures

open Lean Meta
open Ix.Theory.Named.InductiveFixtures

/-! ## Actual kernel metadata and executable analysis -/

def matrixBetaKernelDef : DefinitionVal := kernelDefVal% MatrixBetaAlias
def matrixLetKernelDef : DefinitionVal := kernelDefVal% MatrixLetAlias
def matrixPiKernelDef : DefinitionVal := kernelDefVal% MatrixPiAlias
def matrixIndexKernelDef : DefinitionVal := kernelDefVal% MatrixIndexAlias

def matrixBetaInfo : ConstantInfo := .defnInfo matrixBetaKernelDef
def matrixLetInfo : ConstantInfo := .defnInfo matrixLetKernelDef
def matrixPiInfo : ConstantInfo := .defnInfo matrixPiKernelDef
def matrixIndexInfo : ConstantInfo := .defnInfo matrixIndexKernelDef

def matrixRecMap : ConstMap :=
  typeFamilyAliasMap.insert ``RecAlias recAliasInfo

def matrixBetaMap : ConstMap :=
  matrixRecMap.insert ``MatrixBetaAlias matrixBetaInfo

def matrixLetMap : ConstMap :=
  matrixBetaMap.insert ``MatrixLetAlias matrixLetInfo

def matrixPiMap : ConstMap :=
  matrixLetMap.insert ``MatrixPiAlias matrixPiInfo

def matrixAliasMap : ConstMap :=
  matrixPiMap.insert ``MatrixIndexAlias matrixIndexInfo

theorem matrixRec_fresh :
    typeFamilyAliasMap.find? ``RecAlias = none := by
  rw [typeFamilyAliasMap, SMap.WF.find?_insert
    (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem matrixRecMap_wf : matrixRecMap.WF :=
  typeFamilyAliasMap_wf.insert _ _ matrixRec_fresh

theorem matrixBeta_fresh :
    matrixRecMap.find? ``MatrixBetaAlias = none := by
  rw [matrixRecMap, typeFamilyAliasMap_wf.find?_insert,
    typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem matrixBetaMap_wf : matrixBetaMap.WF :=
  matrixRecMap_wf.insert _ _ matrixBeta_fresh

theorem matrixLet_fresh :
    matrixBetaMap.find? ``MatrixLetAlias = none := by
  rw [matrixBetaMap, matrixRecMap_wf.find?_insert,
    matrixRecMap, typeFamilyAliasMap_wf.find?_insert,
    typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem matrixLetMap_wf : matrixLetMap.WF :=
  matrixBetaMap_wf.insert _ _ matrixLet_fresh

theorem matrixPi_fresh : matrixLetMap.find? ``MatrixPiAlias = none := by
  rw [matrixLetMap, matrixBetaMap_wf.find?_insert,
    matrixBetaMap, matrixRecMap_wf.find?_insert,
    matrixRecMap, typeFamilyAliasMap_wf.find?_insert,
    typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem matrixPiMap_wf : matrixPiMap.WF :=
  matrixLetMap_wf.insert _ _ matrixPi_fresh

theorem matrixIndex_fresh :
    matrixPiMap.find? ``MatrixIndexAlias = none := by
  rw [matrixPiMap, matrixLetMap_wf.find?_insert,
    matrixLetMap, matrixBetaMap_wf.find?_insert,
    matrixBetaMap, matrixRecMap_wf.find?_insert,
    matrixRecMap, typeFamilyAliasMap_wf.find?_insert,
    typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem matrixAliasMap_wf : matrixAliasMap.WF :=
  matrixPiMap_wf.insert _ _ matrixIndex_fresh

def matrixKernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_normalizationMatrix matrixAliasMap

def normalizationMatrixInfo : ConstantInfo :=
  kernelInductInfo% NormalizationMatrix

def normalizationMatrixMkInfo : ConstantInfo :=
  kernelCtorInfo% NormalizationMatrix.mk

def normalizationMatrixRecInfo : ConstantInfo :=
  kernelRecInfo% NormalizationMatrix.rec

def normalizationMatrixKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% NormalizationMatrix.rec 0

def normalizationMatrixKernelCtor : Constructor where
  name := normalizationMatrixMkInfo.name
  type := normalizationMatrixMkInfo.type

def normalizationMatrixKernelType : InductiveType where
  name := normalizationMatrixInfo.name
  type := normalizationMatrixInfo.type
  ctors := [normalizationMatrixKernelCtor]

theorem normalizationMatrix_kernel_family_name :
    normalizationMatrixInfo.name = ``NormalizationMatrix := rfl

theorem normalizationMatrix_kernel_ctor_name :
    normalizationMatrixMkInfo.name = ``NormalizationMatrix.mk := rfl

theorem normalizationMatrix_kernel_recursor_name :
    normalizationMatrixRecInfo.name = ``NormalizationMatrix.rec := rfl

theorem normalizationMatrix_kernel_constructor_shape :
    (match normalizationMatrixMkInfo with
    | .ctorInfo info => (info.numParams, info.numFields)
    | _ => (0, 0)) = (1, 8) := rfl

theorem normalizationMatrix_kernel_recursor_shape :
    (match normalizationMatrixRecInfo with
    | .recInfo info =>
      (info.numParams, info.numIndices, info.numMotives,
        info.numMinors, info.rules.length)
    | _ => (0, 0, 0, 0, 0)) = (1, 1, 1, 1, 1) := rfl

theorem normalizationMatrix_kernel_rule_exact :
    normalizationMatrixKernelRuleRhs =
    normalizationMatrixGenerationChecked.generatedRules[0].rhs := rfl

theorem normalizationMatrix_recursive_positions_exact :
    normalizationMatrixViewChecked.constructors[0].recursive.map
      (fun position => (position.fieldIndex, position.binders.length)) =
        [(4, 0), (5, 1), (6, 0), (7, 0)] := rfl

def matrixCandidateContext (fuel : Nat) : AddInductive.Context where
  env := matrixKernelEnv
  lparams := []
  safety := .safe
  allowPrimitive := false
  fuel := { inductiveFuel := fuel }

def matrixCandidateAccepted (fuel : Nat) : Bool :=
  match AddInductive.buildNormalizationCandidate 1
      [normalizationMatrixKernelType] 0 false (matrixCandidateContext fuel) with
  | .ok _ => true
  | .error _ => false

def matrixTargetExpr (alpha index : Expr) : Expr :=
  .app (.app (.const ``NormalizationMatrix []) alpha)
    (.app (.const ``MatrixIndexAlias []) index)

def matrixExpectedFamilyView : Expr :=
  .forallE `alpha (.sort (.succ .zero))
    (.forallE `index (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) .default) .default

def matrixExpectedCtorView : Expr :=
  .forallE `alpha (.sort (.succ .zero))
    (.forallE `index (.sort (.succ .zero))
      (.forallE `ordinary (.sort .zero)
        (.forallE `beta (.sort .zero)
          (.forallE `letBound (.sort .zero)
            (.forallE `direct (matrixTargetExpr (.bvar 4) (.bvar 3))
              (.forallE `piHidden
                (.forallE `proof (.sort .zero)
                  (matrixTargetExpr (.bvar 6) (.bvar 5)) .default)
                (.forallE `betaRecursive
                  (matrixTargetExpr (.bvar 6) (.bvar 5))
                  (.forallE `letRecursive
                    (matrixTargetExpr (.bvar 7) (.bvar 6))
                    (matrixTargetExpr (.bvar 8) (.bvar 7)) .default)
                  .default)
                .default)
              .default)
            .default)
          .default)
        .default)
      .default)
    .implicit

/-- Binder names are not semantic metadata, so exact executable comparisons
canonicalize only those names and preserve every other expression node. -/
def matrixCanonicalExpr : Expr → Expr
  | .app fn arg => .app (matrixCanonicalExpr fn) (matrixCanonicalExpr arg)
  | .forallE _ domain body bi =>
    .forallE `_ (matrixCanonicalExpr domain) (matrixCanonicalExpr body) bi
  | expr => expr

def matrixCandidateExact (context : AddInductive.Context) : Bool :=
  match AddInductive.buildNormalizationCandidate 1
      [normalizationMatrixKernelType] 0 false context with
  | .ok candidate =>
      (matrixCanonicalExpr candidate.families.singleton.familyType.type.view).equal
          (matrixCanonicalExpr matrixExpectedFamilyView) &&
        match candidate.families.singleton.constructors with
        | .cons constructor .nil =>
          (matrixCanonicalExpr constructor.type.view).equal
            (matrixCanonicalExpr matrixExpectedCtorView)
  | .error _ => false

#guard matrixCandidateExact (matrixCandidateContext 10)
#guard matrixCandidateAccepted 10
#guard !(matrixCandidateAccepted 9)

def matrixOpaquePiAliasInfo : ConstantInfo :=
  .axiomInfo {
    name := ``MatrixPiAlias
    levelParams := matrixPiKernelDef.levelParams
    type := matrixPiKernelDef.type
    isUnsafe := false }

def matrixOpaquePiAliasMap : ConstMap :=
  matrixAliasMap.insert ``MatrixPiAlias matrixOpaquePiAliasInfo

def matrixOpaquePiAliasContext : AddInductive.Context where
  env := Kernel.Environment.ofConstants `_normalizationMatrixOpaquePi
    matrixOpaquePiAliasMap
  lparams := []
  safety := .safe
  allowPrimitive := false
  fuel := { inductiveFuel := 10 }

#guard !(matrixCandidateExact matrixOpaquePiAliasContext)

def matrixNonDefEqCtor : Constructor where
  name := normalizationMatrixMkInfo.name
  type := .forallE `alpha (.sort .zero)
    (matrixTargetExpr (.sort .zero) (.sort .zero)) .implicit

def matrixNonDefEqType : InductiveType :=
  { normalizationMatrixKernelType with ctors := [matrixNonDefEqCtor] }

#guard match AddInductive.buildNormalizationCandidate 1
    [matrixNonDefEqType] 0 false (matrixCandidateContext 10) with
  | .error (.other message) =>
    message ==
      "arg #1 of 'Ix.Theory.Named.InductiveFixtures.NormalizationMatrix.mk' does not match inductive datatype parameters"
  | _ => false

/-! ## Translation of every retained alias -/

def matrixBetaVal : VDefVal where
  name := ``MatrixBetaAlias
  uvars := (vconst(type_of% @MatrixBetaAlias) : VConstant).uvars
  type := (vconst(type_of% @MatrixBetaAlias) : VConstant).type
  value := matrixBetaAliasDefEq.rhs

def matrixLetVal : VDefVal where
  name := ``MatrixLetAlias
  uvars := (vconst(type_of% @MatrixLetAlias) : VConstant).uvars
  type := (vconst(type_of% @MatrixLetAlias) : VConstant).type
  value := matrixLetAliasDefEq.rhs

def matrixPiVal : VDefVal where
  name := ``MatrixPiAlias
  uvars := (vconst(type_of% @MatrixPiAlias) : VConstant).uvars
  type := (vconst(type_of% @MatrixPiAlias) : VConstant).type
  value := matrixPiAliasDefEq.rhs

def matrixIndexVal : VDefVal where
  name := ``MatrixIndexAlias
  uvars := (vconst(type_of% @MatrixIndexAlias) : VConstant).uvars
  type := (vconst(type_of% @MatrixIndexAlias) : VConstant).type
  value := matrixIndexAliasDefEq.rhs

theorem matrixRecInfo_tr :
    TrDefVal .safe typeFamilyAliasEnv recAliasInfo recAliasVal :=
  recAliasInfo_tr.mono
    ((VEnv.addConst_le (by rfl :
      VEnv.empty.addConst ``TypeFamilyAlias
        (vconst(type_of% @TypeFamilyAlias)) =
          some typeFamilyAliasConstEnv)).trans VEnv.addDefEq_le)

theorem matrixBetaInfo_tr :
    TrDefVal .safe normalizationMatrixRecAliasEnv
      matrixBetaInfo matrixBetaVal := by
  refine ⟨⟨⟨by decide, rfl, ?_⟩, rfl⟩, ?_⟩
  · have hshape : TrTypeExpr normalizationMatrixRecAliasEnv
        matrixBetaInfo.levelParams [] matrixBetaInfo.type matrixBetaVal.type := by
      tr_type_expr_tac
    exact hshape.to_trExprS normalizationMatrixRecAliasEnv_ordered trivial
      ⟨_, by type_tac⟩
  · refine .lam ⟨_, VEnv.HasType.sort (by decide)⟩ (.sort rfl) ?_
    refine .app
      (VEnv.HasType.lam
        (VEnv.HasType.sort (by decide))
        (VEnv.HasType.bvar .zero))
      (VEnv.HasType.bvar .zero) ?_ (.bvar rfl)
    exact .lam ⟨_, VEnv.HasType.sort (by decide)⟩ (.sort rfl) (.bvar rfl)

theorem matrixLetInfo_tr :
    TrDefVal .safe normalizationMatrixBetaAliasEnv
      matrixLetInfo matrixLetVal := by
  refine ⟨⟨⟨by decide, rfl, ?_⟩, rfl⟩, ?_⟩
  · have hshape : TrTypeExpr normalizationMatrixBetaAliasEnv
        matrixLetInfo.levelParams [] matrixLetInfo.type matrixLetVal.type := by
      tr_type_expr_tac
    exact hshape.to_trExprS normalizationMatrixBetaAliasEnv_ordered trivial
      ⟨_, by type_tac⟩
  · refine .lam ⟨_, VEnv.HasType.sort (by decide)⟩ (.sort rfl) ?_
    exact .letE (by type_tac) (.sort rfl) (.bvar rfl) (.bvar rfl)

theorem matrixPiInfo_tr :
    TrDefVal .safe normalizationMatrixLetAliasEnv matrixPiInfo matrixPiVal := by
  refine ⟨⟨⟨by decide, rfl, ?_⟩, rfl⟩, ?_⟩
  · have hshape : TrTypeExpr normalizationMatrixLetAliasEnv
        matrixPiInfo.levelParams [] matrixPiInfo.type matrixPiVal.type := by
      tr_type_expr_tac
    exact hshape.to_trExprS normalizationMatrixLetAliasEnv_ordered trivial
      ⟨_, by type_tac⟩
  · refine .lam ⟨_, VEnv.HasType.sort (by decide)⟩ (.sort rfl) ?_
    apply TrExprS.forallE
    · exact ⟨_, VEnv.HasType.sort (by decide)⟩
    · exact ⟨.param 0, VEnv.HasType.bvar (.succ .zero)⟩
    · exact .sort rfl
    · exact .bvar rfl

theorem matrixIndexInfo_tr :
    TrDefVal .safe normalizationMatrixPiAliasEnv
      matrixIndexInfo matrixIndexVal := by
  have hfamily : normalizationMatrixPiAliasEnv.constants
      ``TypeFamilyAlias = some (vconst(type_of% @TypeFamilyAlias)) := rfl
  refine ⟨⟨⟨by decide, rfl, ?_⟩, rfl⟩, ?_⟩
  · have hshape : TrTypeExpr normalizationMatrixPiAliasEnv
        matrixIndexInfo.levelParams [] matrixIndexInfo.type matrixIndexVal.type := by
      tr_type_expr_tac
    exact hshape.to_trExprS normalizationMatrixPiAliasEnv_ordered trivial
      ⟨_, by type_tac⟩
  · refine .lam ⟨_, by type_tac⟩ ?_ (.bvar rfl)
    exact .const rfl rfl rfl

theorem matrixBetaVal_wf : matrixBetaVal.WF
    normalizationMatrixRecAliasEnv := by
  type_tac

theorem matrixLetVal_wf : matrixLetVal.WF
    normalizationMatrixBetaAliasEnv := by
  type_tac

theorem matrixPiVal_wf : matrixPiVal.WF
    normalizationMatrixLetAliasEnv := by
  apply VEnv.HasType.lam
  · exact VEnv.HasType.sort (by decide)
  · apply VEnv.IsDefEq.defeq
      (VEnv.IsDefEq.sortDF
        (l := .imax (.succ .zero) (.param 0)) (l' := .param 0)
        (by decide) (by decide) (by
          rw [VLevel.equiv_def]
          intro ls
          simp only [VLevel.eval, Nat.zero_add]
          let n := ls.getD 0 0
          change Nat.imax 1 n = n
          by_cases h : n = 0
          · simp [Nat.imax, h]
          · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
            simp [Nat.imax, h, Nat.max_eq_right hn]))
    exact VEnv.HasType.forallE (VEnv.HasType.sort (by decide))
      (VEnv.HasType.bvar (.succ .zero))

theorem matrixIndexVal_wf : matrixIndexVal.WF
    normalizationMatrixPiAliasEnv := by
  have hfamily : normalizationMatrixPiAliasEnv.constants
      ``TypeFamilyAlias = some (vconst(type_of% @TypeFamilyAlias)) := rfl
  type_tac

theorem matrixRec_trEnv' :
    TrEnv' .safe matrixRecMap false normalizationMatrixRecAliasEnv :=
  .defn (ci := recAliasKernelDef) (ci' := recAliasVal)
    matrixRecInfo_tr matrixRec_fresh
    (recAliasVal_wf.mono
      ((VEnv.addConst_le (by rfl :
        VEnv.empty.addConst ``TypeFamilyAlias
          (vconst(type_of% @TypeFamilyAlias)) =
            some typeFamilyAliasConstEnv)).trans VEnv.addDefEq_le))
    rfl typeFamilyAlias_trEnv'

theorem matrixBeta_trEnv' :
    TrEnv' .safe matrixBetaMap false normalizationMatrixBetaAliasEnv :=
  .defn (ci := matrixBetaKernelDef) (ci' := matrixBetaVal)
    matrixBetaInfo_tr matrixBeta_fresh matrixBetaVal_wf rfl matrixRec_trEnv'

theorem matrixLet_trEnv' :
    TrEnv' .safe matrixLetMap false normalizationMatrixLetAliasEnv :=
  .defn (ci := matrixLetKernelDef) (ci' := matrixLetVal)
    matrixLetInfo_tr matrixLet_fresh matrixLetVal_wf rfl matrixBeta_trEnv'

theorem matrixPi_trEnv' :
    TrEnv' .safe matrixPiMap false normalizationMatrixPiAliasEnv :=
  .defn (ci := matrixPiKernelDef) (ci' := matrixPiVal)
    matrixPiInfo_tr matrixPi_fresh matrixPiVal_wf rfl matrixLet_trEnv'

theorem matrixAlias_trEnv' :
    TrEnv' .safe matrixAliasMap false normalizationMatrixAliasEnv :=
  .defn (ci := matrixIndexKernelDef) (ci' := matrixIndexVal)
    matrixIndexInfo_tr matrixIndex_fresh matrixIndexVal_wf rfl matrixPi_trEnv'

/-! ## Replay of the actual inductive transaction -/

def normalizationMatrixTypeEnv : VEnv :=
  (normalizationMatrixAliasEnv.addConst normalizationMatrixRawType.name
    normalizationMatrixRawType.toVConstant).get (by decide)

def normalizationMatrixCtorEnv : VEnv :=
  (normalizationMatrixTypeEnv.addConst
    normalizationMatrixRawType.ctors[0].name
    normalizationMatrixRawType.ctors[0].toVConstant).get (by decide)

def normalizationMatrixRecEnv : VEnv :=
  (normalizationMatrixCtorEnv.addConst ``NormalizationMatrix.rec
    normalizationMatrixGenerationChecked.recursor).get (by decide)

theorem normalizationMatrixTypeEnv_ordered :
    normalizationMatrixTypeEnv.Ordered := by
  refine .const (n := normalizationMatrixRawType.name)
    (ci := normalizationMatrixRawType.toVConstant)
    normalizationMatrixAliasEnv_ordered ?_ rfl
  show normalizationMatrixAliasEnv.IsType
    normalizationMatrixGenerationChecked.block.sourceType.uvars []
    normalizationMatrixGenerationChecked.block.sourceType.type
  rw [normalizationMatrixGenerationChecked.block.sourceType_uvars_eq]
  exact normalizationMatrixGenerationChecked_wf.rawFamily_isType

theorem normalizationMatrixRawCtor_wf :
    normalizationMatrixRawType.ctors[0].toVConstant.WF
      normalizationMatrixTypeEnv := by
  have hctor :
      (⟨normalizationMatrixRawType.ctors[0],
        normalizationMatrixViewChecked.constructors[0]⟩ :
          VInductDecl.NormalizedCtor) ∈
        normalizationMatrixGenerationChecked.block.ctorPairs := by
    exact .head _
  show normalizationMatrixTypeEnv.IsType
    normalizationMatrixRawType.ctors[0].uvars []
    normalizationMatrixRawType.ctors[0].type
  rw [normalizationMatrixGenerationChecked.ctor_uvars_eq hctor]
  exact normalizationMatrixGenerationChecked_wf.rawCtor_isType rfl hctor

theorem normalizationMatrixCtorEnv_ordered :
    normalizationMatrixCtorEnv.Ordered :=
  .const (n := normalizationMatrixRawType.ctors[0].name)
    (ci := normalizationMatrixRawType.ctors[0].toVConstant)
    normalizationMatrixTypeEnv_ordered normalizationMatrixRawCtor_wf rfl

theorem normalizationMatrixGenerationEnv :
    VInductDecl.GenerationEnv normalizationMatrixGenerationChecked
      normalizationMatrixCtorEnv := by
  apply normalizationMatrixGenerationChecked_wf.toGenerationEnv
    (envT := normalizationMatrixTypeEnv)
  · rfl
  · exact (VEnv.addConst_le (show
      normalizationMatrixAliasEnv.addConst normalizationMatrixRawType.name
        normalizationMatrixRawType.toVConstant =
          some normalizationMatrixTypeEnv from rfl)).trans
      (VEnv.addConst_le (show
        normalizationMatrixTypeEnv.addConst
          normalizationMatrixRawType.ctors[0].name
          normalizationMatrixRawType.ctors[0].toVConstant =
            some normalizationMatrixCtorEnv from rfl))
  · exact VEnv.addConst_le (show
      normalizationMatrixTypeEnv.addConst
        normalizationMatrixRawType.ctors[0].name
        normalizationMatrixRawType.ctors[0].toVConstant =
          some normalizationMatrixCtorEnv from rfl)
  · exact normalizationMatrixCtorEnv_ordered
  · rfl
  · intro ctor hctor
    change ctor ∈
      [⟨normalizationMatrixRawType.ctors[0],
        normalizationMatrixViewChecked.constructors[0]⟩] at hctor
    obtain rfl := List.mem_singleton.1 hctor
    rfl

theorem normalizationMatrixInfo_tr :
    TrConstVal .safe normalizationMatrixAliasEnv normalizationMatrixInfo
      normalizationMatrixRawType.toVConstVal := by
  have hTypeFamily : normalizationMatrixAliasEnv.constants
      ``TypeFamilyAlias = some (vconst(type_of% @TypeFamilyAlias)) := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr normalizationMatrixAliasEnv
      normalizationMatrixInfo.levelParams [] normalizationMatrixInfo.type
      normalizationMatrixRawType.type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ :=
    normalizationMatrixGenerationChecked_wf.rawFamily_isType
  exact hshape.to_trExprS normalizationMatrixAliasEnv_ordered trivial
    ⟨.sort u, htype⟩

theorem normalizationMatrixMkInfo_tr :
    TrConstVal .safe normalizationMatrixTypeEnv normalizationMatrixMkInfo
      normalizationMatrixRawType.ctors[0] := by
  have hTypeFamily : normalizationMatrixTypeEnv.constants
      ``TypeFamilyAlias = some (vconst(type_of% @TypeFamilyAlias)) := rfl
  have hRecAlias : normalizationMatrixTypeEnv.constants
      ``RecAlias = some (vconst(type_of% @RecAlias)) := rfl
  have hBetaAlias : normalizationMatrixTypeEnv.constants
      ``MatrixBetaAlias = some (vconst(type_of% @MatrixBetaAlias)) := rfl
  have hLetAlias : normalizationMatrixTypeEnv.constants
      ``MatrixLetAlias = some (vconst(type_of% @MatrixLetAlias)) := rfl
  have hPiAlias : normalizationMatrixTypeEnv.constants
      ``MatrixPiAlias = some (vconst(type_of% @MatrixPiAlias)) := rfl
  have hIndexAlias : normalizationMatrixTypeEnv.constants
      ``MatrixIndexAlias = some (vconst(type_of% @MatrixIndexAlias)) := rfl
  have hFamily : normalizationMatrixTypeEnv.constants
      ``NormalizationMatrix = some normalizationMatrixRawType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr normalizationMatrixTypeEnv
      normalizationMatrixMkInfo.levelParams [] normalizationMatrixMkInfo.type
      normalizationMatrixRawType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := normalizationMatrixRawCtor_wf
  exact hshape.to_trExprS normalizationMatrixTypeEnv_ordered trivial
    ⟨.sort u, htype⟩

theorem normalizationMatrixRecInfo_tr :
    TrConstVal .safe normalizationMatrixCtorEnv normalizationMatrixRecInfo
      (inductGenerationRecVal normalizationMatrixGenerationChecked) := by
  have hTypeFamily : normalizationMatrixCtorEnv.constants
      ``TypeFamilyAlias = some (vconst(type_of% @TypeFamilyAlias)) := rfl
  have hIndexAlias : normalizationMatrixCtorEnv.constants
      ``MatrixIndexAlias = some (vconst(type_of% @MatrixIndexAlias)) := rfl
  have hFamily : normalizationMatrixCtorEnv.constants
      ``NormalizationMatrix = some normalizationMatrixRawType.toVConstant := rfl
  have hMk : normalizationMatrixCtorEnv.constants
      ``NormalizationMatrix.mk =
        some normalizationMatrixRawType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr normalizationMatrixCtorEnv
      normalizationMatrixRecInfo.levelParams [] normalizationMatrixRecInfo.type
      (inductGenerationRecVal normalizationMatrixGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨u, hrec⟩ := normalizationMatrixGenerationEnv.recursor_wf
  exact hshape.to_trExprS normalizationMatrixCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

def normalizationMatrixTypeMap : ConstMap :=
  matrixAliasMap.insert ``NormalizationMatrix normalizationMatrixInfo

def normalizationMatrixCtorMap : ConstMap :=
  normalizationMatrixTypeMap.insert ``NormalizationMatrix.mk
    normalizationMatrixMkInfo

def normalizationMatrixMap : ConstMap :=
  normalizationMatrixCtorMap.insert ``NormalizationMatrix.rec
    normalizationMatrixRecInfo

theorem normalizationMatrixType_fresh :
    matrixAliasMap.find? ``NormalizationMatrix = none := by
  rw [matrixAliasMap, matrixPiMap_wf.find?_insert,
    matrixPiMap, matrixLetMap_wf.find?_insert,
    matrixLetMap, matrixBetaMap_wf.find?_insert,
    matrixBetaMap, matrixRecMap_wf.find?_insert,
    matrixRecMap, typeFamilyAliasMap_wf.find?_insert,
    typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem normalizationMatrixTypeMap_wf : normalizationMatrixTypeMap.WF :=
  matrixAliasMap_wf.insert _ _ normalizationMatrixType_fresh

theorem normalizationMatrixMk_fresh :
    normalizationMatrixTypeMap.find? ``NormalizationMatrix.mk = none := by
  rw [normalizationMatrixTypeMap, matrixAliasMap_wf.find?_insert,
    matrixAliasMap, matrixPiMap_wf.find?_insert,
    matrixPiMap, matrixLetMap_wf.find?_insert,
    matrixLetMap, matrixBetaMap_wf.find?_insert,
    matrixBetaMap, matrixRecMap_wf.find?_insert,
    matrixRecMap, typeFamilyAliasMap_wf.find?_insert,
    typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem normalizationMatrixCtorMap_wf : normalizationMatrixCtorMap.WF :=
  normalizationMatrixTypeMap_wf.insert _ _ normalizationMatrixMk_fresh

theorem normalizationMatrixRec_fresh :
    normalizationMatrixCtorMap.find? ``NormalizationMatrix.rec = none := by
  rw [normalizationMatrixCtorMap,
    normalizationMatrixTypeMap_wf.find?_insert,
    normalizationMatrixTypeMap, matrixAliasMap_wf.find?_insert,
    matrixAliasMap, matrixPiMap_wf.find?_insert,
    matrixPiMap, matrixLetMap_wf.find?_insert,
    matrixLetMap, matrixBetaMap_wf.find?_insert,
    matrixBetaMap, matrixRecMap_wf.find?_insert,
    matrixRecMap, typeFamilyAliasMap_wf.find?_insert,
    typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

private def normalizationMatrixAddInductTraceWith
    (generation_wf :
      normalizationMatrixGenerationChecked.WF normalizationMatrixAliasEnv) :
    AddInductTrace matrixAliasMap normalizationMatrixAliasEnv
      normalizationMatrixRawDecl normalizationMatrixMap
      normalizationMatrixFinalEnv := by
  refine {
    generation := normalizationMatrixGenerationChecked
    generation_wf := generation_wf
    typeMap := normalizationMatrixTypeMap
    typeEnv := normalizationMatrixTypeEnv
    ctorMap := normalizationMatrixCtorMap
    ctorEnv := normalizationMatrixCtorEnv
    recEnv := normalizationMatrixRecEnv
    addType := {
      info := normalizationMatrixInfo
      kind_eq := by simp [normalizationMatrixInfo, InductConstantKind.Matches]
      tr := normalizationMatrixInfo_tr
      map_fresh := by
        change matrixAliasMap.find? ``NormalizationMatrix = none
        exact normalizationMatrixType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := normalizationMatrixRecInfo
      kind_eq := by
        simp [normalizationMatrixRecInfo, InductConstantKind.Matches]
      tr := normalizationMatrixRecInfo_tr
      map_fresh := by
        change normalizationMatrixCtorMap.find?
          ``NormalizationMatrix.rec = none
        exact normalizationMatrixRec_fresh
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }
  exact .cons {
    info := normalizationMatrixMkInfo
    kind_eq := by
      simp [normalizationMatrixMkInfo, InductConstantKind.Matches]
    tr := normalizationMatrixMkInfo_tr
    map_fresh := by
      simpa [normalizationMatrixRawType] using normalizationMatrixMk_fresh
    env_add := rfl
    map_add := rfl } .nil

theorem normalizationMatrix_addInduct :
    AddInduct matrixAliasMap normalizationMatrixAliasEnv
      normalizationMatrixRawDecl normalizationMatrixMap
      normalizationMatrixFinalEnv :=
  ⟨normalizationMatrixAddInductTraceWith
    normalizationMatrixGenerationChecked_wf⟩

/-- Actual kernel metadata for the complete matrix is aligned with the Theory
environment obtained from the semantically checked normalization transaction. -/
theorem normalizationMatrix_trEnv' :
    TrEnv' .safe normalizationMatrixMap false normalizationMatrixFinalEnv :=
  .induct normalizationMatrix_addInduct matrixAlias_trEnv'

theorem normalizationMatrix_final_matches_generation :
    normalizationMatrixAliasEnv.addInductGeneration
      normalizationMatrixGenerationChecked =
        some normalizationMatrixFinalEnv :=
  normalizationMatrix_addInductGeneration

theorem normalizationMatrix_env_wf : normalizationMatrixFinalEnv.WF :=
  normalizationMatrix_trEnv'.wf

theorem normalizationMatrix_aligned :
    Aligned .safe normalizationMatrixMap normalizationMatrixFinalEnv :=
  normalizationMatrix_trEnv'.aligned

theorem normalizationMatrix_type_map_lookup :
    normalizationMatrixMap.find? ``NormalizationMatrix =
      some normalizationMatrixInfo := by
  rw [normalizationMatrixMap, normalizationMatrixCtorMap_wf.find?_insert,
    normalizationMatrixCtorMap, normalizationMatrixTypeMap_wf.find?_insert,
    normalizationMatrixTypeMap, matrixAliasMap_wf.find?_insert]
  rfl

theorem normalizationMatrix_type_lookup_unique :
    normalizationMatrixInfo.name = ``NormalizationMatrix ∧
      TrConstant .safe normalizationMatrixFinalEnv normalizationMatrixInfo
        normalizationMatrixRawType.toVConstant :=
  normalizationMatrix_aligned.find?_uniq
    normalizationMatrix_type_map_lookup
    normalizationMatrixFinalEnv_family_lookup

theorem normalizationMatrix_mk_map_lookup :
    normalizationMatrixMap.find? ``NormalizationMatrix.mk =
      some normalizationMatrixMkInfo := by
  rw [normalizationMatrixMap, normalizationMatrixCtorMap_wf.find?_insert,
    normalizationMatrixCtorMap, normalizationMatrixTypeMap_wf.find?_insert]
  rfl

theorem normalizationMatrix_mk_lookup_unique :
    normalizationMatrixMkInfo.name = ``NormalizationMatrix.mk ∧
      TrConstant .safe normalizationMatrixFinalEnv normalizationMatrixMkInfo
        normalizationMatrixRawType.ctors[0].toVConstant :=
  normalizationMatrix_aligned.find?_uniq
    normalizationMatrix_mk_map_lookup
    normalizationMatrixFinalEnv_ctor_lookup

theorem normalizationMatrix_rec_map_lookup :
    normalizationMatrixMap.find? ``NormalizationMatrix.rec =
      some normalizationMatrixRecInfo := by
  rw [normalizationMatrixMap, normalizationMatrixCtorMap_wf.find?_insert]
  rfl

theorem normalizationMatrix_rec_lookup_unique :
    normalizationMatrixRecInfo.name = ``NormalizationMatrix.rec ∧
      TrConstant .safe normalizationMatrixFinalEnv normalizationMatrixRecInfo
        normalizationMatrixGenerationChecked.recursor :=
  normalizationMatrix_aligned.find?_uniq
    normalizationMatrix_rec_map_lookup
    normalizationMatrixFinalEnv_rec_lookup

/-! The semantic generation helpers used above are guarded in
`Theory.Typing.InductiveLemmas`; these two guards pin the separate, now
`sorryAx`-free Verify closure of metadata translation and final environment
replay. -/

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.normalizationMatrixInfo_tr [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.normalizationMatrix_trEnv' [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

end Ix.Theory.Named.InductiveReplayFixtures
