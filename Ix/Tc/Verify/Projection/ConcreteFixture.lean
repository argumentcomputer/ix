import Ix.Tc.Verify.Projection.Concrete
import Lean4Lean.Tests.ProjectionExpressibility

/-!
# Production-syntax fixture for the concrete projection relation

This fixture connects an actual Ix `KExpr.mkPrj` node to Lean4Lean's
universe-polymorphic, dependent `DependentRecord` projection fixture.  The
major is the leading local variable in the exact Theory context retained by
the registered structure view; the result is the recursor-encoded key
projector computed by that view.

Unlike the projection-miss fixture in `NatFixture`, no identity relation is
invented here.  Both raw and typed Ix translation consume the concrete
environment-indexed `TrProj` witness, and the acceptance theorem packages the
real adapter laws with that production syntax node.
-/

namespace Ix.Tc.ConcreteProjectionFixture

open Lean4Lean (VExpr VLocalDecl)
open Lean4Lean.Tests.ProjectionExpressibility

def structureAddress : Address :=
  ⟨⟨Array.replicate 32 64⟩⟩

def structureId : KId .anon := ⟨structureAddress, ()⟩

def nameOf : Address → Option Lean.Name := fun address =>
  if address == structureAddress then some ``DependentRecord else none

theorem nameOf_structure :
    nameOf structureAddress = some ``DependentRecord := by
  simp [nameOf]

abbrev projectionRel :=
  Ix.Tc.RawProjRel.lean4Lean dependentRecordEnv

theorem projectionLaws :
    TrProjOK dependentRecordEnv 2 projectionRel :=
  Ix.Tc.RawProjRel.lean4Lean_ok dependentRecordEnv_wf 2

/-- The Verify compatibility witness exposing the registered key projection
through the concrete relation used by Ix. -/
theorem keyProjection :
    projectionRel 2 symbolicContext ``DependentRecord 0 symbolicMajor
      symbolicKeyResult := by
  exact ⟨dependentRecordView, symbolicLevels, symbolicMajorParams, rfl,
    key_representable⟩

/-- The mixed Ix context corresponding definitionally to Lean4Lean's
`[major, family, α]` Theory context. -/
def context : KVLCtx :=
  [(none, .vlam symbolicMajorBinderType),
    (none, .vlam symbolicFamilyType),
    (none, .vlam symbolicAlphaType)]

@[simp] theorem context_toCtx : context.toCtx = symbolicContext := rfl

theorem contextWF : KVLCtx.WF dependentRecordEnv 2 context := by
  refine ⟨?_, by simp, symbolicMajorBinder_isType⟩
  refine ⟨?_, by simp, ?_⟩
  · refine ⟨trivial, by simp, ?_⟩
    exact ⟨_, by type_tac⟩
  · exact ⟨_, by type_tac⟩

def major : KExpr .anon := KExpr.mkVar 0 ()

def source : KExpr .anon := KExpr.mkPrj structureId 0 major

theorem sourceConstructed : source.Constructed := by
  exact .prj (.var (by decide))

theorem majorRaw :
    _root_.Ix.Tc.RawExprRel (uvars := 2) dependentRecordEnv nameOf projectionRel
      symbolicContext major symbolicMajor := by
  unfold major
  rw [KExpr.mkVar_shape]
  exact .var

theorem sourceRaw :
    _root_.Ix.Tc.RawExprRel (uvars := 2) dependentRecordEnv nameOf projectionRel
      symbolicContext source symbolicKeyResult := by
  unfold source
  rw [KExpr.mkPrj_shape]
  exact .prj nameOf_structure dependentRecord_view_wf.family majorRaw
    keyProjection

theorem majorStructural :
    TrKExprS dependentRecordEnv 2 nameOf projectionRel context major
      symbolicMajor := by
  unfold major
  rw [KExpr.mkVar_shape]
  exact .var rfl

theorem sourceStructural :
    TrKExprS dependentRecordEnv 2 nameOf projectionRel context source
      symbolicKeyResult := by
  unfold source
  rw [KExpr.mkPrj_shape]
  exact .prj nameOf_structure majorStructural keyProjection

/-- The same concrete projection survives an increased universe budget via
the Ix capability derived from Lean4Lean universe instantiation. -/
theorem keyProjectionAtThree :
    projectionRel 3 symbolicContext ``DependentRecord 0 symbolicMajor
      symbolicKeyResult :=
  (Ix.Tc.RawProjRel.lean4Lean_ok dependentRecordEnv_wf 3).monoU
    (by omega) contextWF.toCtx keyProjection

/-- P0's concrete vertical slice: a smart-constructor-built Ix projection is
represented both at the raw ingress boundary and at the typed structural
boundary, using the real registered projection relation and its complete Ix
law bundle. -/
theorem acceptance :
    source.Constructed ∧
      _root_.Ix.Tc.RawExprRel (uvars := 2) dependentRecordEnv nameOf projectionRel
        symbolicContext source symbolicKeyResult ∧
      TrKExprS dependentRecordEnv 2 nameOf projectionRel context source
        symbolicKeyResult ∧
      TrProjOK dependentRecordEnv 2 projectionRel ∧
      projectionRel 3 symbolicContext ``DependentRecord 0 symbolicMajor
        symbolicKeyResult :=
  ⟨sourceConstructed, sourceRaw, sourceStructural, projectionLaws,
    keyProjectionAtThree⟩

end Ix.Tc.ConcreteProjectionFixture
