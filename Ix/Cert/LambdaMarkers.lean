import Ix.Cert.ConversionValues

/-! # Lambda markers from real checks against one expected type

Two actual value fronts checked against the same header put their lambda
values in one interpreted product. A graph lambda cannot be a proof point,
and a positive product cannot contain that point, even at an empty domain.
This gives marker agreement within each supplied strong model, without
typing uniqueness, an inhabited binder context or a model-existence axiom.

The header inputs are only its actual syntax/annotation/full-inference
facts. They are available from ConstantValRun, without requiring its fresh
name guards here. No conversion between the values is checked or assumed.
-/

namespace Ix.Cert.LambdaMarkers

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model Ix.Kernel.SetModel
open Ix.Kernel.SetTheory
open Ix.Kernel.Model.Rules (Frame Graded)
open ConversionValues

universe w
variable {md : Mode} {V : Type w} [SetTheory V] {env : Ix.Kernel.Env md}

/-- Product membership fixes a lambda's regime, for arbitrary domains,
including empty ones. No element of either domain is chosen. -/
theorem lam_mem_pi_bits {leftBit rightBit : Nat} {A D : V} {F B : V → V}
    (member : lamR rightBit D F ∈ˢ piR leftBit A B) :
    leftBit = 0 ↔ rightBit = 0 := by
  constructor
  · intro zero
    by_contra positive
    rw [zero] at member
    exact (lamR_ne_pt positive) (eq_pt_of_mem_piR_zero member)
  · intro zero
    by_contra positive
    rw [zero, lamR_zero] at member
    exact not_pt_mem_piR_pos positive member

/-- Real full inference supplies both readings, their grading, the type's
frame and actual membership at every closed outer valuation. -/
theorem infer_package (M : Cached.StrongModel V env) (φ : LevelParam → Nat)
    {e type : Ix.Kernel.Expr md} {F : Nat} (frame : Frame 0 e)
    (run : inferTypeCore .verified env F 0 e = .ok type) :
    ∃ ea ta,
      denoteMeta M.internal.base2.acval env φ 0 e = some ea ∧
      denoteMeta M.internal.base2.acval env φ 0 type = some ta ∧
      Frame 0 type ∧ Graded V [] ea ∧ Graded V [] ta ∧
      ∀ ρ : BVarIdx → V, interp V ρ ea ∈ˢ interp V ρ ta := by
  obtain ⟨ea, read, _⟩ := infer_reading M φ frame run
  obtain ⟨typeFrame, _, ta, typeRead, grade, typeGrade, member⟩ :=
    Model.Rules.infer_sound (Model.Rules.RulesInputs.ofSem M.internal φ)
      (Ix.Kernel.Rules.inferTypeCore_bridge run) frame (frame_context M φ frame) read
  exact ⟨ea, ta, read, typeRead, typeFrame, grade, typeGrade,
    fun ρ => member ρ (Sat_nil V ρ)⟩

/-- BOTH real value fronts are checked against the same actual header.
The returned marker equality is under the supplied StrongModel parameter;
it is not obtained by inventing a model or inhabiting the binder domain.
Written/computed, fast/slow and Prop/non-Prop annotation paths are uniform:
the real full checks establish the membership used here. -/
theorem lambda_markers_eq_of_fronts (M : Cached.StrongModel V env)
    {cv : Ix.Kernel.ConstantVal md} {expected headerSortType rawL rawR : Ix.Kernel.Expr md}
    {domL bodyL domR bodyR : Ix.Kernel.Expr md} {mL mR : BinderMeta}
    {FA FT FL FR : Nat}
    (headerClosed : cv.type.hasFvar = false)
    (headerBounded : cv.type.looseBVarsBounded 0 = true)
    (headerAnn : annotateCore .verified env FA 0 cv.type = .ok expected)
    (headerInfer : inferTypeCore .verified env FT 0 expected = .ok headerSortType)
    (left : ValueFrontRun .verified FL env cv rawL expected (.lam domL bodyL mL))
    (right : ValueFrontRun .verified FR env cv rawR expected (.lam domR bodyR mR)) :
    mL.pw = mR.pw := by
  have headerFrame := annotation_frame headerAnn headerClosed headerBounded
  have leftFrame := valueFront_frame left
  have rightFrame := valueFront_frame right
  obtain ⟨leftType, leftInfer, leftCheck⟩ := left.2.2.2.2.2
  obtain ⟨rightType, rightInfer, rightCheck⟩ := right.2.2.2.2.2
  obtain ⟨cod, rfl⟩ := Ix.Kernel.Rules.Infer.lam_shape
    (Ix.Kernel.Rules.inferTypeCore_bridge leftInfer)
  apply PropWhen.eq_of_holds
  intro φ
  let ρ : BVarIdx → V := fun _ => SetTheory.empty
  obtain ⟨ha, headerRead, headerGrade⟩ := infer_reading M φ headerFrame headerInfer
  obtain ⟨la, lta, _, leftTypeRead, leftTypeFrame, _, leftTypeGrade, _⟩ :=
    infer_package M φ leftFrame leftInfer
  obtain ⟨ra, rta, rightRead, rightTypeRead, rightTypeFrame, _, rightTypeGrade, rightMember⟩ :=
    infer_package M φ rightFrame rightInfer
  have inputs := Model.Rules.RulesInputs.ofSem M.internal φ
  have leftEq := Model.Rules.defeq_sound inputs (Ix.Kernel.Rules.isDefEqCore_bridge leftCheck)
    leftTypeFrame headerFrame (frame_context M φ leftTypeFrame) (frame_context M φ headerFrame)
    leftTypeRead headerRead leftTypeGrade headerGrade ρ (Sat_nil V ρ)
  have rightEq := Model.Rules.defeq_sound inputs (Ix.Kernel.Rules.isDefEqCore_bridge rightCheck)
    rightTypeFrame headerFrame (frame_context M φ rightTypeFrame) (frame_context M φ headerFrame)
    rightTypeRead headerRead rightTypeGrade headerGrade ρ (Sat_nil V ρ)
  have member : interp V ρ ra ∈ˢ interp V ρ lta := by
    rw [leftEq, ← rightEq]
    exact rightMember ρ
  obtain ⟨rd, rb, _, _, rightShape⟩ := denoteMeta_lam_inv rightRead
  obtain ⟨ld, lb, _, _, leftShape⟩ := denoteMeta_forallE_inv leftTypeRead
  rw [rightShape, leftShape, interp_lam, interp_pi] at member
  have bits := lam_mem_pi_bits member
  exact Bool.eq_iff_iff.mpr (by simpa only [pwBit_eq_zero_iff] using bits)

end Ix.Cert.LambdaMarkers
