import Ix.Cert.LambdaMarkers

/-! # Actual checked values from rule inputs at one interpretation

Successful whole inference supplies readings and grading from EnvModel and
RulesInputs alone. Root marker compatibility uses actual checks against one
header; no prefix StrongModel, chosen binder element or semantic premise.
-/

namespace Ix.Cert.RuleInputValues

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model Ix.Kernel.SetModel
open Ix.Kernel.SetTheory
open Ix.Kernel.Model.Rules (Frame Graded RulesInputs)
open ConversionValues (frame_not_hasFvar annotation_frame valueFront_frame)

universe w
variable {md : Mode} {V : Type w} [SetTheory V] {env : Ix.Kernel.Env md}

/-- Closed syntax supplies the root context for any fixed carrier. -/
theorem frame_context (m : EnvModel V env) (φ : LevelParam → Nat)
    {e : Ix.Kernel.Expr md} (frame : Frame 0 e) : CtxOk m φ 0 [] e :=
  CtxOk.nil (Ix.Kernel.Expr.fvarLeaves_eq_nil_of_not_hasFvar (frame_not_hasFvar frame))

/-- The actual full run supplies both reads, type frame, grades and
membership. The soundness input is exactly the existing rule bundle. -/
theorem infer_package (m : EnvModel V env) (φ : LevelParam → Nat) (inputs : RulesInputs V m φ)
    {e type : Ix.Kernel.Expr md} {F : Nat} (frame : Frame 0 e)
    (run : inferTypeCore .verified env F 0 e = .ok type) :
    ∃ ea ta,
      denoteMeta m.acval env φ 0 e = some ea ∧
      denoteMeta m.acval env φ 0 type = some ta ∧
      Frame 0 type ∧ Graded V [] ea ∧ Graded V [] ta ∧
      ∀ ρ : BVarIdx → V, interp V ρ ea ∈ˢ interp V ρ ta := by
  obtain ⟨ea, read⟩ := acceptedReads_of m φ run frame.1 frame.2.1 frame.2.2
  obtain ⟨typeFrame, _, ta, typeRead, grade, typeGrade, member⟩ :=
    Model.Rules.infer_sound inputs (Ix.Kernel.Rules.inferTypeCore_bridge run)
      frame (frame_context m φ frame) read
  exact ⟨ea, ta, read, typeRead, typeFrame, grade, typeGrade,
    fun ρ => member ρ (Sat_nil V ρ)⟩

/-- The reading denotes the checked subject itself at the carrier's cval.
Only closed leaves, the actual frame/read and its grade are used. -/
theorem reading_denotes (m : EnvModel V env) {φ : LevelParam → Nat}
    {e : Ix.Kernel.Expr md} {ea : AnnotTerm} (frame : Frame 0 e)
    (read : denoteMeta m.acval env φ 0 e = some ea) (grade : Graded V [] ea)
    (ρ : BVarIdx → V) : Denotes (cvalOf m.acval) env φ ρ e (interp V ρ ea) := by
  have value := Denotes_of_denoteMeta m.cval_closedL 0 e read
    frame.1.fvarsBelow frame.2.1 ρ (grade ρ (Sat_nil V ρ))
  simpa only [Ix.Kernel.Expr.closeN_of_hasFvar _ 0 0 (frame_not_hasFvar frame)] using value

/-- Both real whole fronts supply the reads/grades. Static conversion is
an internal pass-proof input, not an added compiler equality check. -/
theorem defeq_readings (m : EnvModel V env) (φ : LevelParam → Nat) (inputs : RulesInputs V m φ)
    {cvA cvB : Ix.Kernel.ConstantVal md} {rawA rawB typeA typeB a b : Ix.Kernel.Expr md}
    {FA FB : Nat} (left : ValueFrontRun .verified FA env cvA rawA typeA a)
    (right : ValueFrontRun .verified FB env cvB rawB typeB b)
    (conversion : Ix.Kernel.Rules.DefEq env 0 a b) :
    ∃ aa ba,
      denoteMeta m.acval env φ 0 a = some aa ∧ denoteMeta m.acval env φ 0 b = some ba ∧
      Graded V [] aa ∧ Graded V [] ba ∧
      ∀ ρ : BVarIdx → V, interp V ρ aa = interp V ρ ba := by
  obtain ⟨_, inferA, _⟩ := left.2.2.2.2.2
  obtain ⟨_, inferB, _⟩ := right.2.2.2.2.2
  have frameA := valueFront_frame left
  have frameB := valueFront_frame right
  obtain ⟨aa, _, readA, _, _, gradeA, _, _⟩ := infer_package m φ inputs frameA inferA
  obtain ⟨ba, _, readB, _, _, gradeB, _, _⟩ := infer_package m φ inputs frameB inferB
  exact ⟨aa, ba, readA, readB, gradeA, gradeB, fun ρ =>
    Model.Rules.defeq_sound inputs conversion frameA frameB
      (frame_context m φ frameA) (frame_context m φ frameB)
      readA readB gradeA gradeB ρ (Sat_nil V ρ)⟩

/-- Real root checks against the SAME header fix both lambda regimes.
All level assignments use the same carrier; no inner context is inhabited. -/
theorem lambda_markers_eq_of_fronts (m : EnvModel V env) (inputs : ∀ φ, RulesInputs V m φ)
    {cv : Ix.Kernel.ConstantVal md} {expected headerSortType rawL rawR : Ix.Kernel.Expr md}
    {domL bodyL domR bodyR : Ix.Kernel.Expr md} {mL mR : BinderMeta} {FA FT FL FR : Nat}
    (headerClosed : cv.type.hasFvar = false) (headerBounded : cv.type.looseBVarsBounded 0 = true)
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
  obtain ⟨cod, rfl⟩ := Ix.Kernel.Rules.Infer.lam_shape (Ix.Kernel.Rules.inferTypeCore_bridge leftInfer)
  apply PropWhen.eq_of_holds
  intro φ
  let ρ : BVarIdx → V := fun _ => SetTheory.empty
  obtain ⟨ha, _, headerRead, _, _, headerGrade, _, _⟩ :=
    infer_package m φ (inputs φ) headerFrame headerInfer
  obtain ⟨_, lta, _, leftTypeRead, leftTypeFrame, _, leftTypeGrade, _⟩ :=
    infer_package m φ (inputs φ) leftFrame leftInfer
  obtain ⟨ra, rta, rightRead, rightTypeRead, rightTypeFrame, _, rightTypeGrade, rightMember⟩ :=
    infer_package m φ (inputs φ) rightFrame rightInfer
  have leftEq := Model.Rules.defeq_sound (inputs φ) (Ix.Kernel.Rules.isDefEqCore_bridge leftCheck)
    leftTypeFrame headerFrame (frame_context m φ leftTypeFrame) (frame_context m φ headerFrame)
    leftTypeRead headerRead leftTypeGrade headerGrade ρ (Sat_nil V ρ)
  have rightEq := Model.Rules.defeq_sound (inputs φ) (Ix.Kernel.Rules.isDefEqCore_bridge rightCheck)
    rightTypeFrame headerFrame (frame_context m φ rightTypeFrame) (frame_context m φ headerFrame)
    rightTypeRead headerRead rightTypeGrade headerGrade ρ (Sat_nil V ρ)
  have member : interp V ρ ra ∈ˢ interp V ρ lta := by
    rw [leftEq, ← rightEq]
    exact rightMember ρ
  obtain ⟨_, _, _, _, rightShape⟩ := denoteMeta_lam_inv rightRead
  obtain ⟨_, _, _, _, leftShape⟩ := denoteMeta_forallE_inv leftTypeRead
  rw [rightShape, leftShape, interp_lam, interp_pi] at member
  have bits := LambdaMarkers.lam_mem_pi_bits member
  exact Bool.eq_iff_iff.mpr (by simpa only [pwBit_eq_zero_iff] using bits)

/-- The checked marker relation, vacuous when either root is not a lambda. -/
theorem markers_of_fronts (m : EnvModel V env) (inputs : ∀ φ, RulesInputs V m φ)
    {cv : Ix.Kernel.ConstantVal md}
    {expected headerSortType rawL rawR checkedL checkedR : Ix.Kernel.Expr md} {FA FT FL FR : Nat}
    (headerClosed : cv.type.hasFvar = false) (headerBounded : cv.type.looseBVarsBounded 0 = true)
    (headerAnn : annotateCore .verified env FA 0 cv.type = .ok expected)
    (headerInfer : inferTypeCore .verified env FT 0 expected = .ok headerSortType)
    (left : ValueFrontRun .verified FL env cv rawL expected checkedL)
    (right : ValueFrontRun .verified FR env cv rawR expected checkedR) :
    ∀ p q, checkedL.lamPw = some p → checkedR.lamPw = some q → p = q := by
  intro p q hp hq
  obtain ⟨_, _, _, rfl, rfl⟩ := Ix.Kernel.Expr.lamPw_some_inv hp
  obtain ⟨_, _, _, rfl, rfl⟩ := Ix.Kernel.Expr.lamPw_some_inv hq
  exact lambda_markers_eq_of_fronts m inputs headerClosed headerBounded headerAnn headerInfer left right

end Ix.Cert.RuleInputValues
