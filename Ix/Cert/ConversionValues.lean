import Ix.Cert.ValueRows
import IxC.Kernel.Model.Capstone
import IxC.Kernel.Model.Rules.Sound
import IxC.Kernel.Verify.Rules.Bridge
import IxC.Kernel.Semantics.DeclRun
import IxC.Kernel.Semantics.Bridge.DeclRun

/-! # Checked conversion gives public value equality

The subjects here are the exact kernel expressions of successful full-grade
inference runs in one environment. Their readings and grading are derived
from those runs at the same strong model; they are not caller-supplied
semantic assumptions. The declaration-level Frame excludes free variables,
and successful inference supplies readability, so the public denotations
are of these subjects themselves, not merely of a different closure.

The ValueFrontRun wrapper retains the checker's actual annotation relation
from raw input values to those subjects. It does not assign a public
denotation to a raw let or free variable, or identify compiler source bytes
with an unrelated inferred expression. Per-pass proofs still must construct
the DefEq derivation and connect the actual source/target records to these
runs. No final CompileCorrect premise or production behavior is changed.
-/

namespace Ix.Cert.ConversionValues

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Kernel.Model.Rules (Frame Graded)

universe w
variable {md : Mode} {V : Type w} [SetTheory V] {env : Env md}

theorem frame_not_hasFvar {e : Ix.Kernel.Expr md} (h : Frame 0 e) : e.hasFvar = false :=
  Ix.Kernel.Expr.not_hasFvar_of_fvarsBelow_zero h.1.fvarsBelow

theorem frame_of_syntax {e : Ix.Kernel.Expr md}
    (closed : e.hasFvar = false) (bounded : e.looseBVarsBounded 0 = true) : Frame 0 e := by
  refine ⟨Ix.Kernel.Expr.WScoped.of_not_hasFvar closed, bounded, ?_⟩
  intro l hl
  rw [Ix.Kernel.Expr.fvarLeaves_eq_nil_of_not_hasFvar closed] at hl
  exact nomatch hl

/-- A declaration-level frame supplies the empty context at every level
assignment. No context or leaf-consistency hypothesis is added. -/
theorem frame_context (M : Cached.StrongModel V env) (φ : LevelParam → Nat)
    {e : Ix.Kernel.Expr md} (h : Frame 0 e) :
    Model.CtxOk M.internal.base2 φ 0 [] e :=
  Model.CtxOk.nil (Ix.Kernel.Expr.fvarLeaves_eq_nil_of_not_hasFvar (frame_not_hasFvar h))

/-- Full-grade successful inference provides both the subject's internal
reading and its grading in the same model and environment. -/
theorem infer_reading (M : Cached.StrongModel V env) (φ : LevelParam → Nat)
    {e type : Ix.Kernel.Expr md} {F : Nat} (frame : Frame 0 e)
    (inferred : inferTypeCore .verified env F 0 e = .ok type) :
    ∃ ea, denoteMeta M.internal.base2.acval env φ 0 e = some ea ∧ Graded V [] ea := by
  obtain ⟨ea, read⟩ := Model.acceptedReads_of M.internal.base2 φ inferred
    frame.1 frame.2.1 frame.2.2
  have inputs := Model.Rules.RulesInputs.ofSem M.internal φ
  have typed := Model.Rules.infer_sound inputs (Ix.Kernel.Rules.inferTypeCore_bridge inferred)
  obtain ⟨_, _, _, _, graded, _, _⟩ := typed frame (frame_context M φ frame) read
  exact ⟨ea, read, graded⟩

/-- A graded reading of a framed subject gives that very subject's public
denotation: the frame proves its depth-zero closure equals the subject. -/
theorem reading_denotes (M : Cached.StrongModel V env) {φ : LevelParam → Nat}
    {e : Ix.Kernel.Expr md} {ea : AnnotTerm} (frame : Frame 0 e)
    (read : denoteMeta M.internal.base2.acval env φ 0 e = some ea)
    (graded : Graded V [] ea) (ρ : BVarIdx → V) :
    Denotes M.model.cval env φ ρ e (interp V ρ ea) := by
  rw [Cached.StrongModel.model_cval]
  have h := Model.Denotes_of_denoteMeta M.internal.base2.cval_closedL 0 e read
    frame.1.fvarsBelow frame.2.1 ρ (graded ρ (Sat_nil V ρ))
  simpa only [Ix.Kernel.Expr.closeN_of_hasFvar _ 0 0 (frame_not_hasFvar frame)] using h

/-- Static DefEq plus both real inference successes gives a common public
value. DefEq is an internal proof leaf for the static pass theorem to supply,
not an assumption proposed for final compiler correctness. -/
theorem defeq_values (M : Cached.StrongModel V env)
    {a b ta tb : Ix.Kernel.Expr md} {Fa Fb : Nat}
    (frameA : Frame 0 a) (frameB : Frame 0 b)
    (inferA : inferTypeCore .verified env Fa 0 a = .ok ta)
    (inferB : inferTypeCore .verified env Fb 0 b = .ok tb)
    (conversion : Ix.Kernel.Rules.DefEq env 0 a b)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    ∃ v, Denotes M.model.cval env φ ρ a v ∧ Denotes M.model.cval env φ ρ b v := by
  obtain ⟨aa, readA, gradeA⟩ := infer_reading M φ frameA inferA
  obtain ⟨ba, readB, gradeB⟩ := infer_reading M φ frameB inferB
  have eq := Model.Rules.defeq_sound (Model.Rules.RulesInputs.ofSem M.internal φ)
    conversion frameA frameB (frame_context M φ frameA) (frame_context M φ frameB)
    readA readB gradeA gradeB ρ (Sat_nil V ρ)
  refine ⟨interp V ρ aa, reading_denotes M frameA readA gradeA ρ, ?_⟩
  rw [eq]
  exact reading_denotes M frameB readB gradeB ρ

/-- Any already identified endpoint values are the common value above. -/
theorem defeq_denotations_eq (M : Cached.StrongModel V env)
    {a b ta tb : Ix.Kernel.Expr md} {Fa Fb : Nat}
    (frameA : Frame 0 a) (frameB : Frame 0 b)
    (inferA : inferTypeCore .verified env Fa 0 a = .ok ta)
    (inferB : inferTypeCore .verified env Fb 0 b = .ok tb)
    (conversion : Ix.Kernel.Rules.DefEq env 0 a b)
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {va vb : V}
    (valueA : Denotes M.model.cval env φ ρ a va)
    (valueB : Denotes M.model.cval env φ ρ b vb) : va = vb := by
  obtain ⟨v, ha, hb⟩ := defeq_values M frameA frameB inferA inferB conversion φ ρ
  exact (Denotes_functional valueA ha).trans (Denotes_functional valueB hb).symm

/-- An existing verified conversion run is another supplier of the same
internal DefEq leaf. This does not replace static per-pass conversion proofs. -/
theorem checked_defeq_values (M : Cached.StrongModel V env)
    {a b ta tb : Ix.Kernel.Expr md} {Fa Fb Fc : Nat}
    (frameA : Frame 0 a) (frameB : Frame 0 b)
    (inferA : inferTypeCore .verified env Fa 0 a = .ok ta)
    (inferB : inferTypeCore .verified env Fb 0 b = .ok tb)
    (conversion : isDefEqCore .verified env Fc 0 a b = .ok true)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    ∃ v, Denotes M.model.cval env φ ρ a v ∧ Denotes M.model.cval env φ ρ b v :=
  defeq_values M frameA frameB inferA inferB
    (Ix.Kernel.Rules.isDefEqCore_bridge conversion) φ ρ

/-- Actual annotation, with the input's declaration guards, supplies the
output frame. This is a syntactic preservation result, not raw-term meaning. -/
theorem annotation_frame {raw checked : Ix.Kernel.Expr md} {F : Nat}
    (annotated : annotateCore .verified env F 0 raw = .ok checked)
    (closed : raw.hasFvar = false) (bounded : raw.looseBVarsBounded 0 = true) :
    Frame 0 checked :=
  let h := Semantics.annotate_syntax annotated closed bounded
  frame_of_syntax h.1 h.2

/-- The checker's own value-front relation contains the actual input guards
and annotation run, so its checked value needs no external frame premise. -/
theorem valueFront_frame {cv : Ix.Kernel.ConstantVal md} {raw type checked : Ix.Kernel.Expr md}
    {F : Nat} (front : ValueFrontRun .verified F env cv raw type checked) : Frame 0 checked :=
  annotation_frame front.2.2.1 front.2.1 front.1

/-- Success of the actual definition checker identifies its stored annotated
body and supplies that body's frame and full value-front trace. The trace's
inference environment is the original prefix env, not the extended result. -/
theorem definition_front {cv : Ix.Kernel.ConstantVal md} {raw : Ix.Kernel.Expr md}
    {hint : ReducibilityHint} {F : Nat} {ev : Evidences md} {out : Env md}
    (checked : checkDecl .verified (fueledOps .verified F) ev env (.defnDecl cv raw hint) = .ok out) :
    ∃ type value, ValueFrontRun .verified F env cv raw type value ∧ Frame 0 value ∧
      out = ⟨.defnInfo ⟨cv.name, cv.levelParams, type⟩ value hint :: env.consts⟩ := by
  obtain ⟨type, value, _, front, installed, _⟩ := Semantics.declDefnRun_of checked
  exact ⟨type, value, front, valueFront_frame front, installed⟩

/-- The exact annotated values of two successful value fronts have a common
public value when the pass proof supplies their conversion. Raw inputs remain
explicitly linked by the existing ValueFrontRun annotation fields; this says
nothing about denoting the raw values before annotation. Both runs and the
model are over the SAME target environment. -/
theorem valueFront_defeq_values (M : Cached.StrongModel V env)
    {cvA cvB : Ix.Kernel.ConstantVal md}
    {rawA rawB typeA typeB a b : Ix.Kernel.Expr md} {Fa Fb : Nat}
    (frontA : ValueFrontRun .verified Fa env cvA rawA typeA a)
    (frontB : ValueFrontRun .verified Fb env cvB rawB typeB b)
    (conversion : Ix.Kernel.Rules.DefEq env 0 a b)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    ∃ v, Denotes M.model.cval env φ ρ a v ∧ Denotes M.model.cval env φ ρ b v := by
  obtain ⟨_, inferA, _⟩ := frontA.2.2.2.2.2
  obtain ⟨_, inferB, _⟩ := frontB.2.2.2.2.2
  exact defeq_values M (valueFront_frame frontA) (valueFront_frame frontB)
    inferA inferB conversion φ ρ

end Ix.Cert.ConversionValues
