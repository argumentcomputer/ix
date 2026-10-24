import Ix.Cert.ConversionValues
import IxC.Kernel.Verify.InferIOLemmas

/-! # One checked beta step from actual annotation and inference

The subject is one closed, top-level lambda application in its actual
pre-insertion environment. Full application inference supplies the real
argument type and domain conversion. The certified beta rule therefore
applies even when the checked marker permits Prop; no raw `.never` licence
is used. Reduction soundness supplies the reduct's frame, reading and grade
at the same strong model, without assuming inference of the reduct.

The annotation trace retains the actual typed opener, body re-abstraction
and marker computation (or already-written marker). The resulting reduct
is not identified with annotation of a raw beta reduct. Relating it to the
actual O6 output, traversing a spine or reducing under binders remain open.
-/

namespace Ix.Cert.AnnotatedBeta

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Kernel.Model.Rules (Frame)
open Ix.Cert.ConversionValues

universe w
variable {md : Mode} {env : Env md}

/-- The certificate is extracted from full inference of this exact checked
application. The lambda's inferred forall and its WHNF have the SAME domain.
The returned io run is real, at the application's actual recursive fuel. -/
theorem inferred_beta_certificate
    {F : Nat} {dom body arg resultType : Ix.Kernel.Expr md} {mb : BinderMeta}
    (run : inferTypeCore .verified env F 0 (.app (.lam dom body mb) arg)
      = .ok resultType) :
    ∃ fuel argType, F = fuel + 1 ∧
      inferTypeCoreIO .verified env fuel 0 arg = .ok argType ∧
      isDefEqCore .verified env fuel 0 argType dom = .ok true ∧
      Ix.Kernel.Rules.Red env 0 (.app (.lam dom body mb) arg) (body.instantiate1 arg) := by
  cases F with
  | zero => rw [inferTypeCore_zero] at run; exact nomatch run
  | succ fuel =>
    obtain ⟨tf, dom', body', mb', headRun, headWhnf, _, argType, argRun, domainRun⟩ :=
      inferTypeCore_app_inv run
    obtain ⟨bt, rfl⟩ := Ix.Kernel.Rules.Infer.lam_shape
      (Ix.Kernel.Rules.inferTypeCore_bridge headRun)
    have domain := (Ix.Kernel.Expr.forallE.inj (whnf_forallE_eq headWhnf)).1
    rw [domain] at domainRun
    have ioRun := inferTypeCoreIO_of_full argRun
    exact ⟨fuel, argType, rfl, ioRun, domainRun,
      .beta (Ix.Kernel.Rules.inferTypeCoreIO_bridge ioRun)
        (Ix.Kernel.Rules.isDefEqCore_bridge domainRun)⟩

/-- The actual annotation subcalls of a closed lambda application. Its sole
opener is `.fvar 0 domA`, at depth one. A written marker is retained; otherwise
the production `annotPwLam` call computes it from the actual opened body. -/
def BetaTrace (env : Env md) (F : Nat)
    (rawTy rawBody : Ix.Kernel.Expr md) (rawMeta : BinderMeta)
    (rawArg domA openedA argA : Ix.Kernel.Expr md) (pw : PropWhen) : Prop :=
  ∃ fuel, F = fuel + 2 ∧
    annotateCore .verified env (fuel + 1) 0 rawArg = .ok argA ∧
    annotateCore .verified env fuel 0 rawTy = .ok domA ∧
    annotateCore .verified env fuel 1
      (rawBody.instantiate1 (.fvar 0 domA)) = .ok openedA ∧
    (if !pwWritten rawMeta.pw then
      annotPwLam (pureFns .verified env fuel) env 1 openedA
    else pure rawMeta.pw) = .ok pw

/-- Invert the real lambda annotation arm, retaining the marker run omitted
by the existing shape-only inversion. This is only the depth-zero arm. -/
theorem annotate_lam_trace
    {fuel : Nat} {rawTy rawBody checked : Ix.Kernel.Expr md} {rawMeta : BinderMeta}
    (run : annotateCore .verified env (fuel + 1) 0
      (.lam rawTy rawBody rawMeta) = .ok checked) :
    ∃ domA openedA pw,
      annotateCore .verified env fuel 0 rawTy = .ok domA ∧
      annotateCore .verified env fuel 1
        (rawBody.instantiate1 (.fvar 0 domA)) = .ok openedA ∧
      (if !pwWritten rawMeta.pw then
        annotPwLam (pureFns .verified env fuel) env 1 openedA
      else pure rawMeta.pw) = .ok pw ∧
      checked = .lam domA (openedA.abstract1 0) {rawMeta with pw} := by
  rw [annotateCore_succ] at run
  simp only [annotateBody, Bind.bind, Except.bind, annotate_def] at run
  cases domRun : annotateCore .verified env fuel 0 rawTy with
  | error err => rw [domRun] at run; exact nomatch run
  | ok domA =>
  rw [domRun] at run; dsimp only at run
  cases bodyRun : annotateCore .verified env fuel 1
      (rawBody.instantiate1 (.fvar 0 domA)) with
  | error err => rw [bodyRun] at run; exact nomatch run
  | ok openedA =>
  rw [bodyRun] at run; dsimp only at run
  by_cases gate : (!pwWritten rawMeta.pw) = true
  · rw [ite_eq_left gate] at run
    cases markerRun : annotPwLam (pureFns .verified env fuel) env 1 openedA with
    | error err => rw [markerRun] at run; exact nomatch run
    | ok pw =>
    rw [markerRun] at run
    simp only [pure, Except.pure, Except.ok.injEq] at run
    exact ⟨domA, openedA, pw, rfl, bodyRun,
      by simpa only [ite_eq_left gate] using markerRun, run.symm⟩
  · rw [ite_eq_right gate] at run
    simp only [pure, Except.pure, Except.ok.injEq] at run
    exact ⟨domA, openedA, rawMeta.pw, rfl, bodyRun,
      by simp only [ite_eq_right gate]; rfl, run.symm⟩

/-- The whole actual annotation run supplies one coherent trace and the
exact checked application. Application annotation itself checks no typing;
the separate full-inference run is essential for the certificate below. -/
theorem annotate_beta_trace
    {F : Nat} {rawTy rawBody rawArg checked : Ix.Kernel.Expr md} {rawMeta : BinderMeta}
    (run : annotateCore .verified env F 0
      (.app (.lam rawTy rawBody rawMeta) rawArg) = .ok checked) :
    ∃ domA openedA argA pw,
      BetaTrace env F rawTy rawBody rawMeta rawArg domA openedA argA pw ∧
      checked = .app (.lam domA (openedA.abstract1 0) {rawMeta with pw}) argA := by
  cases F with
  | zero => rw [annotateCore_zero] at run; exact nomatch run
  | succ fuel =>
    obtain ⟨headA, argA, headRun, argRun, out⟩ := annotateCore_app_inv run
    cases fuel with
    | zero => rw [annotateCore_zero] at headRun; exact nomatch headRun
    | succ fuel =>
      obtain ⟨domA, openedA, pw, domRun, bodyRun, markerRun, headOut⟩ :=
        annotate_lam_trace headRun
      exact ⟨domA, openedA, argA, pw,
        ⟨fuel, rfl, argRun, domRun, bodyRun, markerRun⟩, headOut ▸ out⟩

/-- Public equality for the certified beta step. Only the checked redex has
an inference premise: reduction soundness derives the reduct's frame, read
and grade in the SAME environment/model. No reduct-inference premise or
possibly-Prop marker gate is required. -/
theorem inferred_beta_values {V : Type w} [SetTheory V]
    (M : Cached.StrongModel V env)
    {F : Nat} {dom body arg resultType : Ix.Kernel.Expr md} {mb : BinderMeta}
    (frame : Frame 0 (.app (.lam dom body mb) arg))
    (run : inferTypeCore .verified env F 0 (.app (.lam dom body mb) arg)
      = .ok resultType)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    ∃ value, Denotes M.model.cval env φ ρ (.app (.lam dom body mb) arg) value ∧
      Denotes M.model.cval env φ ρ (body.instantiate1 arg) value := by
  obtain ⟨_, _, _, _, _, reduction⟩ := inferred_beta_certificate run
  obtain ⟨ea, read, grade⟩ := infer_reading M φ frame run
  obtain ⟨frameR, _, er, readR, gradeR, same⟩ :=
    Model.Rules.red_sound (Model.Rules.RulesInputs.ofSem M.internal φ)
      reduction frame (frame_context M φ frame) read grade
  refine ⟨interp V ρ ea, reading_denotes M frame read grade ρ, ?_⟩
  rw [same ρ (Sat_nil V ρ)]
  exact reading_denotes M frameR readR gradeR ρ

/-- One actual closed annotation/inference pair determines the checked
redex, its certificate and reduct before quantifying over strong models.
All runs, the typed opener and both public denotations use the exact original
environment; callers must retain that pre-insertion environment. The raw
input has no free variables, so the actual depth-one opener is fresh.

This does not equate the reduct with annotation of the raw substituted body
or the O6 output. Those separate annotation/substitution bridges remain due. -/
theorem annotated_beta_values
    {rawTy rawBody rawArg checked checkedType : Ix.Kernel.Expr md}
    {rawMeta : BinderMeta} {FA FI : Nat}
    (closed : (Ix.Kernel.Expr.app (.lam rawTy rawBody rawMeta) rawArg).hasFvar = false)
    (bounded : (Ix.Kernel.Expr.app (.lam rawTy rawBody rawMeta) rawArg).looseBVarsBounded 0 = true)
    (annotated : annotateCore .verified env FA 0
      (.app (.lam rawTy rawBody rawMeta) rawArg) = .ok checked)
    (inferred : inferTypeCore .verified env FI 0 checked = .ok checkedType) :
    ∃ (domA openedA argA : Ix.Kernel.Expr md) (pw : PropWhen),
      BetaTrace env FA rawTy rawBody rawMeta rawArg domA openedA argA pw ∧
      checked = .app (.lam domA (openedA.abstract1 0) {rawMeta with pw}) argA ∧
      Ix.Kernel.Rules.Red env 0 checked ((openedA.abstract1 0).instantiate1 argA) ∧
      Ix.Kernel.Rules.DefEq env 0 checked ((openedA.abstract1 0).instantiate1 argA) ∧
      ∀ (V : Type w) [SetTheory V] (M : Cached.StrongModel V env)
        (φ : LevelParam → Nat) (ρ : BVarIdx → V),
        ∃ value, Denotes M.model.cval env φ ρ checked value ∧
          Denotes M.model.cval env φ ρ ((openedA.abstract1 0).instantiate1 argA) value := by
  obtain ⟨domA, openedA, argA, pw, trace, shape⟩ := annotate_beta_trace annotated
  have frame := annotation_frame annotated closed bounded
  subst checked
  obtain ⟨_, _, _, _, _, reduction⟩ := inferred_beta_certificate inferred
  refine ⟨domA, openedA, argA, pw, trace, rfl, reduction,
    Ix.Kernel.Rules.DefEq.ofRed reduction, ?_⟩
  intro V inst M φ ρ
  exact inferred_beta_values M frame inferred φ ρ

end Ix.Cert.AnnotatedBeta
