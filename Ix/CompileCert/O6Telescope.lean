import Ix.CompileCert.O6Opened
import Ix.Cert.ContextValues

/-! # Actual paired annotation and inference through a shared lambda telescope

The opening domains and their exact checking subcalls are produced before
the semantic model is supplied. Context extension records real domain
readings and grades; it never chooses a satisfying valuation.
-/

namespace Ix.CompileCert.O6Telescope

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Kernel.Model.Rules (Frame Graded)
open Ix.Cert.ConversionValues Ix.Cert.ContextValues

universe w
variable {md : Mode} {env : Ix.Kernel.Env md}

/-- Proof-only raw syntax, with the outermost binder first. -/
def wrapLams (bs : List (Ix.Kernel.Expr md × BinderMeta)) (body : Ix.Kernel.Expr md) :=
  bs.foldr (fun (ty, mb) b => Ix.Kernel.Expr.lam ty b mb) body

@[simp] theorem wrapLams_nil (body : Ix.Kernel.Expr md) : wrapLams [] body = body := rfl

@[simp] theorem wrapLams_cons (ty body : Ix.Kernel.Expr md) (mb : BinderMeta) (bs) :
    wrapLams ((ty, mb) :: bs) body = .lam ty (wrapLams bs body) mb := rfl

/-- The actual annotated domains determine the innermost-first replacement list. -/
def openers (d : Nat) (As : List (Ix.Kernel.Expr md)) : List (Ix.Kernel.Expr md) :=
  (As.zipIdx.map (fun (A, i) => Ix.Kernel.Expr.fvar (d + i) A)).reverse

@[simp] theorem openers_length (d : Nat) (As : List (Ix.Kernel.Expr md)) :
    (openers d As).length = As.length := by simp [openers]

theorem openers_append_one (d : Nat) (As : List (Ix.Kernel.Expr md)) (A : Ix.Kernel.Expr md) :
    openers d (As ++ [A]) = .fvar (d + As.length) A :: openers d As := by
  simp [openers, List.zipIdx_append, List.reverse_append]

/-- Only the newly introduced index can identify the actual opener. Older
leaves, including hereditary domain leaves, are strictly below that index. -/
theorem annotation_reopen_at {d F : Nat} {rawBody domA opened : Ix.Kernel.Expr md}
    (scope : Ix.Kernel.Expr.WScoped d rawBody)
    (bounded : rawBody.looseBVarsBounded 1 = true) (domainFrame : Frame d domA)
    (run : annotateCore .verified env F (d + 1)
      (rawBody.instantiate1 (.fvar d domA)) = .ok opened) :
    (opened.abstract1 d).instantiate1 (.fvar d domA) = opened := by
  have openedScope := Ix.Kernel.Expr.WScoped.instantiate1 domainFrame.1 0 scope
  have openedBound := Ix.Kernel.Expr.looseBVarsBounded_instantiate1_gen
    (a := .fvar d domA) rfl bounded
  have leaves := annotateCore_leaves_sub F _ run openedScope openedBound
  have cond : Ix.Kernel.Expr.LeafCond d domA opened := by
    intro l hl index
    rcases Ix.Kernel.Expr.fvarLeaves_instantiate1 rawBody 0 (leaves l hl) with old | added
    · have lt := Ix.Kernel.Expr.fvarLeaves_lt_of_wscoped scope l old
      omega
    · simp only [Ix.Kernel.Expr.fvarLeaves, List.mem_cons] at added
      rcases added with rfl | inherited
      · rfl
      · have lt := Ix.Kernel.Expr.fvarLeaves_lt_of_wscoped domainFrame.1 l inherited
        omega
  exact abstract1_instantiate1 opened 0
    (Ix.Kernel.Expr.fvarConsistent_of_leafCond _ cond)
    (annotateCore_looseBVars F _ run openedBound)

theorem annotation_frame_at {d F : Nat} {raw checked : Ix.Kernel.Expr md}
    (frame : Frame d raw) (run : annotateCore .verified env F d raw = .ok checked) :
    Frame d checked := by
  have leaves := annotateCore_leaves_sub F raw run frame.1 frame.2.1
  exact ⟨annotateCore_WScoped F raw run frame.1, annotateCore_looseBVars F raw run frame.2.1,
    fun l hl => frame.2.2 l (leaves l hl)⟩

/-- Actual domain subcalls after the already produced prefix. Fuels decrease
once per real lambda arm, and the full inference is only the baseline's. -/
inductive DomainTraceFrom (env : Ix.Kernel.Env md) (d : Nat) :
    List (Ix.Kernel.Expr md) → List (Ix.Kernel.Expr md × BinderMeta) →
    List (Ix.Kernel.Expr md) → Nat → Nat → Nat → Prop where
  | nil {prior FAL FAR FIL} : DomainTraceFrom env d prior [] [] FAL FAR FIL
  | step {prior bs As rawTy rawMeta A AT u fal far fil}
      (frame : Frame (d + prior.length) A)
      (annL : annotateCore .verified env fal (d + prior.length)
        (rawTy.instantiateList (openers d prior)) = .ok A)
      (annR : annotateCore .verified env far (d + prior.length)
        (rawTy.instantiateList (openers d prior)) = .ok A)
      (inferL : inferTypeCore .verified env fil (d + prior.length) A = .ok AT)
      (sortL : whnf .verified env fil (d + prior.length) AT = .ok (.sort u))
      (rest : DomainTraceFrom env d (prior ++ [A]) bs As fal far fil) :
      DomainTraceFrom env d prior ((rawTy, rawMeta) :: bs) (A :: As)
        (fal + 1) (far + 1) (fil + 1)

def DomainTrace (env : Ix.Kernel.Env md) (d : Nat)
    (bs : List (Ix.Kernel.Expr md × BinderMeta)) (As : List (Ix.Kernel.Expr md))
    (FAL FAR FIL : Nat) : Prop := DomainTraceFrom env d [] bs As FAL FAR FIL

theorem DomainTraceFrom.length {d FAL FAR FIL : Nat} {prior As bs}
    (trace : DomainTraceFrom env d prior bs As FAL FAR FIL) : As.length = bs.length := by
  induction trace with
  | nil => rfl
  | step _ _ _ _ _ _ ih => simp only [List.length_cons, ih]

/-- Indexed projection of the actual calls, retaining their exact fuel and
the original raw domain opened by precisely its preceding domains. -/
theorem DomainTraceFrom.at {d FAL FAR FIL : Nat} {prior As bs}
    (trace : DomainTraceFrom env d prior bs As FAL FAR FIL)
    {i : Nat} {rawTy A : Ix.Kernel.Expr md} {rawMeta : BinderMeta}
    (rawAt : bs[i]? = some (rawTy, rawMeta)) (atA : As[i]? = some A) :
    Frame (d + prior.length + i) A ∧ ∃ fal far fil AT u,
      FAL = fal + i + 1 ∧ FAR = far + i + 1 ∧ FIL = fil + i + 1 ∧
      annotateCore .verified env fal (d + prior.length + i)
        (rawTy.instantiateList (openers d (prior ++ As.take i))) = .ok A ∧
      annotateCore .verified env far (d + prior.length + i)
        (rawTy.instantiateList (openers d (prior ++ As.take i))) = .ok A ∧
      inferTypeCore .verified env fil (d + prior.length + i) A = .ok AT ∧
      whnf .verified env fil (d + prior.length + i) AT = .ok (.sort u) := by
  induction trace generalizing i with
  | nil => cases rawAt
  | @step prior bs As ty mb B BT u fal far fil frame annL annR inferL sortL rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at rawAt atA
      obtain ⟨rfl, rfl⟩ := rawAt
      subst A
      simpa only [Nat.add_zero, List.take_zero, List.append_nil] using
        And.intro frame ⟨fal, far, fil, BT, u, rfl, rfl, rfl, annL, annR, inferL, sortL⟩
    | succ i =>
      obtain ⟨fr, fL, fR, fI, T, v, eL, eR, eI, aL, aR, iL, sL⟩ := ih rawAt atA
      have depth : d + (prior ++ [B]).length + i = d + prior.length + (i + 1) := by simp; omega
      refine ⟨depth ▸ fr, fL, fR, fI, T, v, by omega, by omega, by omega, ?_⟩
      simpa only [depth, List.take_succ_cons, List.append_assoc, List.singleton_append] using
        And.intro aL (And.intro aR (And.intro iL sL))

/-- Real semantic extensions for any supplied model, without a Sat witness. -/
inductive ContextTrace {V : Type w} [SetTheory V] (m : EnvModel V env) (φ : LevelParam → Nat) :
    Nat → List AnnotTerm → List (Ix.Kernel.Expr md) → List AnnotTerm → Prop where
  | nil {d Δ} : ContextTrace m φ d Δ [] Δ
  | step {d Δ A As Δ' da}
      (read : denoteMeta m.acval env φ d A = some da) (frame : Frame d A)
      (context : CtxOk m φ d Δ A) (grade : Graded V Δ da)
      (rest : ContextTrace m φ (d + 1) (da :: Δ) As Δ') :
      ContextTrace m φ d Δ (A :: As) Δ'

theorem ContextTrace.length {V : Type w} [SetTheory V] {m : EnvModel V env}
    {φ : LevelParam → Nat} {d Δ As Δ'} (trace : ContextTrace m φ d Δ As Δ') :
    Δ'.length = Δ.length + As.length := by
  induction trace with
  | nil => simp
  | step _ _ _ _ _ ih => simp only [List.length_cons] at ih ⊢; omega

/-- Invert the actual paired lambda calls. The accumulator contains only
domains already produced by those calls; instantiateList_cons identifies
each next real opening with the cumulative bulk opening. -/
theorem paired_telescope_from (d : Nat) (bs : List (Ix.Kernel.Expr md × BinderMeta))
    {prior : List (Ix.Kernel.Expr md)} {base output wholeBaseA wholeOutA wholeType : Ix.Kernel.Expr md}
    {FAL FAR FIL : Nat}
    (frame : Frame (d + prior.length) ((wrapLams bs base).instantiateList (openers d prior)))
    (annL : annotateCore .verified env FAL (d + prior.length)
      ((wrapLams bs base).instantiateList (openers d prior)) = .ok wholeBaseA)
    (annR : annotateCore .verified env FAR (d + prior.length)
      ((wrapLams bs output).instantiateList (openers d prior)) = .ok wholeOutA)
    (inferL : inferTypeCore .verified env FIL (d + prior.length) wholeBaseA = .ok wholeType) :
    ∃ (As : List (Ix.Kernel.Expr md)) (leftOpen rightOpen innerType : Ix.Kernel.Expr md)
      (fal far fil : Nat),
      DomainTraceFrom env d prior bs As FAL FAR FIL ∧
      FAL = fal + bs.length ∧ FAR = far + bs.length ∧ FIL = fil + bs.length ∧
      annotateCore .verified env fal (d + (prior ++ As).length)
        (base.instantiateList (openers d (prior ++ As))) = .ok leftOpen ∧
      annotateCore .verified env far (d + (prior ++ As).length)
        (output.instantiateList (openers d (prior ++ As))) = .ok rightOpen ∧
      inferTypeCore .verified env fil (d + (prior ++ As).length) leftOpen = .ok innerType ∧
      Frame (d + (prior ++ As).length) (base.instantiateList (openers d (prior ++ As))) ∧
      Frame (d + (prior ++ As).length) leftOpen ∧
      ∀ (V : Type w) [SetTheory V] (M : Cached.StrongModel V env) (φ : LevelParam → Nat)
        (Δ : List AnnotTerm),
        CtxOk M.internal.base2 φ (d + prior.length) Δ
          ((wrapLams bs base).instantiateList (openers d prior)) →
        ∃ Δ', ContextTrace M.internal.base2 φ (d + prior.length) Δ As Δ' ∧
          CtxOk M.internal.base2 φ (d + (prior ++ As).length) Δ'
            (base.instantiateList (openers d (prior ++ As))) ∧
          CtxOk M.internal.base2 φ (d + (prior ++ As).length) Δ' leftOpen := by
  induction bs generalizing prior wholeBaseA wholeOutA wholeType FAL FAR FIL with
  | nil =>
    simp only [wrapLams_nil] at frame annL annR
    refine ⟨[], wholeBaseA, wholeOutA, wholeType, FAL, FAR, FIL, .nil,
      rfl, rfl, rfl, ?_⟩
    simp only [List.append_nil]
    refine ⟨annL, annR, inferL, frame, annotation_frame_at frame annL, ?_⟩
    intro V _ M φ Δ context
    exact ⟨Δ, .nil, context, (annotate_context M φ frame context annL).2⟩
  | cons binder bs ih =>
    obtain ⟨rawTy, rawMeta⟩ := binder
    simp only [wrapLams_cons, Ix.Kernel.Expr.instantiateList] at frame annL annR
    cases FAL with
    | zero => rw [annotateCore_zero] at annL; exact nomatch annL
    | succ fAL =>
    cases FAR with
    | zero => rw [annotateCore_zero] at annR; exact nomatch annR
    | succ fAR =>
    cases FIL with
    | zero => rw [inferTypeCore_zero] at inferL; exact nomatch inferL
    | succ fIL =>
    obtain ⟨A, left, pwL, domainL, bodyL, shapeL⟩ := annotateCore_lam_inv annL
    obtain ⟨AR, right, pwR, domainR, bodyR, shapeR⟩ := annotateCore_lam_inv annR
    have common := O6Annotation.annotation_unique domainL domainR
    subst AR
    have domainFrame := annotation_frame_at frame.lam_ty domainL
    have rawScope := frame.1
    have rawBound := frame.2.1
    simp only [Ix.Kernel.Expr.WScoped] at rawScope
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at rawBound
    have reopen := annotation_reopen_at rawScope.2 rawBound.2 domainFrame bodyL
    rw [shapeL] at inferL
    obtain ⟨AT, u, inner, domainInfer, domainSort, bodyInfer, _, _, _⟩ := inferTypeCore_lam_inv inferL
    rw [reopen] at bodyInfer
    have depth : d + (prior ++ [A]).length = d + prior.length + 1 := by simp [Nat.add_assoc]
    have nextFrame : Frame (d + (prior ++ [A]).length)
        ((wrapLams bs base).instantiateList (openers d (prior ++ [A]))) := by
      simpa only [depth, openers_append_one, Ix.Kernel.Expr.instantiateList_cons] using
        frame.lam_open domainFrame
    have nextL : annotateCore .verified env fAL (d + (prior ++ [A]).length)
        ((wrapLams bs base).instantiateList (openers d (prior ++ [A]))) = .ok left := by
      simpa only [depth, openers_append_one, Ix.Kernel.Expr.instantiateList_cons] using bodyL
    have nextR : annotateCore .verified env fAR (d + (prior ++ [A]).length)
        ((wrapLams bs output).instantiateList (openers d (prior ++ [A]))) = .ok right := by
      simpa only [depth, openers_append_one, Ix.Kernel.Expr.instantiateList_cons] using bodyR
    obtain ⟨As, l, r, T, fl, fr, fi, trace, eL, eR, eI, aL, aR, iL, rawFr, checkedFr, contexts⟩ :=
      ih nextFrame nextL nextR (depth.symm ▸ bodyInfer)
    have appendEq : (prior ++ [A]) ++ As = prior ++ A :: As := by simp only [List.append_assoc, List.singleton_append]
    refine ⟨A :: As, l, r, T, fl, fr, fi,
      .step domainFrame domainL domainR domainInfer domainSort trace,
      by simp only [List.length_cons]; omega,
      by simp only [List.length_cons]; omega,
      by simp only [List.length_cons]; omega,
      appendEq ▸ aL, appendEq ▸ aR, appendEq ▸ iL, appendEq ▸ rawFr, appendEq ▸ checkedFr, ?_⟩
    intro V _ M φ Δ context
    simp only [wrapLams_cons, Ix.Kernel.Expr.instantiateList] at context
    have domainCtx := (annotate_context M φ frame.lam_ty context.lam_ty domainL).2
    obtain ⟨da, _, domainRead, _, _, _, domainGrade, _, _⟩ :=
      infer_package_at M φ domainFrame domainCtx domainInfer
    have openedCtx := CtxOk.openS domainCtx context.lam_body domainRead domainGrade
    obtain ⟨Δ', contextTrace, rawCtx, checkedCtx⟩ := contexts V M φ (da :: Δ)
      (by simpa only [depth, openers_append_one, Ix.Kernel.Expr.instantiateList_cons] using openedCtx)
    exact ⟨Δ', .step domainRead domainFrame domainCtx domainGrade (depth ▸ contextTrace),
      appendEq ▸ rawCtx, appendEq ▸ checkedCtx⟩

theorem DomainTrace.length {d FAL FAR FIL : Nat} {bs As}
    (trace : DomainTrace env d bs As FAL FAR FIL) : As.length = bs.length :=
  DomainTraceFrom.length trace

theorem DomainTrace.at {d FAL FAR FIL : Nat} {bs As}
    (trace : DomainTrace env d bs As FAL FAR FIL)
    {i : Nat} {rawTy A : Ix.Kernel.Expr md} {rawMeta : BinderMeta}
    (rawAt : bs[i]? = some (rawTy, rawMeta)) (atA : As[i]? = some A) :
    Frame (d + i) A ∧ ∃ fal far fil AT u,
      FAL = fal + i + 1 ∧ FAR = far + i + 1 ∧ FIL = fil + i + 1 ∧
      annotateCore .verified env fal (d + i)
        (rawTy.instantiateList (openers d (As.take i))) = .ok A ∧
      annotateCore .verified env far (d + i)
        (rawTy.instantiateList (openers d (As.take i))) = .ok A ∧
      inferTypeCore .verified env fil (d + i) A = .ok AT ∧
      whnf .verified env fil (d + i) AT = .ok (.sort u) := by
  simpa only [List.length_nil, Nat.add_zero, List.nil_append] using
    DomainTraceFrom.at trace rawAt atA

/-- Ordinary whole-root guards and actual whole checks produce the common
typed telescope and bulk-opened leaf checks before quantifying over models.
The semantic output then extends the empty context for each supplied model. -/
theorem paired_telescope {bs : List (Ix.Kernel.Expr md × BinderMeta)}
    {base output wholeBaseA wholeOutA wholeType : Ix.Kernel.Expr md} {FAL FAR FIL : Nat}
    (noFvars : (wrapLams bs base).hasFvar = false)
    (bounded : (wrapLams bs base).looseBVarsBounded 0 = true)
    (annL : annotateCore .verified env FAL 0 (wrapLams bs base) = .ok wholeBaseA)
    (annR : annotateCore .verified env FAR 0 (wrapLams bs output) = .ok wholeOutA)
    (inferL : inferTypeCore .verified env FIL 0 wholeBaseA = .ok wholeType) :
    ∃ (As : List (Ix.Kernel.Expr md)) (leftOpen rightOpen innerType : Ix.Kernel.Expr md)
      (fal far fil : Nat),
      DomainTrace env 0 bs As FAL FAR FIL ∧
      FAL = fal + bs.length ∧ FAR = far + bs.length ∧ FIL = fil + bs.length ∧
      annotateCore .verified env fal bs.length
        (base.instantiateList (openers 0 As)) = .ok leftOpen ∧
      annotateCore .verified env far bs.length
        (output.instantiateList (openers 0 As)) = .ok rightOpen ∧
      inferTypeCore .verified env fil bs.length leftOpen = .ok innerType ∧
      Frame bs.length (base.instantiateList (openers 0 As)) ∧ Frame bs.length leftOpen ∧
      ∀ (V : Type w) [SetTheory V] (M : Cached.StrongModel V env) (φ : LevelParam → Nat),
        ∃ Δ, ContextTrace M.internal.base2 φ 0 [] As Δ ∧ Δ.length = bs.length ∧
          CtxOk M.internal.base2 φ bs.length Δ (base.instantiateList (openers 0 As)) ∧
          CtxOk M.internal.base2 φ bs.length Δ leftOpen := by
  have rawFrame := frame_of_syntax noFvars bounded
  have empty (e : Ix.Kernel.Expr md) : e.instantiateList (openers 0 []) = e := by
    simp only [openers, List.zipIdx_nil, List.map_nil, List.reverse_nil, Ix.Kernel.Expr.instantiateList_nil]
  obtain ⟨As, left, right, inner, fal, far, fil, trace, eL, eR, eI, aL, aR, iL, rawFr, checkedFr, contexts⟩ :=
    paired_telescope_from 0 bs (prior := []) (base := base) (output := output)
      (by simpa only [List.length_nil, Nat.add_zero, empty] using rawFrame)
      (by simpa only [List.length_nil, Nat.add_zero, empty] using annL)
      (by simpa only [List.length_nil, Nat.add_zero, empty] using annR) inferL
  have len := trace.length
  simp only [List.nil_append, Nat.zero_add, len] at aL aR iL rawFr checkedFr contexts
  refine ⟨As, left, right, inner, fal, far, fil, trace, eL, eR, eI, aL, aR, iL, rawFr, checkedFr, ?_⟩
  intro V _ M φ
  obtain ⟨Δ, ct, rc, cc⟩ := contexts V M φ []
    (by simpa only [List.length_nil, empty] using frame_context M φ rawFrame)
  exact ⟨Δ, ct, by simpa only [List.length_nil, Nat.zero_add, len] using ct.length, rc, cc⟩

end Ix.CompileCert.O6Telescope
