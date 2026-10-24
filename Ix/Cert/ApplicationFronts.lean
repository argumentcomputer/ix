import Ix.Cert.ContextValues

/-! # Real argument fronts from enclosing application checks

Full application inference already checks its argument against the actual
WHNF domain. With the same raw function, successful annotation/inference/
WHNF runs at different fuels agree by monotonicity. Both actual argument
fronts therefore have one expected domain, derived from enclosing successes.

The domain's semantic frame/context/read/grade comes from the function's
real inference and WHNF. No fresh domain annotation/inference, generic
typing-completeness theorem or per-node runtime check is invented. This is
an internal producer bridge; value comparison and the typed-header consumer
adaptation remain separate, as do the full O6 reader/Translate producers.
-/

namespace Ix.Cert.ApplicationFronts

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Kernel.Model.Rules (Frame Graded)
open ContextValues

universe w
variable {md : Mode} {V : Type w} [SetTheory V] {env : Ix.Kernel.Env md}

/-- Typed transport from actual function inference and WHNF supplies the
domain package. It does not assert an executable inference of that domain,
and its grading needs no witness that the context or domain is inhabited. -/
theorem function_domain (M : Cached.StrongModel V env) (φ : LevelParam → Nat)
    {d FI FW : Nat} {Δ : List AnnotTerm} {fn fnType dom cod : Ix.Kernel.Expr md}
    {mt : BinderMeta} (frame : Frame d fn) (context : CtxOk M.internal.base2 φ d Δ fn)
    (inferred : inferTypeCore .verified env FI d fn = .ok fnType)
    (reduced : whnf .verified env FW d fnType = .ok (.forallE dom cod mt)) :
    Frame d dom ∧ CtxOk M.internal.base2 φ d Δ dom ∧
      ∃ da, denoteMeta M.internal.base2.acval env φ d dom = some da ∧ Graded V Δ da := by
  obtain ⟨_, ta, _, typeRead, typeFrame, typeContext, _, typeGrade, _⟩ :=
    infer_package_at M φ frame context inferred
  obtain ⟨forallFrame, leaves, pa, forallRead, forallGrade, _⟩ :=
    Model.Rules.red_sound (Model.Rules.RulesInputs.ofSem M.internal φ)
      (Ix.Kernel.Rules.whnf_bridge reduced) typeFrame typeContext typeRead typeGrade
  have forallContext := typeContext.of_subset leaves
  obtain ⟨da, ba, domainRead, _, rfl⟩ := denoteMeta_forallE_inv forallRead
  exact ⟨forallFrame.forallE_ty, forallContext.forallE_ty, da, domainRead,
    (Model.Rules.Graded.pi forallGrade).1⟩

/-- BOTH LocalFronts and their common expected domain are conclusions of
the real enclosing calls. Full inference checks each argument, including
Prop; annotation alone would not supply those checks. Dependent result
types retain their distinct actual substitutions.

Raw Frame/CtxOk is the existing context-induction invariant. The shared raw
function is this argument-context case, not a final restriction on rewrites.
The output header is a semantic package derived by typed transport, not a
fabricated raw-header annotation/full-inference run. -/
theorem paired_app_argument_fronts (M : Cached.StrongModel V env) (φ : LevelParam → Nat)
    {d : Nat} {Δ : List AnnotTerm}
    {rawFn rawArgL rawArgR checkedL checkedR typeL typeR : Ix.Kernel.Expr md}
    {FAL FAR FIL FIR : Nat}
    (frameL : Frame d (.app rawFn rawArgL)) (frameR : Frame d (.app rawFn rawArgR))
    (contextL : CtxOk M.internal.base2 φ d Δ (.app rawFn rawArgL))
    (contextR : CtxOk M.internal.base2 φ d Δ (.app rawFn rawArgR))
    (annL : annotateCore .verified env FAL d (.app rawFn rawArgL) = .ok checkedL)
    (annR : annotateCore .verified env FAR d (.app rawFn rawArgR) = .ok checkedR)
    (inferL : inferTypeCore .verified env FIL d checkedL = .ok typeL)
    (inferR : inferTypeCore .verified env FIR d checkedR = .ok typeR) :
    ∃ (fnA argL argR fnType dom cod : Ix.Kernel.Expr md) (mt : BinderMeta),
      checkedL = .app fnA argL ∧ checkedR = .app fnA argR ∧
      typeL = cod.instantiate1 argL ∧ typeR = cod.instantiate1 argR ∧
      (∃ F, annotateCore .verified env F d rawFn = .ok fnA) ∧
      (∃ F, inferTypeCore .verified env F d fnA = .ok fnType) ∧
      (∃ F, whnf .verified env F d fnType = .ok (.forallE dom cod mt)) ∧
      Frame d rawArgL ∧ Frame d rawArgR ∧
      CtxOk M.internal.base2 φ d Δ rawArgL ∧ CtxOk M.internal.base2 φ d Δ rawArgR ∧
      LocalFront env d rawArgL dom argL ∧ LocalFront env d rawArgR dom argR ∧
      Frame d dom ∧ CtxOk M.internal.base2 φ d Δ dom ∧
      ∃ da, denoteMeta M.internal.base2.acval env φ d dom = some da ∧ Graded V Δ da := by
  cases FAL with
  | zero => rw [annotateCore_zero] at annL; exact nomatch annL
  | succ fal =>
  cases FAR with
  | zero => rw [annotateCore_zero] at annR; exact nomatch annR
  | succ far =>
  cases FIL with
  | zero => rw [inferTypeCore_zero] at inferL; exact nomatch inferL
  | succ fil =>
  cases FIR with
  | zero => rw [inferTypeCore_zero] at inferR; exact nomatch inferR
  | succ fir =>
  obtain ⟨fnL, argL, fnAnnL, argAnnL, shapeL⟩ := annotateCore_app_inv annL
  obtain ⟨fnR, argR, fnAnnR, argAnnR, shapeR⟩ := annotateCore_app_inv annR
  have fnEq : fnL = fnR := Except.ok.inj
    ((annotateCore_mono (Nat.le_max_left fal far) fnAnnL).symm.trans
      (annotateCore_mono (Nat.le_max_right fal far) fnAnnR))
  subst fnR
  rw [shapeL] at inferL
  rw [shapeR] at inferR
  obtain ⟨fnTypeL, domL, codL, mtL, fnInferL, fnWhnfL, resultL, argTypeL, argInferL, argCheckL⟩ :=
    inferTypeCore_app_inv inferL
  obtain ⟨fnTypeR, domR, codR, mtR, fnInferR, fnWhnfR, resultR, argTypeR, argInferR, argCheckR⟩ :=
    inferTypeCore_app_inv inferR
  have typeEq : fnTypeL = fnTypeR := Except.ok.inj
    ((inferTypeCore_mono (Nat.le_max_left fil fir) fnInferL).symm.trans
      (inferTypeCore_mono (Nat.le_max_right fil fir) fnInferR))
  subst fnTypeR
  have whnfEq := Except.ok.inj
    ((whnf_mono (Nat.le_max_left fil fir) fnWhnfL).symm.trans
      (whnf_mono (Nat.le_max_right fil fir) fnWhnfR))
  obtain ⟨domainEq, codomainEq, metaEq⟩ := Ix.Kernel.Expr.forallE.inj whnfEq
  subst domR
  subst codR
  subst mtR
  obtain ⟨checkedFrame, checkedContext⟩ := annotate_context M φ frameL contextL annL
  rw [shapeL] at checkedFrame checkedContext
  obtain ⟨domainFrame, domainContext, da, domainRead, domainGrade⟩ :=
    function_domain M φ checkedFrame.app_fn checkedContext.app_fn fnInferL fnWhnfL
  exact ⟨fnL, argL, argR, fnTypeL, domL, codL, mtL, shapeL, shapeR, resultL, resultR,
    ⟨fal, fnAnnL⟩, ⟨fil, fnInferL⟩, ⟨fil, fnWhnfL⟩,
    frameL.app_arg, frameR.app_arg, contextL.app_arg, contextR.app_arg,
    ⟨fal, fil, fil, argTypeL, argAnnL, argInferL, argCheckL⟩,
    ⟨far, fir, fir, argTypeR, argAnnR, argInferR, argCheckR⟩,
    domainFrame, domainContext, da, domainRead, domainGrade⟩

/-- Explicit producer-to-consumer connection for actual lambda arguments.
The caller supplies enclosing annotation/full inference, raw context
invariants and the body comparison IH. BOTH local fronts and ALL header
facts are derived by paired_app_argument_fronts; no domain inference or
unproved header package is an input. This returns the argument comparison,
leaving whole-application/O6 production composition separate. -/
theorem paired_app_lambda_arguments (M : Cached.StrongModel V env) (φ : LevelParam → Nat)
    {d : Nat} {Δ : List AnnotTerm}
    {rawFn rawArgL rawArgR fnL fnR dom bodyL bodyR typeL typeR : Ix.Kernel.Expr md}
    {mL mR : BinderMeta} {FAL FAR FIL FIR : Nat}
    (frameL : Frame d (.app rawFn rawArgL)) (frameR : Frame d (.app rawFn rawArgR))
    (contextL : CtxOk M.internal.base2 φ d Δ (.app rawFn rawArgL))
    (contextR : CtxOk M.internal.base2 φ d Δ (.app rawFn rawArgR))
    (annL : annotateCore .verified env FAL d (.app rawFn rawArgL) =
      .ok (.app fnL (.lam dom bodyL mL)))
    (annR : annotateCore .verified env FAR d (.app rawFn rawArgR) =
      .ok (.app fnR (.lam dom bodyR mR)))
    (inferL : inferTypeCore .verified env FIL d (.app fnL (.lam dom bodyL mL)) = .ok typeL)
    (inferR : inferTypeCore .verified env FIR d (.app fnR (.lam dom bodyR mR)) = .ok typeR)
    (bodyIH : ∀ da, denoteMeta M.internal.base2.acval env φ d dom = some da →
      EqAt M.internal.base2 φ (d + 1) (da :: Δ)
        (bodyL.instantiate1 (.fvar d dom)) (bodyR.instantiate1 (.fvar d dom))) :
    ∃ la ra,
      denoteMeta M.internal.base2.acval env φ d (.lam dom bodyL mL) = some la ∧
      denoteMeta M.internal.base2.acval env φ d (.lam dom bodyR mR) = some ra ∧
      Graded V Δ la ∧ Graded V Δ ra ∧
      EqAt M.internal.base2 φ d Δ (.lam dom bodyL mL) (.lam dom bodyR mR) := by
  obtain ⟨fnA, argL, argR, _, expected, _, _, shapeL, shapeR, _, _, _, _, _,
      rawFrameL, rawFrameR, rawContextL, rawContextR, frontL, frontR,
      headerFrame, headerContext, ha, headerRead, headerGrade⟩ :=
    paired_app_argument_fronts M φ frameL frameR contextL contextR annL annR inferL inferR
  have argEqL := (Ix.Kernel.Expr.app.inj shapeL).2
  have argEqR := (Ix.Kernel.Expr.app.inj shapeR).2
  subst argL
  subst argR
  exact checked_lambda_congr_of_header M φ headerFrame headerContext headerRead headerGrade
    rawFrameL rawFrameR rawContextL rawContextR frontL frontR bodyIH

end Ix.Cert.ApplicationFronts
