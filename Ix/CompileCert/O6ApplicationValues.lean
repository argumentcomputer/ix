import Ix.CompileCert.O6Opened
import Ix.Cert.ApplicationFronts

/-! # Actual O6 values through an application and lambda argument

The enclosing checks supply the lambda argument's real annotation/full
inference. The O6 opening proof supplies its shapes and body conversion;
the actual application producer supplies the local fronts and typed header.
No shape, header, LocalFront or body equality is a caller premise here.

The whole roots have ordinary declaration guards, while the O6 body may
use its lambda's bvar zero. Further ambient binders and the full reader/
Translate composition remain separate; no final context restriction is
proposed. The source-recursion/image relationship is still N-PERM's task.
-/

namespace Ix.CompileCert.O6ApplicationValues

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Kernel.Model.Rules (Graded)
open Ix.Cert.ConversionValues Ix.Cert.ContextValues
open O6RecRead

universe w
variable {md : Mode} {env : Ix.Kernel.Env md} {V : Type w} [SetTheory V]

/-- Fixed-context application congruence, consumed below with the argument
comparison derived from actual O6 producers. No function value is assumed:
the identical function's two readings agree by functionality. -/
theorem app_argument {m : EnvModel V env} {φ : LevelParam → Nat} {d : Nat}
    {Δ : List AnnotTerm} {fn a b : Ix.Kernel.Expr md}
    (argument : EqAt m φ d Δ a b) : EqAt m φ d Δ (.app fn a) (.app fn b) := by
  intro frameL frameR la ra contextL contextR readL readR gradeL gradeR ρ sat
  obtain ⟨fa, aa, readFnL, readArgL, rfl⟩ := denoteMeta_app_inv readL
  obtain ⟨fb, ba, readFnR, readArgR, rfl⟩ := denoteMeta_app_inv readR
  have fnEq := Option.some.inj (readFnL.symm.trans readFnR)
  have argEq := argument frameL.app_arg frameR.app_arg aa ba contextL.app_arg contextR.app_arg
    readArgL readArgR (Model.Rules.Graded.app gradeL).2 (Model.Rules.Graded.app gradeR).2 ρ sat
  rw [interp_app, interp_app, fnEq, argEq]

variable {keyOf : Ix.Name → Key md} {levelOf : Ix.Level → Ix.Kernel.Level}

open Ix.Compile.Pass Ix.Compile.Pass.Opt in
/-- Public values of the ACTUAL whole applications. All local fronts,
header facts, lambda shapes, openers and body comparison are derived from
the real enclosing runs and actual O6/image/read evidence. Both whole full
runs are ordinary source-form/target checks in the same prefix env, not
invented local checks. No global marker equation or whole syntactic DefEq
is needed for this semantic application composition. -/
theorem o6_lambda_argument_values (env : Ix.Kernel.Env md)
    {opt : OptEnv} {o : Occ} {output : Ix.Expr} {r : Ix.Name} {block : OptBlock} {s : RecShape}
    {inp : ViewInput} {all : Array Ix.Name} {view : BlockView} {rv : Ix.RecursorVal}
    {img : Ix.Compile.Image.Image}
    (pass : O6.apply opt o = some output) (kind : classify o.head = some (.kRec, r))
    (blockLookup : opt.blockOf o.head = some block) (shapeLookup : block.shapes.get? r = some s)
    (built : buildView inp all = .ok view) (source : inp.const? r = some (.recInfo rv))
    (generated : view.image inp r = .ok img)
    (recognized : readShape r img.levelParams rv.numParams rv.numMotives rv.numMinors rv.numIndices
      img.value (ImageShape.viewRecInfo view) = some s)
    (universeArity : o.us.size = img.levelParams.size)
    {baseReader outReader : Ix.Kernel.Reader.MemberReader md} {baseWire outWire : Ixon.Expr}
    {baseK outputK : Ix.Kernel.Expr md}
    (baseRead : baseReader.read baseWire = .ok baseK) (outRead : outReader.read outWire = .ok outputK)
    (baseRelated : Rel (keyOf := keyOf) (levelOf := levelOf)
      (Ix.Compile.Canon.mkAppN (Ix.Compile.Canon.substLevels img.levelParams o.us img.value) o.args) baseK)
    (outRelated : Rel (keyOf := keyOf) (levelOf := levelOf) output outputK)
    {rawFn rawDom checkedL checkedR typeL typeR : Ix.Kernel.Expr md}
    {rawMeta : BinderMeta} {FAL FAR FIL FIR : Nat}
    (closedL : (Ix.Kernel.Expr.app rawFn (.lam rawDom baseK rawMeta)).hasFvar = false)
    (boundedL : (Ix.Kernel.Expr.app rawFn (.lam rawDom baseK rawMeta)).looseBVarsBounded 0 = true)
    (closedR : (Ix.Kernel.Expr.app rawFn (.lam rawDom outputK rawMeta)).hasFvar = false)
    (boundedR : (Ix.Kernel.Expr.app rawFn (.lam rawDom outputK rawMeta)).looseBVarsBounded 0 = true)
    (annL : annotateCore .verified env FAL 0 (.app rawFn (.lam rawDom baseK rawMeta)) = .ok checkedL)
    (annR : annotateCore .verified env FAR 0 (.app rawFn (.lam rawDom outputK rawMeta)) = .ok checkedR)
    (inferL : inferTypeCore .verified env FIL 0 checkedL = .ok typeL)
    (inferR : inferTypeCore .verified env FIR 0 checkedR = .ok typeR) :
    ∀ (V : Type w) [SetTheory V] (M : Cached.StrongModel V env)
      (φ : LevelParam → Nat) (ρ : BVarIdx → V),
      ∃ value, Denotes M.model.cval env φ ρ checkedL value ∧
        Denotes M.model.cval env φ ρ checkedR value := by
  have rawFrameL := frame_of_syntax closedL boundedL
  have rawFrameR := frame_of_syntax closedR boundedR
  have checkedFrameL := annotation_frame annL closedL boundedL
  have checkedFrameR := annotation_frame annR closedR boundedR
  cases FAL with
  | zero => rw [annotateCore_zero] at annL; exact nomatch annL
  | succ fal =>
  cases FAR with
  | zero => rw [annotateCore_zero] at annR; exact nomatch annR
  | succ far =>
  cases FIL with
  | zero => rw [inferTypeCore_zero] at inferL; exact nomatch inferL
  | succ fil =>
  obtain ⟨fnL, argL, fnAnnL, argAnnL, appShapeL⟩ := annotateCore_app_inv annL
  obtain ⟨fnR, argR, fnAnnR, argAnnR, appShapeR⟩ := annotateCore_app_inv annR
  have fnEq := O6Annotation.annotation_unique fnAnnL fnAnnR
  subst fnR
  have appInferL := inferL
  rw [appShapeL] at appInferL
  obtain ⟨_, _, _, _, _, _, _, _, argInferL, _⟩ := inferTypeCore_app_inv appInferL
  obtain ⟨domA, leftOpen, rightOpen, _, pwL, pwR, _, _, _, _, _, _, _, _,
      _, rightAnn, _, _, argShapeL, argShapeR, domainFrame, _, leftReopen, _, _, bodyEq⟩ :=
    O6Opened.o6_rec_under_lam_opened_red env pass kind blockLookup shapeLookup
      built source generated recognized universeArity baseRead outRead baseRelated outRelated
      (frame_not_hasFvar rawFrameL.app_arg) rawFrameL.app_arg.2.1 argAnnL argAnnR argInferL
  have outNo := frame_not_hasFvar rawFrameR.app_arg
  have outBound := rawFrameR.app_arg.2.1
  simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at outNo
  simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at outBound
  have rightReopen := O6Opened.annotation_reopen outNo.2 outBound.2 domainFrame rightAnn
  have openedConversion : Ix.Kernel.Rules.DefEq env 1
      ((leftOpen.abstract1 0).instantiate1 (.fvar 0 domA))
      ((rightOpen.abstract1 0).instantiate1 (.fvar 0 domA)) := by
    rw [leftReopen, rightReopen]
    exact bodyEq
  have wholeShapeL : checkedL = .app fnL (.lam domA (leftOpen.abstract1 0) {rawMeta with pw := pwL}) := by
    rw [appShapeL, argShapeL]
  have wholeShapeR : checkedR = .app fnL (.lam domA (rightOpen.abstract1 0) {rawMeta with pw := pwR}) := by
    rw [appShapeR, argShapeR]
  intro V inst M φ ρ
  have bodyIH : ∀ da, denoteMeta M.internal.base2.acval env φ 0 domA = some da →
      EqAt M.internal.base2 φ 1 [da]
        ((leftOpen.abstract1 0).instantiate1 (.fvar 0 domA))
        ((rightOpen.abstract1 0).instantiate1 (.fvar 0 domA)) := by
    intro da _ fL fR la ra cL cR rL rR gL gR σ sat
    exact Model.Rules.defeq_sound (Model.Rules.RulesInputs.ofSem M.internal φ)
      openedConversion fL fR cL cR rL rR gL gR σ sat
  obtain ⟨_, _, _, _, _, _, argumentEq⟩ := Ix.Cert.ApplicationFronts.paired_app_lambda_arguments M φ
    rawFrameL rawFrameR (frame_context M φ rawFrameL) (frame_context M φ rawFrameR)
    (wholeShapeL ▸ annL) (wholeShapeR ▸ annR) (wholeShapeL ▸ inferL) (wholeShapeR ▸ inferR) bodyIH
  have wholeEq : EqAt M.internal.base2 φ 0 [] checkedL checkedR := by
    rw [wholeShapeL, wholeShapeR]
    exact app_argument argumentEq
  obtain ⟨la, readL, gradeL⟩ := infer_reading M φ checkedFrameL inferL
  obtain ⟨ra, readR, gradeR⟩ := infer_reading M φ checkedFrameR inferR
  have same := wholeEq checkedFrameL checkedFrameR la ra
    (frame_context M φ checkedFrameL) (frame_context M φ checkedFrameR)
    readL readR gradeL gradeR ρ (Sat_nil V ρ)
  refine ⟨interp V ρ la, reading_denotes M checkedFrameL readL gradeL ρ, ?_⟩
  rw [same]
  exact reading_denotes M checkedFrameR readR gradeR ρ

end Ix.CompileCert.O6ApplicationValues
