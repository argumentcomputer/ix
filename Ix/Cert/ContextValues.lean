import Ix.Cert.LambdaMarkers

/-! # Internal semantic context composition from actual local checks

Frame/CtxOk and the body comparison are the context-induction invariant,
not new final compiler assumptions. Actual annotation/full-inference/type
checks supply checked scope, readings and grades. Comparisons at depth d
hold only under Sat of that context: no satisfying valuation is selected,
and no global literal marker equality is inferred from a possibly empty
context. Open terms remain internal readings, not public Denotes subjects.
-/

namespace Ix.Cert.ContextValues

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model Ix.Kernel.SetModel
open Ix.Kernel.SetTheory
open Ix.Kernel.Model.Rules (Frame Graded)

universe w
variable {md : Mode} {V : Type w} [SetTheory V] {env : Ix.Kernel.Env md}

/-- Existing DefEqSem currency at one fixed context, for the induction
hypothesis. The endpoint below also witnesses its actual reads and grades. -/
def EqAt (m : EnvModel V env) (φ : LevelParam → Nat) (d : Nat) (Δ : List AnnotTerm)
    (a b : Ix.Kernel.Expr md) : Prop :=
  Frame d a → Frame d b → ∀ aa ba,
    CtxOk m φ d Δ a → CtxOk m φ d Δ b →
    denoteMeta m.acval env φ d a = some aa → denoteMeta m.acval env φ d b = some ba →
    Graded V Δ aa → Graded V Δ ba →
    ∀ ρ : BVarIdx → V, Sat V Δ ρ → interp V ρ aa = interp V ρ ba

/-- Only actual local runs, retaining their individual fuels. This is a
proof package, not a new runtime checker or an assertion that root checks
automatically provide a common expected-type check at every nested node. -/
def LocalFront (env : Ix.Kernel.Env md) (d : Nat) (raw expected checked : Ix.Kernel.Expr md) : Prop :=
  ∃ FA FI FC inferred,
    annotateCore .verified env FA d raw = .ok checked ∧
    inferTypeCore .verified env FI d checked = .ok inferred ∧
    isDefEqCore .verified env FC d inferred expected = .ok true

/-- Real annotation transports the raw context invariant through its proved
leaf subset, including the types carried by free-variable leaves. -/
theorem annotate_context (M : Cached.StrongModel V env) (φ : LevelParam → Nat)
    {d F : Nat} {Δ : List AnnotTerm} {raw checked : Ix.Kernel.Expr md}
    (frame : Frame d raw) (context : CtxOk M.internal.base2 φ d Δ raw)
    (run : annotateCore .verified env F d raw = .ok checked) :
    Frame d checked ∧ CtxOk M.internal.base2 φ d Δ checked := by
  have leaves := annotateCore_leaves_sub F raw run frame.1 frame.2.1
  exact ⟨⟨annotateCore_WScoped F raw run frame.1, annotateCore_looseBVars F raw run frame.2.1,
    fun l hl => frame.2.2 l (leaves l hl)⟩, context.of_subset leaves⟩

/-- The actual full run supplies both reads, grades and type membership.
Its leaf-subset conclusion supplies the inferred type's CtxOk. No Sat
witness is needed for the package; membership remains conditional on Sat. -/
theorem infer_package_at (M : Cached.StrongModel V env) (φ : LevelParam → Nat)
    {d F : Nat} {Δ : List AnnotTerm} {e type : Ix.Kernel.Expr md}
    (frame : Frame d e) (context : CtxOk M.internal.base2 φ d Δ e)
    (run : inferTypeCore .verified env F d e = .ok type) :
    ∃ ea ta,
      denoteMeta M.internal.base2.acval env φ d e = some ea ∧
      denoteMeta M.internal.base2.acval env φ d type = some ta ∧
      Frame d type ∧ CtxOk M.internal.base2 φ d Δ type ∧
      Graded V Δ ea ∧ Graded V Δ ta ∧
      ∀ ρ : BVarIdx → V, Sat V Δ ρ → interp V ρ ea ∈ˢ interp V ρ ta := by
  obtain ⟨ea, read⟩ := Model.acceptedReads_of M.internal.base2 φ run frame.1 frame.2.1 frame.2.2
  obtain ⟨typeFrame, leaves, ta, typeRead, grade, typeGrade, member⟩ :=
    Model.Rules.infer_sound (Model.Rules.RulesInputs.ofSem M.internal φ)
      (Ix.Kernel.Rules.inferTypeCore_bridge run) frame context read
  exact ⟨ea, ta, read, typeRead, typeFrame, context.of_subset leaves, grade, typeGrade, member⟩

/-- Common actual type checks fix the lambda bits ONLY at a valid context
valuation. In contrast to the closed helper, no PropWhen extensionality or
arbitrary empty-set valuation is used at an open context. -/
theorem lambda_bits_at (M : Cached.StrongModel V env) (φ : LevelParam → Nat)
    {d : Nat} {Δ : List AnnotTerm}
    {expected headerSortType domL bodyL domR bodyR leftType rightType : Ix.Kernel.Expr md}
    {mL mR : BinderMeta} {FH FL FR CL CR : Nat}
    (headerFrame : Frame d expected) (headerContext : CtxOk M.internal.base2 φ d Δ expected)
    (headerInfer : inferTypeCore .verified env FH d expected = .ok headerSortType)
    (leftFrame : Frame d (.lam domL bodyL mL)) (rightFrame : Frame d (.lam domR bodyR mR))
    (leftContext : CtxOk M.internal.base2 φ d Δ (.lam domL bodyL mL))
    (rightContext : CtxOk M.internal.base2 φ d Δ (.lam domR bodyR mR))
    (leftInfer : inferTypeCore .verified env FL d (.lam domL bodyL mL) = .ok leftType)
    (rightInfer : inferTypeCore .verified env FR d (.lam domR bodyR mR) = .ok rightType)
    (leftCheck : isDefEqCore .verified env CL d leftType expected = .ok true)
    (rightCheck : isDefEqCore .verified env CR d rightType expected = .ok true) :
    ∀ ρ : BVarIdx → V, Sat V Δ ρ → (pwBit φ mL.pw = 0 ↔ pwBit φ mR.pw = 0) := by
  obtain ⟨cod, rfl⟩ := Ix.Kernel.Rules.Infer.lam_shape
    (Ix.Kernel.Rules.inferTypeCore_bridge leftInfer)
  obtain ⟨ha, _, headerRead, _, _, _, headerGrade, _, _⟩ :=
    infer_package_at M φ headerFrame headerContext headerInfer
  obtain ⟨_, lta, _, leftTypeRead, leftTypeFrame, leftTypeContext, _, leftTypeGrade, _⟩ :=
    infer_package_at M φ leftFrame leftContext leftInfer
  obtain ⟨ra, rta, rightRead, rightTypeRead, rightTypeFrame, rightTypeContext, _, rightTypeGrade, rightMember⟩ :=
    infer_package_at M φ rightFrame rightContext rightInfer
  intro ρ sat
  have inputs := Model.Rules.RulesInputs.ofSem M.internal φ
  have leftEq := Model.Rules.defeq_sound inputs (Ix.Kernel.Rules.isDefEqCore_bridge leftCheck)
    leftTypeFrame headerFrame leftTypeContext headerContext
    leftTypeRead headerRead leftTypeGrade headerGrade ρ sat
  have rightEq := Model.Rules.defeq_sound inputs (Ix.Kernel.Rules.isDefEqCore_bridge rightCheck)
    rightTypeFrame headerFrame rightTypeContext headerContext
    rightTypeRead headerRead rightTypeGrade headerGrade ρ sat
  have member : interp V ρ ra ∈ˢ interp V ρ lta := by
    rw [leftEq, ← rightEq]
    exact rightMember ρ sat
  obtain ⟨_, _, _, _, rightShape⟩ := denoteMeta_lam_inv rightRead
  obtain ⟨_, _, _, _, leftShape⟩ := denoteMeta_forallE_inv leftTypeRead
  rw [rightShape, leftShape, interp_lam, interp_pi] at member
  exact LambdaMarkers.lam_mem_pi_bits member

/-- Reading functionality turns witnessed pointwise equality into the
fixed-context induction motive. No existence is inferred from that motive. -/
theorem eqAt_of_readings {m : EnvModel V env} {φ : LevelParam → Nat} {d : Nat}
    {Δ : List AnnotTerm} {a b : Ix.Kernel.Expr md} {aa ba : AnnotTerm}
    (leftRead : denoteMeta m.acval env φ d a = some aa)
    (rightRead : denoteMeta m.acval env φ d b = some ba)
    (agree : ∀ ρ : BVarIdx → V, Sat V Δ ρ → interp V ρ aa = interp V ρ ba) :
    EqAt m φ d Δ a b := by
  intro _ _ aa' ba' _ _ leftRead' rightRead' _ _ ρ sat
  have leftEq := Option.some.inj (leftRead.symm.trans leftRead')
  have rightEq := Option.some.inj (rightRead.symm.trans rightRead')
  rw [← leftEq, ← rightEq]
  exact agree ρ sat

/-- INTERNAL same-domain lambda context constructor. The raw Frame/CtxOk
and body EqAt are the proof induction invariant; the local fronts/header
are actual runs. Checked frames, contexts, reads and grades are derived.
The result is meaningful only at valid context valuations, and does not
assert a global marker equation, whole syntactic DefEq or public Denotes
of open terms. Local expected-type checks must still be produced by the
actual checker trace or a proved typed transport, not assumed from a root
front or invented as new runtime checks. -/
theorem checked_lambda_congr_at (M : Cached.StrongModel V env) (φ : LevelParam → Nat)
    {d : Nat} {Δ : List AnnotTerm}
    {rawHeader expected headerSortType rawL rawR dom bodyL bodyR : Ix.Kernel.Expr md}
    {mL mR : BinderMeta} {FA FT : Nat}
    (headerFrame : Frame d rawHeader) (headerContext : CtxOk M.internal.base2 φ d Δ rawHeader)
    (headerAnn : annotateCore .verified env FA d rawHeader = .ok expected)
    (headerInfer : inferTypeCore .verified env FT d expected = .ok headerSortType)
    (leftFrame : Frame d rawL) (rightFrame : Frame d rawR)
    (leftContext : CtxOk M.internal.base2 φ d Δ rawL)
    (rightContext : CtxOk M.internal.base2 φ d Δ rawR)
    (left : LocalFront env d rawL expected (.lam dom bodyL mL))
    (right : LocalFront env d rawR expected (.lam dom bodyR mR))
    (bodyIH : ∀ da, denoteMeta M.internal.base2.acval env φ d dom = some da →
      EqAt M.internal.base2 φ (d + 1) (da :: Δ)
        (bodyL.instantiate1 (.fvar d dom)) (bodyR.instantiate1 (.fvar d dom))) :
    ∃ la ra,
      denoteMeta M.internal.base2.acval env φ d (.lam dom bodyL mL) = some la ∧
      denoteMeta M.internal.base2.acval env φ d (.lam dom bodyR mR) = some ra ∧
      Graded V Δ la ∧ Graded V Δ ra ∧
      EqAt M.internal.base2 φ d Δ (.lam dom bodyL mL) (.lam dom bodyR mR) := by
  obtain ⟨FAL, FIL, FCL, leftType, leftAnn, leftInfer, leftCheck⟩ := left
  obtain ⟨FAR, FIR, FCR, rightType, rightAnn, rightInfer, rightCheck⟩ := right
  obtain ⟨checkedHeaderFrame, checkedHeaderContext⟩ :=
    annotate_context M φ headerFrame headerContext headerAnn
  obtain ⟨checkedLeftFrame, checkedLeftContext⟩ :=
    annotate_context M φ leftFrame leftContext leftAnn
  obtain ⟨checkedRightFrame, checkedRightContext⟩ :=
    annotate_context M φ rightFrame rightContext rightAnn
  obtain ⟨la, _, leftRead, _, _, _, leftGrade, _, _⟩ :=
    infer_package_at M φ checkedLeftFrame checkedLeftContext leftInfer
  obtain ⟨ra, _, rightRead, _, _, _, rightGrade, _, _⟩ :=
    infer_package_at M φ checkedRightFrame checkedRightContext rightInfer
  have bits := lambda_bits_at M φ checkedHeaderFrame checkedHeaderContext headerInfer
    checkedLeftFrame checkedRightFrame checkedLeftContext checkedRightContext
    leftInfer rightInfer leftCheck rightCheck
  have agree : ∀ ρ : BVarIdx → V, Sat V Δ ρ → interp V ρ la = interp V ρ ra := by
    obtain ⟨daL, baL, domainReadL, bodyReadL, rfl⟩ := denoteMeta_lam_inv leftRead
    obtain ⟨daR, baR, domainReadR, bodyReadR, rfl⟩ := denoteMeta_lam_inv rightRead
    have common := Option.some.inj (domainReadL.symm.trans domainReadR)
    subst daR
    obtain ⟨domainGrade, bodyGradeL⟩ := Model.Rules.Graded.lam leftGrade
    obtain ⟨_, bodyGradeR⟩ := Model.Rules.Graded.lam rightGrade
    intro ρ sat
    rw [interp_lam, interp_lam]
    apply lamR_zero_agree (bits ρ sat)
    intro x member
    exact bodyIH daL domainReadL
      (checkedLeftFrame.lam_open checkedLeftFrame.lam_ty)
      (checkedRightFrame.lam_open checkedLeftFrame.lam_ty) baL baR
      (CtxOk.openS checkedLeftContext.lam_ty checkedLeftContext.lam_body domainReadL domainGrade)
      (CtxOk.openS checkedRightContext.lam_ty checkedRightContext.lam_body domainReadL domainGrade)
      bodyReadL bodyReadR bodyGradeL bodyGradeR (cons x ρ) (Sat_cons V sat member)
  exact ⟨la, ra, leftRead, rightRead, leftGrade, rightGrade, eqAt_of_readings leftRead rightRead agree⟩

end Ix.Cert.ContextValues
