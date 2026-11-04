import Ix.Cert.NoCtor
import IxC.Kernel.Verify.InferLemmas
import IxC.Kernel.Verify.Abstract

/-! # The constants of a checked term

IxC's checker looks up every constant of a term it accepts: inference looks up a constant node
and visits every subterm (an application's argument too), and annotation keeps every constant
node except a `let`'s type and value, which it infers before taking the reduct. So whatever
holds of the constants the checker finds, and of the constants an annotated term keeps, holds
of the input's constants.

* `ConstsAll P e`: every constant node of a kernel term (not a free variable's type, not a
  projection's structure) satisfies `P`.
* `inferTypeCore_constsAll`: a term whose inference succeeds has every constant node in the
  environment.
* `annotateCore_constsAll`: a term annotates to one whose constant nodes satisfy `P`, with every
  constant of the environment satisfying `P`, only if its own constant nodes satisfy `P`.
* `constantValRun_constsAll`, `constantValRun_noSelf`: a constant the checker's front door
  accepted has every constant node of its type in the environment before it, so not its own
  name.
* `ingress_constsAll`: the ingress maps a Lean term's constants to their keys, node for node. -/

namespace Ix.Cert.CheckedConsts

open Ix.Kernel

variable {md : Mode} {mode : CheckMode}

/-- **Every constant node of a term satisfies `P`**: its constants, not a free variable's type
and not a projection's structure. -/
def ConstsAll (P : Ix.Kernel.Key md → Prop) : Ix.Kernel.Expr md → Prop
  | .const n _ => P n
  | .app f a => ConstsAll P f ∧ ConstsAll P a
  | .lam ty b _ | .forallE ty b _ => ConstsAll P ty ∧ ConstsAll P b
  | .letE ty v b _ => ConstsAll P ty ∧ ConstsAll P v ∧ ConstsAll P b
  | .proj _ _ e => ConstsAll P e
  | _ => True

theorem constsAll_mono {P Q : Ix.Kernel.Key md → Prop} (h : ∀ k, P k → Q k) :
    ∀ {e : Ix.Kernel.Expr md}, ConstsAll P e → ConstsAll Q e
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .lit _, _ => trivial
  | .const n _, hp => h n hp
  | .app _ _, hp => ⟨constsAll_mono h hp.1, constsAll_mono h hp.2⟩
  | .lam _ _ _, hp => ⟨constsAll_mono h hp.1, constsAll_mono h hp.2⟩
  | .forallE _ _ _, hp => ⟨constsAll_mono h hp.1, constsAll_mono h hp.2⟩
  | .letE _ _ _ _, hp => ⟨constsAll_mono h hp.1, constsAll_mono h hp.2.1, constsAll_mono h hp.2.2⟩
  | .proj _ _ e, hp => constsAll_mono h (e := e) hp

/-- Instantiating a bound variable keeps the term's constant nodes. -/
theorem constsAll_of_instantiate1 {P : Ix.Kernel.Key md → Prop} {v : Ix.Kernel.Expr md} :
    ∀ {e : Ix.Kernel.Expr md} {d : Nat}, ConstsAll P (e.instantiate1 v d) → ConstsAll P e
  | .bvar _, _, _ | .fvar _ _, _, _ | .sort _, _, _ | .lit _, _, _ => trivial
  | .const _ _, _, h => h
  | .app _ _, _, h => ⟨constsAll_of_instantiate1 h.1, constsAll_of_instantiate1 h.2⟩
  | .lam _ _ _, _, h => ⟨constsAll_of_instantiate1 h.1, constsAll_of_instantiate1 h.2⟩
  | .forallE _ _ _, _, h => ⟨constsAll_of_instantiate1 h.1, constsAll_of_instantiate1 h.2⟩
  | .letE _ _ _ _, _, h =>
    ⟨constsAll_of_instantiate1 h.1, constsAll_of_instantiate1 h.2.1, constsAll_of_instantiate1 h.2.2⟩
  | .proj _ _ e, d, h => constsAll_of_instantiate1 (e := e) (d := d) h

/-- Abstracting a free variable keeps the term's constant nodes. -/
theorem constsAll_of_abstract1 {P : Ix.Kernel.Key md → Prop} {d : Nat} :
    ∀ {e : Ix.Kernel.Expr md} {k : Nat}, ConstsAll P (e.abstract1 d k) → ConstsAll P e
  | .bvar _, _, _ | .fvar _ _, _, _ | .sort _, _, _ | .lit _, _, _ => trivial
  | .const _ _, _, h => h
  | .app _ _, _, h => ⟨constsAll_of_abstract1 h.1, constsAll_of_abstract1 h.2⟩
  | .lam _ _ _, _, h => ⟨constsAll_of_abstract1 h.1, constsAll_of_abstract1 h.2⟩
  | .forallE _ _ _, _, h => ⟨constsAll_of_abstract1 h.1, constsAll_of_abstract1 h.2⟩
  | .letE _ _ _ _, _, h =>
    ⟨constsAll_of_abstract1 h.1, constsAll_of_abstract1 h.2.1, constsAll_of_abstract1 h.2.2⟩
  | .proj _ _ e, k, h => constsAll_of_abstract1 (e := e) (k := k) h

/-- A term whose constants resolve has every constant node in the environment. -/
theorem constsAll_of_constsResolve {env : Ix.Kernel.Env md} :
    ∀ {e : Ix.Kernel.Expr md}, e.constsResolve env = true → ConstsAll (fun k => (env.find? k).isSome = true) e
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .lit _, _ => trivial
  | .const _ _, h => h
  | .app _ _, h => by
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at h
    exact ⟨constsAll_of_constsResolve h.1, constsAll_of_constsResolve h.2⟩
  | .lam _ _ _, h => by
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at h
    exact ⟨constsAll_of_constsResolve h.1, constsAll_of_constsResolve h.2⟩
  | .forallE _ _ _, h => by
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at h
    exact ⟨constsAll_of_constsResolve h.1, constsAll_of_constsResolve h.2⟩
  | .letE _ _ _ _, h => by
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at h
    exact ⟨constsAll_of_constsResolve h.1.1, constsAll_of_constsResolve h.1.2, constsAll_of_constsResolve h.2⟩
  | .proj _ _ e, h => by
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at h
    exact constsAll_of_constsResolve (e := e) h.2

/-- A term that mentions no key `T` has every constant node other than `T`. -/
theorem constsAll_of_mentions {T : Ix.Kernel.Key md} :
    ∀ {e : Ix.Kernel.Expr md}, e.mentionsConst T = false → ConstsAll (· ≠ T) e
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .lit _, _ => trivial
  | .const _ _, h => by
    simp only [Ix.Kernel.Expr.mentionsConst, beq_eq_false_iff_ne] at h
    exact h
  | .app _ _, h => by
    simp only [Ix.Kernel.Expr.mentionsConst, Bool.or_eq_false_iff] at h
    exact ⟨constsAll_of_mentions h.1, constsAll_of_mentions h.2⟩
  | .lam _ _ _, h => by
    simp only [Ix.Kernel.Expr.mentionsConst, Bool.or_eq_false_iff] at h
    exact ⟨constsAll_of_mentions h.1, constsAll_of_mentions h.2⟩
  | .forallE _ _ _, h => by
    simp only [Ix.Kernel.Expr.mentionsConst, Bool.or_eq_false_iff] at h
    exact ⟨constsAll_of_mentions h.1, constsAll_of_mentions h.2⟩
  | .letE _ _ _ _, h => by
    simp only [Ix.Kernel.Expr.mentionsConst, Bool.or_eq_false_iff] at h
    exact ⟨constsAll_of_mentions h.1.1, constsAll_of_mentions h.1.2, constsAll_of_mentions h.2⟩
  | .proj _ _ e, h => by
    simp only [Ix.Kernel.Expr.mentionsConst, Bool.or_eq_false_iff] at h
    exact constsAll_of_mentions (e := e) h.2

/-! ## Inference and annotation -/

/-- **A term whose inference succeeds has every constant node in the environment**: inference
looks up a constant node and infers every subterm (an application's function and argument, a
binder's domain and opened body, a projection's subject), and refuses a `let`. -/
theorem inferTypeCore_constsAll {env : Ix.Kernel.Env md} :
    ∀ (fuel : Nat) {d : Nat} {e t : Ix.Kernel.Expr md}, inferTypeCore mode env fuel d e = .ok t →
      ConstsAll (fun k => (env.find? k).isSome = true) e
  | 0, _, _, _, h => by rw [inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, d, e, t, h => by
    cases e with
    | bvar | fvar | sort | lit => trivial
    | const n us =>
      obtain ⟨ci, hf, -⟩ := inferTypeCore_const_inv h
      show (env.find? n).isSome = true
      rw [hf]
      rfl
    | app f a =>
      obtain ⟨tf, ty', body', m', hf, -, -, ta, ha, -⟩ := inferTypeCore_app_inv h
      exact ⟨inferTypeCore_constsAll fuel hf, inferTypeCore_constsAll fuel ha⟩
    | lam ty body m =>
      obtain ⟨tty, u, bt, hty, -, hb, -⟩ := inferTypeCore_lam_inv h
      exact ⟨inferTypeCore_constsAll fuel hty, constsAll_of_instantiate1 (inferTypeCore_constsAll fuel hb)⟩
    | forallE ty body m =>
      obtain ⟨tty, u, bt, v, hty, -, hb, -⟩ := inferTypeCore_forall_inv h
      exact ⟨inferTypeCore_constsAll fuel hty, constsAll_of_instantiate1 (inferTypeCore_constsAll fuel hb)⟩
    | letE ty v b l => exact (inferTypeCore_letE_inv h).elim
    | proj sn i e =>
      obtain ⟨tpe, te, T, us, entry, he, -⟩ := inferTypeCore_proj_inv h
      exact inferTypeCore_constsAll fuel (e := e) he

/-- **Annotation keeps a term's constants, or finds them**: a term annotates to one whose
constant nodes satisfy `P`, with every constant of the environment satisfying `P`, only if its
own constant nodes satisfy `P`. Annotation keeps every constant node but a `let`'s type and
value, whose annotations it infers before taking the reduct. -/
theorem annotateCore_constsAll {env : Ix.Kernel.Env md} {P : Ix.Kernel.Key md → Prop}
    (hP : ∀ k, (env.find? k).isSome = true → P k) :
    ∀ (fuel : Nat) {d : Nat} {e e' : Ix.Kernel.Expr md}, annotateCore mode env fuel d e = .ok e' →
      ConstsAll P e' → ConstsAll P e
  | 0, _, _, _, h, _ => by rw [annotateCore_zero] at h; exact nomatch h
  | fuel + 1, d, e, e', h, h' => by
    cases e with
    | bvar | fvar | sort | lit => trivial
    | const n us =>
      rw [annotateCore_succ] at h
      simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact h'
    | app f a =>
      obtain ⟨f', a', hf, ha, rfl⟩ := annotateCore_app_inv h
      exact ⟨annotateCore_constsAll hP fuel hf h'.1, annotateCore_constsAll hP fuel ha h'.2⟩
    | lam ty body m =>
      obtain ⟨ty', body', pw, hty, hb, rfl⟩ := annotateCore_lam_inv h
      exact ⟨annotateCore_constsAll hP fuel hty h'.1,
        constsAll_of_instantiate1 (annotateCore_constsAll hP fuel hb (constsAll_of_abstract1 h'.2))⟩
    | forallE ty body m =>
      obtain ⟨ty', body', pw, hty, hb, rfl⟩ := annotateCore_forallE_inv h
      exact ⟨annotateCore_constsAll hP fuel hty h'.1,
        constsAll_of_instantiate1 (annotateCore_constsAll hP fuel hb (constsAll_of_abstract1 h'.2))⟩
    | letE ty v b l =>
      obtain ⟨ty', v', hty, hv, hb, tty, u, tv, hity, -, hiv, -⟩ := annotateCore_letE_inv h
      exact ⟨annotateCore_constsAll hP fuel hty (constsAll_mono hP (inferTypeCore_constsAll fuel hity)),
        annotateCore_constsAll hP fuel hv (constsAll_mono hP (inferTypeCore_constsAll fuel hiv)),
        constsAll_of_instantiate1 (annotateCore_constsAll hP fuel hb h')⟩
    | proj sn i e =>
      obtain ⟨e₂, tt, te, he, -, -, T, us, entry, -, -, -, rfl⟩ := annotateCore_proj_inv h
      exact annotateCore_constsAll hP fuel (e := e) he h'

/-! ## The front door -/

/-- **A constant the checker's front door accepted has every constant node of its type in the
environment before it**: its annotated type's constants resolve there. -/
theorem constantValRun_constsAll {μ : CheckMode} {F : Nat} {env : Ix.Kernel.Env md}
    {cv : Ix.Kernel.ConstantVal md} {type' : Ix.Kernel.Expr md} (h : Semantics.ConstantValRun μ F env cv type') :
    ConstsAll (fun k => (env.find? k).isSome = true) cv.type := by
  obtain ⟨-, -, -, -, -, -, hann, -, hres, -⟩ := h
  exact annotateCore_constsAll (fun _ hk => hk) F hann (constsAll_of_constsResolve hres)

/-- **A constant the checker's front door accepted does not name itself in its type**: the
environment before it does not hold its name. -/
theorem constantValRun_noSelf {μ : CheckMode} {F : Nat} {env : Ix.Kernel.Env md}
    {cv : Ix.Kernel.ConstantVal md} {type' : Ix.Kernel.Expr md} (h : Semantics.ConstantValRun μ F env cv type') :
    ConstsAll (· ≠ cv.name) cv.type := by
  have hfresh : (env.find? cv.name).isNone = true := h.1
  refine constsAll_mono (fun k hk e => ?_) (constantValRun_constsAll h)
  subst e
  rw [Option.isNone_iff_eq_none] at hfresh
  rw [hfresh] at hk
  cases hk

/-! ## The ingress -/

open Ix.LeanIngress (ingressExpr ingressKey ingressMData withContract)
open Ix.CompileCert.ExpressionState (ConstsSatisfy)

theorem withContract_constsAll {P : Ix.Kernel.Key .source → Prop} {c : Ix.SemanticContract.Contract}
    {e : Ix.Expr} {x y : Ix.Kernel.Expr .source} (h : withContract c e x = .ok y) :
    ConstsAll P y ↔ ConstsAll P x := by
  unfold withContract at h
  split at h <;> first
    | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact Iff.rfl)
    | cases h

/-- **The ingress maps a Lean term's constants to their keys, node for node**: a property holds
of every constant node of the conversion exactly when it holds of every constant's key in the
source. -/
theorem ingress_constsAll {σ : Ix.Name → LevelParam} {P : Ix.Kernel.Key .source → Prop} :
    ∀ {e : Ix.Expr} {k : Ix.Kernel.Expr .source}, ingressExpr σ e = .ok k →
      (ConstsAll P k ↔ ConstsSatisfy (fun n => P (ingressKey n)) e)
  | .bvar _ _, _, h => by cases h; simp only [Ix.Kernel.Expr.mkBvar_eq]; exact Iff.rfl
  | .fvar _ _, _, h => by simp [ingressExpr, throw, throwThe, MonadExceptOf.throw] at h
  | .mvar _ _, _, h => by simp [ingressExpr, throw, throwThe, MonadExceptOf.throw] at h
  | .sort _ _, _, h => by
    rw [ingressExpr] at h
    obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    exact Iff.rfl
  | .const _ _ _, _, h => by
    rw [ingressExpr] at h
    obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    exact Iff.rfl
  | .app _ _ _, _, h => by
    rw [ingressExpr] at h
    obtain ⟨_, hf, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨_, ha, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    exact and_congr (ingress_constsAll hf) (ingress_constsAll ha)
  | .lam _ _ _ _ _, _, h => by
    rw [ingressExpr] at h
    obtain ⟨_, ht, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨_, hb, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    exact and_congr (ingress_constsAll ht) (ingress_constsAll hb)
  | .forallE _ _ _ _ _, _, h => by
    rw [ingressExpr] at h
    obtain ⟨_, ht, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨_, hb, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    exact and_congr (ingress_constsAll ht) (ingress_constsAll hb)
  | .letE _ _ _ _ _ _, _, h => by
    rw [ingressExpr] at h
    obtain ⟨_, ht, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨_, hv, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨_, hb, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    exact and_congr (ingress_constsAll ht) (and_congr (ingress_constsAll hv) (ingress_constsAll hb))
  | .lit (.natVal _) _, _, h => by cases h; exact Iff.rfl
  | .lit (.strVal _) _, _, h => by cases h; exact Iff.rfl
  | .mdata _ e _, _, h => by
    rw [Ix.LeanIngress.ingressExpr_mdata] at h
    unfold ingressMData at h
    split at h
    · obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      obtain ⟨_, hx, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      exact (withContract_constsAll h).trans (ingress_constsAll (e := e) hx)
    · exact ingress_constsAll (e := e) h
  | .proj _ _ e _, _, h => by
    rw [ingressExpr] at h
    obtain ⟨_, he, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    cases h
    have hiff := ingress_constsAll (P := P) he
    exact hiff

/-- Renaming keys renames the constant nodes. -/
theorem constsAll_substKeys {P : Ix.Kernel.Key .source → Prop} (ρ : Ix.LeanIngress.FiberMap) :
    ∀ {e : Ix.Kernel.Expr .source},
      ConstsAll P (Ix.LeanIngress.Expr.substKeys ρ e) ↔ ConstsAll (fun k => P (Ix.LeanIngress.Key.subst ρ k)) e
  | .bvar _ | .fvar _ _ | .sort _ | .lit _ => Iff.rfl
  | .const _ _ => Iff.rfl
  | .app _ _ => and_congr (constsAll_substKeys ρ) (constsAll_substKeys ρ)
  | .lam _ _ _ => and_congr (constsAll_substKeys ρ) (constsAll_substKeys ρ)
  | .forallE _ _ _ => and_congr (constsAll_substKeys ρ) (constsAll_substKeys ρ)
  | .letE _ _ _ _ =>
    and_congr (constsAll_substKeys ρ) (and_congr (constsAll_substKeys ρ) (constsAll_substKeys ρ))
  | .proj _ _ e => constsAll_substKeys ρ (e := e)

/-- Mapping levels keeps the constant nodes. -/
theorem constsAll_mapLevels {P : Ix.Kernel.Key .source → Prop} (f : Ix.Kernel.Level → Ix.Kernel.Level) :
    ∀ {e : Ix.Kernel.Expr .source}, ConstsAll P (Ix.LeanIngress.mapLevels f e) ↔ ConstsAll P e
  | .bvar _ | .fvar _ _ | .sort _ | .lit _ => Iff.rfl
  | .const _ _ => Iff.rfl
  | .app _ _ => and_congr (constsAll_mapLevels f) (constsAll_mapLevels f)
  | .lam _ _ _ => and_congr (constsAll_mapLevels f) (constsAll_mapLevels f)
  | .forallE _ _ _ => and_congr (constsAll_mapLevels f) (constsAll_mapLevels f)
  | .letE _ _ _ _ =>
    and_congr (constsAll_mapLevels f) (and_congr (constsAll_mapLevels f) (constsAll_mapLevels f))
  | .proj _ _ e => constsAll_mapLevels f (e := e)

/-- The pins' canonical form keeps the constant nodes. -/
theorem constsAll_canonExpr {P : Ix.Kernel.Key md → Prop} (m : LevelParam → LevelParam) :
    ∀ {e : Ix.Kernel.Expr md}, ConstsAll P (canonExpr m e) ↔ ConstsAll P e
  | .bvar _ | .fvar _ _ | .sort _ | .lit _ => Iff.rfl
  | .const _ _ => Iff.rfl
  | .app _ _ => and_congr (constsAll_canonExpr m) (constsAll_canonExpr m)
  | .lam _ _ _ => and_congr (constsAll_canonExpr m) (constsAll_canonExpr m)
  | .forallE _ _ _ => and_congr (constsAll_canonExpr m) (constsAll_canonExpr m)
  | .letE _ _ _ _ =>
    and_congr (constsAll_canonExpr m) (and_congr (constsAll_canonExpr m) (constsAll_canonExpr m))
  | .proj _ _ e => constsAll_canonExpr m (e := e)

/--
info: 'Ix.Cert.CheckedConsts.annotateCore_constsAll' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms annotateCore_constsAll

/--
info: 'Ix.Cert.CheckedConsts.constantValRun_noSelf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms constantValRun_noSelf

/--
info: 'Ix.Cert.CheckedConsts.ingress_constsAll' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ingress_constsAll

end Ix.Cert.CheckedConsts
