import IxCCGrounding.Model

/-!
# Lifting and environment agreement for `Denotes` (`IxCCGrounding.Lift`)

Moved out of `IxCCGrounding.Subst` (names and statements unchanged) so that the relation's
environment lemma under a binder (`relEnv_lift`, `IxCCGrounding.Apply`) can use them:

* **Environment agreement** (`den_agree`): a term denotes the same set in two variable
  environments that agree on its loose variables (`looseIn`).
* **Lifting** (`den_lift`): a term lifted by `k` above `c` denotes in `ρ` what the term denotes in
  `skipEnv ρ k c`, the environment that skips the `k` inserted indices.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

theorem looseIn_natLit (i n : Nat) : looseIn i (natLitToConstructor (md := .anon) n) = false := by
  cases n <;> simp [natLitToConstructor, looseIn]

theorem looseIn_strLit (i : Nat) (s : String) :
    looseIn i (strLitToConstructor (md := .anon) s) = false := by
  unfold strLitToConstructor
  generalize s.toList = l
  induction l with
  | nil => simp [looseIn]
  | cons c cs ih => simp only [List.foldr_cons, looseIn, Bool.false_or] at ih ⊢; exact ih

section Envs

variable {V : Type w}

/-- The environment that skips the `k` indices inserted at `c`. -/
def skipEnv (ρ : BVarIdx → V) (k c : Nat) : BVarIdx → V := fun i =>
  if i < c then ρ i else ρ (i + k)

theorem skipEnv_push (x : V) (ρ : BVarIdx → V) (k c : Nat) :
    skipEnv (push x ρ) k (c + 1) = push x (skipEnv ρ k c) := by
  funext i
  cases i with
  | zero => simp [skipEnv, push]
  | succ i =>
    show (if i + 1 < c + 1 then push x ρ (i + 1) else push x ρ (i + 1 + k)) = skipEnv ρ k c i
    simp only [skipEnv]
    by_cases h : i < c
    · have h' : i + 1 < c + 1 := by omega
      simp only [h, h', ↓reduceIte]; rfl
    · have h' : ¬ i + 1 < c + 1 := by omega
      simp only [h, h', ↓reduceIte]
      rw [show i + 1 + k = (i + k) + 1 by omega]; rfl

end Envs

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

section Den

variable {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat}

/-! ## Environment agreement -/

/-- **A term denotes the same set in two environments that agree on its loose variables.** -/
theorem den_agree {ρ : BVarIdx → V} {e : KExpr} {X : V} (h : Denotes cval env φ ρ e X) :
    ∀ {ρ' : BVarIdx → V}, (∀ i, looseIn i e = true → ρ i = ρ' i) → Denotes cval env φ ρ' e X := by
  induction h with
  | @bvar ρ i =>
    intro ρ' hag
    rw [hag i (by simp [looseIn])]
    exact .bvar
  | sort => intro _ _; exact .sort
  | const hf hl => intro _ _; exact .const hf hl
  | app _ _ ihf iha =>
    intro ρ' hag
    exact .app (ihf fun i hi => hag i (by simp [looseIn, hi]))
      (iha fun i hi => hag i (by simp [looseIn, hi]))
  | lam _ _ hP ihA ihF =>
    intro ρ' hag
    refine .lam (ihA fun i hi => hag i (by simp [looseIn, hi])) (fun x hx => ihF x hx ?_) hP
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hag i (by simp [looseIn, hi])
  | pi _ _ hP ihA ihB =>
    intro ρ' hag
    refine .pi (ihA fun i hi => hag i (by simp [looseIn, hi])) (fun x hx => ihB x hx ?_) hP
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hag i (by simp [looseIn, hi])
  | proj_table ht _ ih => intro ρ' hag; exact .proj_table ht (ih fun i hi => hag i (by simpa [looseIn] using hi))
  | proj_fst ht _ ih => intro ρ' hag; exact .proj_fst ht (ih fun i hi => hag i (by simpa [looseIn] using hi))
  | proj_snd ht _ ih => intro ρ' hag; exact .proj_snd ht (ih fun i hi => hag i (by simpa [looseIn] using hi))
  | natLit _ ih =>
    intro ρ' _
    exact .natLit (ih fun i hi => by rw [looseIn_natLit] at hi; cases hi)
  | strLit _ ih =>
    intro ρ' _
    exact .strLit (ih fun i hi => by rw [looseIn_strLit] at hi; cases hi)

/-! ## Lifting -/

theorem den_const_env {ρ ρ' : BVarIdx → V} {n : KKey} {us : List Level} {X : V}
    (h : Denotes cval env φ ρ (.const n us) X) : Denotes cval env φ ρ' (.const n us) X := by
  cases h with
  | const hf hl => exact .const hf hl

/-- **A lifted term denotes in `ρ` what the term denotes with the inserted indices skipped.** -/
theorem den_lift (k : Nat) (e : KExpr) : ∀ (c : Nat) (ρ : BVarIdx → V) (X : V),
    Denotes cval env φ ρ (e.liftLooseBVars k c) X ↔ Denotes cval env φ (skipEnv ρ k c) e X := by
  induction e with
  | bvar i =>
    intro c ρ X
    simp only [Expr.liftLooseBVars]
    by_cases h : i ≥ c
    · have h' : ¬ i < c := by omega
      simp only [h, h', ↓reduceIte, den_bvar, skipEnv]
    · have h' : i < c := by omega
      simp only [h, h', ↓reduceIte, den_bvar, skipEnv]
  | fvar _ _ _ =>
    intro c ρ X
    simp only [Expr.liftLooseBVars]
    constructor <;> intro h <;> cases h
  | sort u =>
    intro c ρ X
    simp only [Expr.liftLooseBVars, den_sort]
  | const n us =>
    intro c ρ X
    simp only [Expr.liftLooseBVars]
    exact ⟨den_const_env, den_const_env⟩
  | app f a ihf iha =>
    intro c ρ X
    simp only [Expr.liftLooseBVars, den_app, ihf, iha]
  | lam ty body m iht ihb =>
    intro c ρ X
    simp only [Expr.liftLooseBVars, den_lam, iht, ihb, skipEnv_push]
  | forallE ty body m iht ihb =>
    intro c ρ X
    simp only [Expr.liftLooseBVars, den_pi, iht, ihb, skipEnv_push]
  | letE _ _ _ _ _ _ _ =>
    intro c ρ X
    simp only [Expr.liftLooseBVars]
    constructor <;> intro h <;> cases h
  | lit l =>
    intro c ρ X
    simp only [Expr.liftLooseBVars]
    exact ⟨fun h => den_agree h fun i hi => by simp [looseIn] at hi,
      fun h => den_agree h fun i hi => by simp [looseIn] at hi⟩
  | proj s i e ih =>
    intro c ρ X
    simp only [Expr.liftLooseBVars]
    constructor
    · intro h
      cases h with
      | proj_table ht he => exact .proj_table ht ((ih c ρ _).mp he)
      | proj_fst ht he => exact .proj_fst ht ((ih c ρ _).mp he)
      | proj_snd ht he => exact .proj_snd ht ((ih c ρ _).mp he)
    · intro h
      cases h with
      | proj_table ht he => exact .proj_table ht ((ih c ρ _).mpr he)
      | proj_fst ht he => exact .proj_fst ht ((ih c ρ _).mpr he)
      | proj_snd ht he => exact .proj_snd ht ((ih c ρ _).mpr he)

end Den

end IxCC.Grounding
