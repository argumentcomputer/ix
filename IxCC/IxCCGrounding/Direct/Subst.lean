import IxCCGrounding.Tele

/-!
# Substitution of a term for a bound variable (`IxCCGrounding.Direct.Subst`)

**Part B.** What β and the walk along a spine need of the kernel's model, from `Denotes`'s rules
alone (and `cval_params` for the last lemma):

* `den_inst1Lift`: a term with the variable at depth `xs.length` replaced by `a` (lifted past the
  binders crossed) denotes, under the sets `xs`, what the term denotes with `a`'s set bound
  beneath them;
* `fits_inst1Lift`: `Fits` across the same substitution, when the telescope has a `∀` for every
  argument before substitution (without that, a telescope whose tail is the substituted variable
  becomes a `∀` only after substitution, which `Fits`, read syntactically, does not follow);
* `fits_uninst`: `Fits` of a type instantiated at levels `us` back to the assignment those levels
  induce, what `Laws.proj_ctor` is stated at.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

variable {V : Type w}

theorem pushAll_ge {xs : List V} {ρ : BVarIdx → V} {i : Nat} (h : xs.length ≤ i) :
    pushAll xs ρ i = ρ (i - xs.length) := by
  simp only [pushAll, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simpa using h)]
  rfl

variable [Ix.Kernel.SetTheory V] {env : KEnv}

section Den

variable {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat}

/-- **Substitution**: the variable at depth `xs.length` replaced by `a`. -/
theorem den_inst1Lift {a : KExpr} {A : V} {ρ : BVarIdx → V} (ha : Denotes cval env φ ρ a A) :
    ∀ (e : KExpr) (xs : List V) (Y : V),
      Denotes cval env φ (pushAll xs ρ) (e.instantiate1Lift a xs.length) Y ↔
        Denotes cval env φ (pushAll xs (push A ρ)) e Y := by
  intro e
  induction e with
  | bvar i =>
    intro xs Y
    simp only [Expr.instantiate1Lift]
    by_cases h1 : i = xs.length
    · subst h1
      simp only [↓reduceIte]
      rw [den_lift, skipEnv_zero, den_bvar]
      have e1 : (fun j => pushAll xs ρ (j + xs.length)) = ρ := funext fun j => pushAll_offset xs ρ j
      have e2 : pushAll xs (push A ρ) xs.length = A := by
        have := pushAll_offset xs (push A ρ) 0
        simpa [push] using this
      rw [e1, e2]
      exact ⟨fun h => Denotes_functional h ha, fun h => h ▸ ha⟩
    · simp only [h1, ↓reduceIte, den_bvar]
      by_cases h2 : i > xs.length
      · simp only [h2, ↓reduceIte, den_bvar]
        rw [pushAll_ge (by omega), pushAll_ge (by omega)]
        have : i - xs.length = (i - 1 - xs.length) + 1 := by omega
        rw [this]
        rfl
      · simp only [h2, ↓reduceIte, den_bvar]
        rw [pushAll_lt (E' := push A ρ) (by omega)]
  | fvar _ _ _ =>
    intro xs Y
    simp only [Expr.instantiate1Lift]
    constructor <;> intro h <;> cases h
  | sort u =>
    intro xs Y
    simp only [Expr.instantiate1Lift, den_sort]
  | const n us =>
    intro xs Y
    simp only [Expr.instantiate1Lift]
    exact ⟨den_const_env, den_const_env⟩
  | app f b ihf ihb =>
    intro xs Y
    simp only [Expr.instantiate1Lift, den_app, ihf, ihb]
  | lam ty body m iht ihb =>
    intro xs Y
    have key : ∀ x Z, Denotes cval env φ (push x (pushAll xs ρ))
        (body.instantiate1Lift a (xs.length + 1)) Z ↔
          Denotes cval env φ (push x (pushAll xs (push A ρ))) body Z := fun x Z => by
      rw [← pushAll_snoc, ← pushAll_snoc, show xs.length + 1 = (xs ++ [x]).length by simp]
      exact ihb (xs ++ [x]) Z
    simp only [Expr.instantiate1Lift, den_lam, iht, key]
  | forallE ty body m iht ihb =>
    intro xs Y
    have key : ∀ x Z, Denotes cval env φ (push x (pushAll xs ρ))
        (body.instantiate1Lift a (xs.length + 1)) Z ↔
          Denotes cval env φ (push x (pushAll xs (push A ρ))) body Z := fun x Z => by
      rw [← pushAll_snoc, ← pushAll_snoc, show xs.length + 1 = (xs ++ [x]).length by simp]
      exact ihb (xs ++ [x]) Z
    simp only [Expr.instantiate1Lift, den_pi, iht, key]
  | letE _ _ _ _ _ _ _ =>
    intro xs Y
    simp only [Expr.instantiate1Lift]
    constructor <;> intro h <;> cases h
  | lit l =>
    intro xs Y
    simp only [Expr.instantiate1Lift]
    exact ⟨fun h => den_agree h fun i hi => by simp [looseIn] at hi,
      fun h => den_agree h fun i hi => by simp [looseIn] at hi⟩
  | proj s i e ih =>
    intro xs Y
    simp only [Expr.instantiate1Lift]
    constructor
    · intro h
      cases h with
      | proj_table ht he => exact .proj_table ht ((ih xs _).mp he)
      | proj_fst ht he => exact .proj_fst ht ((ih xs _).mp he)
      | proj_snd ht he => exact .proj_snd ht ((ih xs _).mp he)
    · intro h
      cases h with
      | proj_table ht he => exact .proj_table ht ((ih xs _).mpr he)
      | proj_fst ht he => exact .proj_fst ht ((ih xs _).mpr he)
      | proj_snd ht he => exact .proj_snd ht ((ih xs _).mpr he)

/-- At depth `0`. -/
theorem den_inst1Lift0 {a : KExpr} {A : V} {ρ : BVarIdx → V} (ha : Denotes cval env φ ρ a A)
    (e : KExpr) (Y : V) :
    Denotes cval env φ ρ (e.instantiate1Lift a 0) Y ↔ Denotes cval env φ (push A ρ) e Y := by
  have := den_inst1Lift ha e [] Y
  simpa [pushAll_nil] using this

/-- **`Fits` across the substitution**, when the telescope has a `∀` for every argument. -/
theorem fits_inst1Lift {a : KExpr} {A : V} {ρ : BVarIdx → V} (ha : Denotes cval env φ ρ a A) :
    ∀ (xs : List V) (T : KExpr) (ys : List V) (σ : BVarIdx → V) (R : KExpr),
      xs.length ≤ kPis T →
      Fits cval env φ (pushAll ys ρ) (T.instantiate1Lift a ys.length) xs σ R →
      ∃ σ' R', Fits cval env φ (pushAll ys (push A ρ)) T xs σ' R'
  | [], _, _, _, _, _, _ => ⟨_, _, .nil⟩
  | x :: xs, T, ys, σ, R, hk, h => by
    cases T with
    | forallE D B m =>
      simp only [Expr.instantiate1Lift] at h
      cases h with
      | cons hD hx hrest =>
        rw [← pushAll_snoc] at hrest
        have hrest' : Fits cval env φ (pushAll (ys ++ [x]) ρ)
            (B.instantiate1Lift a (ys ++ [x]).length) xs σ R := by simpa using hrest
        obtain ⟨σ', R', hf⟩ := fits_inst1Lift ha xs B (ys ++ [x]) σ R
          (by simp only [kPis, List.length_cons] at hk; omega) hrest'
        rw [pushAll_snoc] at hf
        exact ⟨σ', R', .cons ((den_inst1Lift ha D ys _).mp hD) hx hf⟩
    | _ => simp [kPis] at hk

end Den

/-- **`Fits` back to the assignment the levels induce**: a telescope whose level parameters are
among `ks`, which denotes at `ψ`, fits there whatever its instantiation by `us` fits at `φ`, when
`ψ` agrees on `ks` with the assignment `us` induces at `φ`. -/
theorem fits_uninst (M : Model V env) (hL : Laws M) {ks : List LevelParam} {us : List Level}
    {φ ψ : LevelParam → Nat} (hψ : ∀ p ∈ ks, Level.substFn φ ks us p = ψ p) :
    ∀ (xs : List V) (T : KExpr) (ρ σ : BVarIdx → V) (R : KExpr) (TT : V),
      T.allLevelParamsDefined ks = true → Denotes M.cval env ψ ρ T TT →
      Fits M.cval env φ ρ (T.instantiateLevelParams ks us) xs σ R →
      ∃ σ' R', Fits M.cval env ψ ρ T xs σ' R'
  | [], _, _, _, _, _, _, _, _ => ⟨_, _, .nil⟩
  | x :: xs, T, ρ, σ, R, TT, hd, hT, h => by
    cases T with
    | forallE D B m =>
      simp only [Expr.instantiateLevelParams] at h
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
      cases h with
      | cons hD hx hrest =>
        obtain ⟨Dd, Bf, hDd, hB, _, _⟩ := den_pi.mp hT
        have hD' := den_inst M hL hψ hDd hd.1.1
        obtain rfl := Denotes_functional hD hD'
        obtain ⟨σ', R', hf⟩ := fits_uninst M hL hψ xs B _ σ R _ hd.1.2 (hB x hx) hrest
        exact ⟨σ', R', .cons hDd hx hf⟩
    | _ => cases h

end IxCC.Grounding
