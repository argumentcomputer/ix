import IxCC.Lam.Semantics

/-! # Lam: basic properties

Determinism holds by construction (`eval` is a function; stated below).
The rules below are the ones erasure's proof reads off directly: □ is stuck
under application, projection, `case` and primitives, a key
mismatch in `proj` is stuck, and `tick`, `glob` and closure entry charge
exactly one unit. Clock monotonicity (`eval k ρ t = r → r ≠ timeout → k ≤ k'
→ eval k' ρ t = r`) is proved (`Lam.eval_mono`); `tests-lam` also checks it
on random clocks. -/

namespace IxCC.Lam

open IxCC.Sem (Result)

variable {P : Program} {k : Nat} {ρ : Env}

theorem eval_deterministic {t : Term} {r₁ r₂ : Result Val} (h₁ : eval P k ρ t = r₁)
    (h₂ : eval P k ρ t = r₂) : r₁ = r₂ := h₁ ▸ h₂

theorem eval_box : eval P k ρ .box = .ok .box := by
  rw [eval]

theorem eval_trap : eval P k ρ .trap = .trap := by
  rw [eval]

theorem eval_tick_zero (t : Term) : eval P 0 ρ (.tick t) = .timeout := by
  rw [eval]

theorem eval_tick_succ (t : Term) : eval P (k + 1) ρ (.tick t) = eval P k ρ t := by
  rw [eval]

theorem eval_glob_succ {g : GlobalId} {gl : Global} (h : P.global? g = some gl) :
    eval P (k + 1) ρ (.glob g) = eval P k [] gl.body := by
  rw [eval]; simp [h]

theorem eval_glob_zero (g : GlobalId) : eval P 0 ρ (.glob g) = .timeout ∨
    eval P 0 ρ (.glob g) = .stuck := by
  rw [eval]; split <;> simp

theorem apply_clos_succ (ρ' : Env) (b : Term) (s : Slot) :
    apply P (k + 1) (.clos ρ' b) s = eval P k (s :: ρ') b := by
  rw [apply]

/-- □ is stuck under application. -/
theorem apply_box (s : Slot) : apply P k .box s = .stuck := by
  rw [apply]; intros; contradiction

/-- A constructor or literal is stuck under application. -/
theorem apply_con (c : Key.CtorKey) (fs : List Val) (s : Slot) :
    apply P k (.con c fs) s = .stuck := by
  rw [apply]; intros; contradiction

/-- □ is stuck under projection. -/
theorem eval_proj_box {c : Key.CtorKey} {i : Nat} {s : Term} (h : eval P k ρ s = .ok .box) :
    eval P k ρ (.proj c i s) = .stuck := by
  rw [eval, h]

/-- A projection with another constructor's key is stuck. -/
theorem eval_proj_key {c c' : Key.CtorKey} {i : Nat} {s : Term} {fs : List Val}
    (h : eval P k ρ s = .ok (.con c' fs)) (hc : c' ≠ c) :
    eval P k ρ (.proj c i s) = .stuck := by
  rw [eval, h]; simp [hc]

/-- □ is stuck as a `case` scrutinee. -/
theorem eval_case_box {s : Term} {alts : List Alt} {d : Option Term}
    (h : eval P k ρ s = .ok .box) : eval P k ρ (.case s alts d) = .stuck := by
  rw [eval, h]; rfl

theorem natArgs_box (vs : List Val) (h : Val.box ∈ vs) : natArgs vs = none := by
  induction vs with
  | nil => cases h
  | cons v vs ih =>
    cases h with
    | head => rfl
    | tail _ h' =>
      match v with
      | .lit (.nat n) => simp [natArgs, ih h']
      | .lit (.str _) | .box | .clos .. | .con .. => rfl

/-- □ is stuck as a primitive argument. -/
theorem primResult_box (K : Known) (p : Prim) (vs : List Val) (h : Val.box ∈ vs) :
    primResult K p vs = .stuck := by
  simp [primResult, natArgs_box vs h]

end IxCC.Lam
