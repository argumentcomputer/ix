/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.SetModel.Ops
import Ix.Theory.Certified.Level

namespace Ix.Theory.Model

open SetTheory SetModel Certified

/-- Only zero versus positive matters to the set-theoretic binder operators. -/
def regime (p : PropWhen) (values : List Nat) : Nat :=
  if p.holds (values.getD · 0) then 0 else 1

@[simp] theorem regime_zeroCondition (l : VLevel) (values : List Nat) :
    regime (zeroCondition l) values = 0 ↔ l.eval values = 0 := by
  unfold regime
  rw [zeroCondition_correct]
  by_cases h : l.eval values = 0 <;> simp [h]

@[simp] theorem regime_always (values : List Nat) : regime .always values = 0 := rfl

@[simp] theorem regime_never (values : List Nat) : regime .never values = 1 := rfl

@[simp] theorem regime_instCondition (p : PropWhen) (ls : List VLevel) (values : List Nat) :
    regime (instCondition ls p) values = regime p (ls.map (VLevel.eval values)) := by
  unfold regime
  rw [instCondition_correct]

universe u
variable {V : Type u} [SetTheory V]

/-- The universe bound for the actual product operator, including an
arbitrary-size domain when the codomain sort is zero. -/
theorem piR_mem_univ {a b : Nat} {A : V} {B : V → V}
    (hA : A ∈ˢ univ a) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ univ b) :
    piR b A B ∈ˢ univ (VLevel.natIMax a b) := by
  cases b with
  | zero =>
    change piR 0 A B ∈ˢ univ 0
    rw [univ_zero]
    exact piR_zero_mem_univZero
  | succ b =>
    have hn : Nat.max a (b + 1) ≠ 0 :=
      Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ b) (Nat.le_max_right a (b + 1)))
    simp only [VLevel.natIMax, Nat.add_one_ne_zero, ↓reduceIte]
    rw [piR_pos (Nat.succ_ne_zero b)]
    apply (univ_isTGUniverse hn).piSet_mem
    · exact univ_mono (Nat.le_max_left ..) A hA
    · intro x hx
      exact univ_mono (Nat.le_max_right ..) (B x) (hB x hx)

theorem annotated_pi_mem_univ {a : Nat} {b : VLevel} {p : PropWhen}
    {values : List Nat} {A : V} {B : V → V}
    (hp : p = zeroCondition b)
    (hA : A ∈ˢ univ a) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ univ (b.eval values)) :
    piR (regime p values) A B ∈ˢ univ (VLevel.natIMax a (b.eval values)) := by
  subst p
  rw [piR_zero_agree (regime_zeroCondition b values) (fun _ _ => rfl)]
  exact piR_mem_univ hA hB

/-- The fixed empty proposition used by the certified primitive signature. -/
noncomputable def falseValue : V := empty

theorem falseValue_uninhabited (x : V) : ¬ x ∈ˢ (falseValue : V) := not_mem_empty x

theorem falseValue_has_sort : (falseValue : V) ∈ˢ univ 0 := empty_mem_univ 0

/-- Type of dependent elimination from the empty proposition. -/
noncomputable def falseElimType (level : Nat) : V :=
  piR level (piR (level + 1) empty (fun _ => univ level)) fun motive =>
    piR level empty (fun x => app motive x)

/-- The empty eliminator is a function graph at positive sorts and the proof
point at sort zero. Its type is inhabited because its second domain is empty. -/
noncomputable def falseElimValue (level : Nat) : V :=
  lamR level (piR (level + 1) empty (fun _ => univ level)) fun _ =>
    lamR level empty (fun _ => empty)

theorem falseElimValue_mem (level : Nat) :
    (falseElimValue level : V) ∈ˢ falseElimType level := by
  apply lamR_mem
  intro motive _
  apply lamR_mem
  intro x hx
  exact (not_mem_empty x hx).elim

end Ix.Theory.Model
