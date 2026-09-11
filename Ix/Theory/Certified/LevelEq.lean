/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Level

namespace Ix.Theory.Certified

namespace LevelEq

/-- A structural upper-bound check, used only when it proves pointwise
ordering. In particular, a field at u fits a carrier at u+1. -/
def leq (a b : VLevel) : Bool :=
  if a = b then true else
    match a, b with
    | .zero, _ => true
    | .max a b, c => leq a c && leq b c
    | a, .max b c => leq a b || leq a c
    | .succ a, .succ b => leq a b
    | a, .succ b => leq a b
    | .imax a b, c => leq a c && leq b c
    | _, _ => false
termination_by sizeOf a + sizeOf b

theorem leq_sound {a b : VLevel} (h : leq a b = true) (values : List Nat) :
    a.eval values ≤ b.eval values := by
  unfold leq at h
  split at h
  next he => subst b; exact Nat.le_refl _
  next =>
    split at h
    next => exact Nat.zero_le _
    next a b c =>
      simp only [Bool.and_eq_true] at h
      exact Nat.max_le.mpr ⟨leq_sound h.1 values, leq_sound h.2 values⟩
    next a b c =>
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact Nat.le_trans (leq_sound h values) (Nat.le_max_left _ _)
      · exact Nat.le_trans (leq_sound h values) (Nat.le_max_right _ _)
    next a b => exact Nat.succ_le_succ (leq_sound h values)
    next a b => exact Nat.le_trans (leq_sound h values) (Nat.le_succ _)
    next a b c =>
      simp only [Bool.and_eq_true] at h
      have hm := Nat.max_le.mpr ⟨leq_sound h.1 values, leq_sound h.2 values⟩
      change VLevel.natIMax _ _ ≤ _
      unfold VLevel.natIMax
      split
      · exact Nat.zero_le _
      · exact hm
    next => contradiction
termination_by sizeOf a + sizeOf b

/-- Conservative simplification. Failure to identify equivalent levels is a
decline, never permission to compare their zero conditions as full levels. -/
def max (a b : VLevel) : VLevel :=
  match a, b with
  | .zero, b => b
  | a, .zero => a
  | a, b => if leq a b then b else if leq b a then a else .max a b

theorem eval_max (a b : VLevel) (values : List Nat) :
    (max a b).eval values = Nat.max (a.eval values) (b.eval values) := by
  unfold max
  split <;> simp_all [VLevel.eval]
  split
  next h => exact (Nat.max_eq_right (leq_sound h values)).symm
  next =>
    split
    next h => exact (Nat.max_eq_left (leq_sound h values)).symm
    next => rfl

def imax (a b : VLevel) : VLevel :=
  match a, b with
  | _, .zero => .zero
  | a, .succ b => max a (.succ b)
  | .zero, b => b
  | a, b => if a = b then a else .imax a b

theorem eval_imax (a b : VLevel) (values : List Nat) :
    (imax a b).eval values = VLevel.natIMax (a.eval values) (b.eval values) := by
  unfold imax
  split
  · simp [VLevel.eval, VLevel.natIMax]
  · simp [eval_max, VLevel.eval, VLevel.natIMax]
  · simp only [VLevel.eval, VLevel.natIMax, Nat.zero_max]
    split <;> simp_all
  · split
    · subst b
      simp [VLevel.natIMax]
    · rfl

def normalize : VLevel → VLevel
  | .zero => .zero
  | .param i => .param i
  | .succ a => .succ (normalize a)
  | .max a b => max (normalize a) (normalize b)
  | .imax a b => imax (normalize a) (normalize b)

theorem eval_normalize (l : VLevel) (values : List Nat) :
    (normalize l).eval values = l.eval values := by
  induction l <;> simp_all [normalize, VLevel.eval, eval_max, eval_imax]

def check (n : Nat) (a b : VLevel) : Bool :=
  decide (a.WF n ∧ b.WF n) && decide (normalize a = normalize b)

theorem check_sound {n : Nat} {a b : VLevel} (h : check n a b = true) :
    a.WF n ∧ b.WF n ∧ ∀ values, a.eval values = b.eval values := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1, h.1.2, fun values => ?_⟩
  rw [← eval_normalize a values, ← eval_normalize b values, h.2]

end LevelEq

end Ix.Theory.Certified
