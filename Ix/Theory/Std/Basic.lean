/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Batteries.Data.List.Basic
import Init.Omega

namespace Ix.Theory

protected theorem List.Forall₂.rfl
    {R : α → α → Prop} {xs : List α} (h : ∀ x ∈ xs, R x x) : xs.Forall₂ R xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    exact .cons h.1 (ih h.2)

protected theorem List.Forall₂.length_eq
    {R : α → β → Prop} {left : List α} {right : List β}
    (related : List.Forall₂ R left right) : left.length = right.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih
theorem List.map_id_mem {f : α → α} (xs : List α) (h : ∀ x ∈ xs, f x = x) :
    xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.mem_cons, forall_eq_or_imp] at h; simp [h.1, ih h.2]

end Ix.Theory
