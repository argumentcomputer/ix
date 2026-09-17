/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Std/Basic.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
Import trim (2026-09-17): `Batteries.Data.List.Basic` dropped; `List.Forall₂`
replaced by the local `Ix.Kernel.Forall₂` with the same two lemmas.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Init.Omega

namespace Ix.Kernel

/-- Pointwise relation between two lists of the same length. A local
replacement for Batteries' `List.Forall₂`, so the kernel depends on Lean core
only; the name stays under `Ix.Kernel` to avoid clashing with Batteries in
packages that import both. -/
inductive Forall₂ (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → Forall₂ R as bs → Forall₂ R (a :: as) (b :: bs)

protected theorem Forall₂.rfl
    {R : α → α → Prop} {xs : List α} (h : ∀ x ∈ xs, R x x) : Forall₂ R xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    exact .cons h.1 (ih h.2)

protected theorem Forall₂.length_eq
    {R : α → β → Prop} {left : List α} {right : List β}
    (related : Forall₂ R left right) : left.length = right.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih
theorem List.map_id_mem {f : α → α} (xs : List α) (h : ∀ x ∈ xs, f x = x) :
    xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.mem_cons, forall_eq_or_imp] at h; simp [h.1, ih h.2]

end Ix.Kernel
