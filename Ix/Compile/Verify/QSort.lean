/-
Adapted for Ix from `Ix/Theory/Named/Verify/QSort.lean` (the named tree's
adaptation of lean4lean's `Lean4Lean/Verify/QSort.lean`): only the size and
permutation half of the verification is kept, under the compiler-verification
namespace.  The named tree's Apache license is in `Ix/Theory/Named/LICENSE`.
SPDX-License-Identifier: Apache-2.0
-/

/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import Init.Data.Array.Basic
import all Init.Data.Array.QSort.Basic

/-!
# Permutation property of `Array.qsort`

Adapted from the verification in leanprover/lean4#14658
(tests/elab/grind_qsort.lean on the `qsort_verification` branch).

The theorems are:
* `size_qsort : (qsort as lt lo hi).size = as.size`
* `qsort_perm : qsort as lt lo hi ~ as`
-/
namespace Ix.Compile.Verify.QSort

open Array List Vector

attribute [grind =] Vector.toArray_perm_iff
attribute [grind =] Vector.perm_toArray_iff

attribute [grind .] Vector.swap_perm

attribute [grind .] List.Perm.refl
attribute [grind .] Array.Perm.refl
attribute [grind .] Vector.Perm.refl

grind_pattern List.Perm.trans => l₁ ~ l₂, l₁ ~ l₃
grind_pattern Array.Perm.trans => xs ~ ys, xs ~ zs
grind_pattern Vector.Perm.trans => xs ~ ys, xs ~ zs

/-- Variant of `List.Perm.take` specifying the permutation is constant after `i` elementwise. -/
theorem List.Perm.take_of_getElem {l₁ l₂ : List α} (h : l₁ ~ l₂) {i : Nat}
    (w : ∀ j, i ≤ j → (_ : j < l₁.length) → l₁[j] = l₂[j]'(by have := h.length_eq; omega)) :
    l₁.take i ~ l₂.take i := by
  apply h.take_of_getElem?
  intro j hij
  by_cases h_length₁ : j < l₁.length
  <;> have h_length₂ := h.length_eq ▸ h_length₁
  <;> grind

/-- Variant of `List.Perm.drop` specifying the permutation is constant before `i` elementwise. -/
theorem List.Perm.drop_of_getElem {l₁ l₂ : List α} (h : l₁ ~ l₂) {i : Nat}
    (w : ∀ j, j < i → (_ : j < l₁.length) → l₁[j] = l₂[j]'(by have := h.length_eq; omega)) :
    l₁.drop i ~ l₂.drop i := by
  apply h.drop_of_getElem?
  intro j hij
  by_cases h_length₁ : j < l₁.length
  <;> have h_length₂ := h.length_eq ▸ h_length₁
  <;> grind

private theorem getElem_mk {l : List α} {i : Nat} (h : i < l.length) :
    (Array.mk l)[i]'(by simpa using h) = l[i] := by
  rw [← Array.getElem_toList]

theorem Array.Perm.extract' {xs ys : Array α} (h : xs ~ ys) {lo hi : Nat}
    (wlo : ∀ i, i < lo → (_ : i < xs.size) → xs[i] = ys[i]'(by have := h.size_eq; omega))
    (whi : ∀ i, hi ≤ i → (_ : i < xs.size) → xs[i] = ys[i]'(by have := h.size_eq; omega)) :
    xs.extract lo hi ~ ys.extract lo hi := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp_all only [Array.perm_iff_toList_perm, List.extract_toArray]
  apply List.Perm.take_of_getElem
    (w := fun i h₁ h₂ => by
      rw [List.getElem_drop, List.getElem_drop, ← getElem_mk, ← getElem_mk]
      exact whi (lo + i) (by omega) (by grind))
  apply List.Perm.drop_of_getElem
    (w := fun i h₁ h₂ => by
      rw [← getElem_mk, ← getElem_mk]
      exact wlo i h₁ (by grind))
  simpa using List.perm_iff_toArray_perm.mpr h

theorem Vector.Perm.extract' {xs ys : Vector α n} (h : xs ~ ys) {lo hi : Nat}
    (wlo : ∀ i, i < lo → (_ : i < n) → xs[i] = ys[i]) (whi : ∀ i, hi ≤ i → (_ : i < n) → xs[i] = ys[i]) :
    xs.extract lo hi ~ ys.extract lo hi := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, h⟩
  exact ⟨Array.Perm.extract' h.toArray (by simpa using wlo) (by simpa using whi)⟩

attribute [grind .] Array.Perm.extract'
attribute [grind .] Vector.Perm.extract'

variable (lt : α → α → Bool) (lo hi : Nat)

@[simp, grind =] public theorem size_qsort (as : Array α) :
    (qsort as lt lo hi).size = as.size := by
  grind [qsort]

private theorem qpartition_loop_perm (as : Vector α n)
    (hhi : hi < n) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi) :
    (qpartition.loop lt lo hi hhi pivot as i k).2 ~ as := by
  fun_induction qpartition.loop with grind

@[local grind .]
private theorem qpartition_perm
    (as : Vector α n) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (qpartition as lt lo hi).2 ~ as := by
  unfold qpartition
  refine Vector.Perm.trans (qpartition_loop_perm ..) ?_
  repeat' first
  | split
  | grind
  | refine Vector.Perm.trans (Vector.swap_perm ..) ?_

private theorem qsort_sort_perm
    (as : Vector α n) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    qsort.sort lt as lo hi w hlo hhi ~ as := by
  fun_induction qsort.sort with grind

grind_pattern qsort_sort_perm => qsort.sort lt as lo hi w hlo hhi

public theorem qsort_perm (as : Array α) : qsort as lt lo hi ~ as := by
  grind [qsort]

end Ix.Compile.Verify.QSort
