import Batteries.Tactic.OpenPrivate
import Init.Data.Array.QSort.Basic

/-!
# `Array.qsort` permutes its input

Pass 1 sorts arrays of node indices with `Array.qsort` (`Ix/Compile/Canon/Graph.lean`: the
successor lists of `sccsOf` and every component Tarjan pops). Only the set of elements
matters to the component theorems; core proves nothing about `qsort`, so this module proves
that it is a permutation (`qsort_perm`, `mem_qsort`), through its private `sort` and
`qpartition.loop` (opened with Batteries' `open private`).
-/

open private Array.qsort.sort from Init.Data.Array.QSort.Basic
open private Array.qpartition.loop from Init.Data.Array.QSort.Basic

namespace Ix.CompileCert.Canon

theorem vector_swap_perm {α : Type u} {n : Nat} (as : Vector α n) (i j : Nat) (hi : i < n)
    (hj : j < n) : (as.swap i j hi hj).toArray.Perm as.toArray := by
  rw [Vector.toArray_swap]; exact Array.swap_perm _ _

theorem qpartition_loop_perm {α : Type u} {n : Nat} (lt : α → α → Bool) (lo hi : Nat)
    (hhi : hi < n) (pivot : α) (as : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k)
    (w : k ≤ hi) :
    (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).2.toArray.Perm as.toArray := by
  rw [Array.qpartition.loop]
  split
  · split
    · exact (qpartition_loop_perm lt lo hi hhi pivot _ _ _ _ _ _).trans (vector_swap_perm _ _ _ (by omega) (by omega))
    · exact qpartition_loop_perm lt lo hi hhi pivot _ _ _ _ _ _
  · exact vector_swap_perm _ _ _ (by omega) (by omega)
termination_by hi - k

theorem qpartition_perm {α : Type u} {n : Nat} (as : Vector α n) (lt : α → α → Bool)
    (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (Array.qpartition as lt lo hi w hlo hhi).2.toArray.Perm as.toArray := by
  unfold Array.qpartition
  simp only
  refine (qpartition_loop_perm _ _ _ _ _ _ _ _ _ _ _).trans ?_
  split <;> split <;> split
  all_goals first
    | exact Array.Perm.refl _
    | exact vector_swap_perm _ _ _ (by omega) (by omega)
    | exact (vector_swap_perm _ _ _ (by omega) (by omega)).trans (vector_swap_perm _ _ _ (by omega) (by omega))
    | exact ((vector_swap_perm _ _ _ (by omega) (by omega)).trans (vector_swap_perm _ _ _ (by omega) (by omega))).trans
        (vector_swap_perm _ _ _ (by omega) (by omega))

theorem qsort_sort_perm {α : Type u} (lt : α → α → Bool) {n : Nat} (as : Vector α n)
    (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    (Array.qsort.sort lt as lo hi w hlo hhi).toArray.Perm as.toArray := by
  rw [Array.qsort.sort]
  split
  · split
    rename_i mid hmid as' heq
    have hp : as'.toArray.Perm as.toArray := by
      have := qpartition_perm as lt lo hi w hlo hhi
      rw [heq] at this; exact this
    split
    · exact hp
    · rename_i h₂
      exact ((qsort_sort_perm lt _ _ _ _ _ _).trans (qsort_sort_perm lt _ _ _ _ _ _)).trans hp
  · exact Array.Perm.refl _
termination_by hi - lo

/-- `Array.qsort` permutes its input. -/
theorem qsort_perm {α : Type u} (as : Array α) (lt : α → α → Bool) : (as.qsort lt).Perm as := by
  unfold Array.qsort
  split
  · exact Array.Perm.refl _
  · exact qsort_sort_perm lt _ _ _ _ _ _

theorem mem_qsort {α : Type u} {as : Array α} {lt : α → α → Bool} {x : α} :
    x ∈ as.qsort lt ↔ x ∈ as :=
  (qsort_perm as lt).mem_iff

end Ix.CompileCert.Canon
