module

public import Init.Data.Array.Lemmas
public import Init.Data.Array.Extract
import Lean.Elab.Tactic.Omega

public section

namespace Ix.Compile.Parallel

/-- Evaluate a map on bounded, consecutive chunks and join them in input order.
`width` is a task count, independent of the runtime's worker pool size. -/
@[expose] def map {α β : Type} (width : Nat) (f : α → β) (xs : Array α) : Array β :=
  let width := max 1 width
  let n := xs.size
  let size := (n + width - 1) / width
  let chunks := if size == 0 then 0 else (n + size - 1) / size
  (((Array.range chunks).map fun c => Task.spawn fun _ =>
    (xs.extract (c * size) ((c + 1) * size)).map f).map Task.get).flatten

/-- Consecutive slices of an array form its corresponding prefix. -/
theorem slices_flatten {α : Type} (xs : Array α) (s : Nat) :
    ∀ k, ((Array.range k).map fun c => xs.extract (c * s) ((c + 1) * s)).flatten =
      xs.extract 0 (k * s) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Array.range_succ, Array.map_append, Array.flatten_append, ih]
    rw [show ((#[k] : Array Nat).map fun c => xs.extract (c * s) ((c + 1) * s)).flatten =
      xs.extract (k * s) ((k + 1) * s) by simp]
    rw [Array.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
      Nat.max_eq_right (Nat.mul_le_mul_right s (Nat.le_succ k))]

theorem ceil_mul_ge (n s : Nat) (pos : 0 < s) : n ≤ (n + s - 1) / s * s := by
  have split := Nat.div_add_mod (n + s - 1) s
  have small := Nat.mod_lt (n + s - 1) pos
  generalize (n + s - 1) / s = q at split ⊢
  generalize (n + s - 1) % s = r at split small
  rw [Nat.mul_comm] at split
  omega

/-- The computed chunk count and size cover every input element. -/
theorem chunks_cover (n w : Nat) (wpos : 0 < w) :
    n ≤ (if ((n + w - 1) / w == 0) = true then 0
      else (n + (n + w - 1) / w - 1) / ((n + w - 1) / w)) * ((n + w - 1) / w) := by
  by_cases zero : (n + w - 1) / w = 0
  · have := ceil_mul_ge n w wpos
    rw [zero, Nat.zero_mul] at this
    simp only [zero]
    omega
  · simp only [zero, beq_iff_eq, ite_false]
    exact ceil_mul_ge n _ (Nat.pos_of_ne_zero zero)

/-- Mapping covering slices and joining them is the original array map. -/
theorem slices_map {α β : Type} (f : α → β) (xs : Array α) (s k : Nat)
    (cover : xs.size ≤ k * s) :
    ((Array.range k).map fun c => (xs.extract (c * s) ((c + 1) * s)).map f).flatten = xs.map f := by
  have slices := slices_flatten xs s k
  rw [Array.extract_eq_self_of_le cover] at slices
  have mapped := congrArg (Array.map f) slices
  rw [Array.map_flatten, Array.map_map] at mapped
  simpa [Function.comp_def] using mapped

/-- Task evaluation preserves every value and its original position. -/
theorem map_eq {α β : Type} (width : Nat) (f : α → β) (xs : Array α) :
    map width f xs = xs.map f := by
  unfold map
  simp only [Array.map_map, Function.comp_def]
  exact slices_map _ xs _ _ (chunks_cover xs.size (max 1 width)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 width)))

end Ix.Compile.Parallel
