import Aiur.Scalar.Circuit.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Aiur.Scalar.Circuit

/-- Values satisfying the Boolean, pairwise exclusion, and sum selector equations. -/
structure SelectorsValid [Field F] (parent : F) (selectors : List F) : Prop where
  boolean : ∀ selector ∈ selectors, selector * (selector - 1) = 0
  exclusive : selectors.Pairwise (fun left right => left * right = 0)
  sum : selectors.sum = parent

/-- Adding a disabled branch preserves all selector equations. -/
theorem SelectorsValid.zero_cons [Field F] {parent : F} {selectors : List F}
    (valid : SelectorsValid parent selectors) : SelectorsValid parent (0 :: selectors) := by
  refine ⟨?_, List.pairwise_cons.mpr ⟨by simp, valid.exclusive⟩, by simpa using valid.sum⟩
  intro selector member
  rcases List.mem_cons.mp member with rfl | member
  · simp
  · exact valid.boolean selector member

/-- All-zero selectors supply a witness for an inactive match. -/
theorem SelectorsValid.zeros [Field F] {selectors : List F}
    (zeros : ∀ selector ∈ selectors, selector = 0) : SelectorsValid (0 : F) selectors := by
  induction selectors with
  | nil => exact ⟨by simp, by simp, rfl⟩
  | cons head tail ih =>
      have headZero := zeros head (by simp)
      subst head
      exact (ih (fun selector member => zeros selector (by simp [member]))).zero_cons

/-- A chosen branch and zeroes elsewhere supply a witness for an active match. -/
theorem SelectorsValid.single [Field F] {before after : List F}
    (beforeZero : ∀ selector ∈ before, selector = 0)
    (afterZero : ∀ selector ∈ after, selector = 0) :
    SelectorsValid (1 : F) (before ++ 1 :: after) := by
  induction before with
  | nil =>
      have tail := SelectorsValid.zeros afterZero
      refine ⟨?_, List.pairwise_cons.mpr ⟨by simpa using afterZero, tail.exclusive⟩, ?_⟩
      · intro selector member
        rcases List.mem_cons.mp member with rfl | member
        · simp
        · exact tail.boolean selector member
      · simp [tail.sum]
  | cons head tail ih =>
      have headZero := beforeZero head (by simp)
      subst head
      exact (ih (fun selector member => beforeZero selector (by simp [member]))).zero_cons

/-- An inactive match forces every selector to zero, in any field characteristic. -/
theorem SelectorsValid.inactive [Field F] {selectors : List F}
    (valid : SelectorsValid (0 : F) selectors) : ∀ selector ∈ selectors, selector = 0 := by
  induction selectors with
  | nil => simp
  | cons head tail ih =>
      obtain ⟨pairs, exclusive⟩ := List.pairwise_cons.mp valid.exclusive
      rcases selector_boolean (valid.boolean head (by simp)) with zero | one
      · subst head
        have tailValid : SelectorsValid (0 : F) tail := {
          boolean := fun value member => valid.boolean value (by simp [member])
          exclusive
          sum := by simpa using valid.sum
        }
        intro value member
        rcases List.mem_cons.mp member with zero | member
        · exact zero
        · exact ih tailValid value member
      · subst head
        have zeros : ∀ value ∈ tail, value = 0 := by simpa using pairs
        have tailSum : tail.sum = 0 := List.sum_eq_zero zeros
        have impossible := valid.sum
        simp [tailSum] at impossible

/-- An active match has exactly one selected occurrence; all other selectors are zero. -/
theorem SelectorsValid.active [Field F] {selectors : List F}
    (valid : SelectorsValid (1 : F) selectors) :
    ∃ before after, selectors = before ++ 1 :: after ∧
      (∀ selector ∈ before, selector = 0) ∧ (∀ selector ∈ after, selector = 0) := by
  induction selectors with
  | nil => simpa using valid.sum
  | cons head tail ih =>
      obtain ⟨pairs, exclusive⟩ := List.pairwise_cons.mp valid.exclusive
      rcases selector_boolean (valid.boolean head (by simp)) with zero | one
      · subst head
        have tailValid : SelectorsValid (1 : F) tail := {
          boolean := fun value member => valid.boolean value (by simp [member])
          exclusive
          sum := by simpa using valid.sum
        }
        obtain ⟨before, after, shape, beforeZero, afterZero⟩ := ih tailValid
        refine ⟨0 :: before, after, by simp [shape], ?_, afterZero⟩
        intro selector member
        rcases List.mem_cons.mp member with zero | member
        · exact zero
        · exact beforeZero selector member
      · subst head
        exact ⟨[], tail, rfl, by simp, by simpa using pairs⟩

/-- A selected default branch excludes every literal guarded by an inverse equation. -/
theorem default_excludes_literal [Field F] {value pattern inverse : F}
    (equation : (value - pattern) * inverse - 1 = 0) : value ≠ pattern := by
  intro same
  have nonzero := inverse_nonzero equation
  exact nonzero (sub_eq_zero.mpr same)

end Aiur.Scalar.Circuit
