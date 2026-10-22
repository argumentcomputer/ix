import Aiur.Optimized.PolynomialFacts
import Mathlib.Algebra.BigOperators.Field

namespace Aiur.Optimized

variable {F : Type} [Field F]

/-- The value of the failure certificate emitted for a conjunction. -/
def combination : List F → List F → F
  | d :: ds, u :: us => d * u + combination ds us
  | _, _ => 0

theorem combination_zero_left {differences : List F}
    (zero : ∀ d ∈ differences, d = 0) (coefficients : List F) : combination differences coefficients = 0 := by
  induction differences generalizing coefficients with
  | nil => rfl
  | cons d ds ih =>
      cases coefficients <;> simp_all [combination]

theorem combination_zero_right (differences : List F) :
    combination differences (List.replicate differences.length 0) = 0 := by
  induction differences <;> simp_all [List.replicate_succ, combination]

/-- A failed conjunction is witnessed by one inverse coefficient. This proof
does not assume a finite field or any bound on the number of conditions. -/
theorem failure_certificate_iff (differences : List F) :
    (∃ coefficients, coefficients.length = differences.length ∧ combination differences coefficients = 1) ↔
      ¬ (∀ d ∈ differences, d = 0) := by
  classical
  constructor
  · rintro ⟨coefficients, _, equation⟩ allZero
    rw [combination_zero_left allZero] at equation
    exact zero_ne_one equation
  · intro fails
    induction differences with
    | nil => simp at fails
    | cons d ds ih =>
        by_cases zero : d = 0
        · obtain ⟨coefficients, length, equation⟩ := ih (by simpa [zero] using fails)
          exact ⟨0 :: coefficients, by simp [length], by simp [combination, zero, equation]⟩
        · exact ⟨d⁻¹ :: List.replicate ds.length 0, by simp,
            by simp [combination, zero, combination_zero_right]⟩

theorem guarded_failure_iff (enable : F) (differences : List F) :
    (∃ coefficients, coefficients.length = differences.length ∧
      enable * (combination differences coefficients - 1) = 0) ↔
      (enable = 0 ∨ ¬ (∀ d ∈ differences, d = 0)) := by
  classical
  constructor
  · rintro ⟨coefficients, length, equation⟩
    rcases mul_eq_zero.mp equation with inactive | failed
    · exact Or.inl inactive
    · exact Or.inr ((failure_certificate_iff differences).mp
        ⟨coefficients, length, sub_eq_zero.mp failed⟩)
  · rintro (inactive | failed)
    · exact ⟨List.replicate differences.length 0, by simp, by simp [inactive]⟩
    · obtain ⟨coefficients, length, equation⟩ := (failure_certificate_iff differences).mpr failed
      exact ⟨coefficients, length, by simp [equation]⟩

theorem selector_boolean (value : F) : value * (value - 1) = 0 ↔ value = 0 ∨ value = 1 := by
  simp only [mul_eq_zero, sub_eq_zero]

variable {I : Type} [Fintype I]

theorem exclusive_sum (selectors : I → F)
    (exclusive : ∀ i j, i ≠ j → selectors i * selectors j = 0) {i : I}
    (active : selectors i ≠ 0) : ∑ j, selectors j = selectors i := by
  classical
  apply Finset.sum_eq_single i
  · intro j _ different
    exact (mul_eq_zero.mp (exclusive i j different.symm)).resolve_left active
  · simp

/-- Exclusive Boolean children have a Boolean sum in every characteristic.
Their sum can therefore define the parent's activation. -/
theorem selector_sum_boolean (selectors : I → F)
    (boolean : ∀ i, selectors i * (selectors i - 1) = 0)
    (exclusive : ∀ i j, i ≠ j → selectors i * selectors j = 0) :
    (∑ i, selectors i) * ((∑ i, selectors i) - 1) = 0 := by
  classical
  by_cases zero : ∀ i, selectors i = 0
  · simp [zero]
  · obtain ⟨i, active⟩ := not_forall.mp zero
    rw [exclusive_sum selectors exclusive active]
    exact boolean i

/-- Coverage selects exactly one child when the parent is active. Repeated
branches cannot wrap a finite field's characteristic because of exclusion. -/
theorem selector_exactly_one (selectors : I → F)
    (boolean : ∀ i, selectors i * (selectors i - 1) = 0)
    (exclusive : ∀ i j, i ≠ j → selectors i * selectors j = 0)
    (coverage : ∑ i, selectors i = 1) : ∃! i, selectors i = 1 := by
  classical
  have nonzero : ∃ i, selectors i ≠ 0 := by
    by_contra! absent
    simp [absent] at coverage
  obtain ⟨i, active⟩ := nonzero
  have one : selectors i = 1 := ((selector_boolean _).mp (boolean i)).resolve_left active
  refine ⟨i, one, ?_⟩
  intro j selected
  by_contra different
  have zero := exclusive i j (Ne.symm different)
  simp [one, selected] at zero

theorem selector_inactive (selectors : I → F)
    (exclusive : ∀ i j, i ≠ j → selectors i * selectors j = 0)
    (coverage : ∑ i, selectors i = 0) : ∀ i, selectors i = 0 := by
  intro i
  by_contra active
  exact active ((exclusive_sum selectors exclusive active).symm.trans coverage)

end Aiur.Optimized
