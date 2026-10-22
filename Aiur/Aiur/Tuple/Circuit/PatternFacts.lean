import Aiur.Tuple.Circuit.Basic

namespace Aiur.Tuple.Circuit

/-- The equality-test equations determine the indicator in every field. -/
theorem equality_indicator_sound [Field F] [DecidableEq F] {difference equal inverse : F}
    (zero : difference * equal = 0)
    (inverseEquation : difference * inverse - (1 - equal) = 0) :
    equal = if difference = 0 then 1 else 0 := by
  by_cases same : difference = 0
  · simp only [same, zero_mul, zero_sub, neg_eq_zero] at inverseEquation
    simpa [same] using (sub_eq_zero.mp inverseEquation).symm
  · simpa [same] using (mul_eq_zero.mp zero).resolve_left same

/-- Every field difference has witnesses for the emitted equality-test equations. -/
theorem equality_indicator_complete [Field F] [DecidableEq F] (difference : F) :
    let equal : F := if difference = 0 then 1 else 0
    equal * (equal - 1) = 0 ∧ difference * equal = 0 ∧
      difference * difference⁻¹ - (1 - equal) = 0 := by
  by_cases same : difference = 0 <;> simp [same]

end Aiur.Tuple.Circuit
