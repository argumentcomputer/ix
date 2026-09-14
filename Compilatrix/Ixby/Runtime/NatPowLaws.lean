import Compilatrix.Ixby.Runtime.ConversionLaws

/-! Source arithmetic and intermediate bounds for the emitted repeated
squaring loop. The loop squares only when the halved exponent is nonzero. -/

namespace Compilatrix.Ixby.Runtime.NatLoops

theorem pow_halving (base exponent : Nat) :
    base ^ exponent = (base * base) ^ (exponent / 2) * base ^ (exponent % 2) := by
  calc
    base ^ exponent = base ^ (2 * (exponent / 2) + exponent % 2) := by
      congr 1; omega
    _ = (base * base) ^ (exponent / 2) * base ^ (exponent % 2) := by
      rw [Nat.pow_add, Nat.pow_mul]
      simp [Nat.pow_succ]

theorem pow_even (base exponent : Nat) (even : exponent % 2 = 0) :
    (base * base) ^ (exponent / 2) = base ^ exponent := by
  rw [pow_halving base exponent, even, Nat.pow_zero, Nat.mul_one]

theorem pow_odd (base exponent accumulator : Nat) (odd : exponent % 2 = 1) :
    (accumulator * base) * (base * base) ^ (exponent / 2) = accumulator * base ^ exponent := by
  rw [pow_halving base exponent, odd, Nat.pow_one]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem pow_half_le (base exponent : Nat) (remaining : 0 < exponent / 2) :
    (base * base) ^ (exponent / 2) ≤ base ^ exponent := by
  by_cases zero : base = 0
  · subst base
    simp [Nat.zero_pow remaining]
  · rw [pow_halving base exponent]
    exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))

theorem pow_square_le (base exponent : Nat) (remaining : 0 < exponent / 2) :
    base * base ≤ base ^ exponent :=
  Nat.le_trans (Nat.le_pow remaining) (pow_half_le base exponent remaining)

theorem pow_accumulator_le (base exponent accumulator : Nat) (positive : 0 < exponent) :
    accumulator * base ≤ accumulator * base ^ exponent :=
  Nat.mul_le_mul_left accumulator (Nat.le_pow positive)

end Compilatrix.Ixby.Runtime.NatLoops
