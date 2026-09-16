import Compilatrix.Aiur.Field

/-! The elementary ring identities needed by the pinned affine analyzer.
All proofs use the exact Goldilocks representation; no field instance or
primality assumption is introduced. -/

namespace Compilatrix.Aiur.CounterAnalysis

open _root_.Aiur (G gSize)

theorem add_assoc (a b c : G) : (a + b) + c = a + (b + c) := by
  apply Field.ext
  simp only [G.add_n]
  simp only [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem mul_one (a : G) : a * 1 = a := by
  apply Field.ext
  change (G.ofNat (a.n * (1 : G).n)).n = a.n
  rw [G.ofNat_n]
  have one : (1 : G).n = 1 := rfl
  simp only [one, Nat.mul_one, Nat.mod_eq_of_lt (Field.value_lt a)]

theorem one_mul (a : G) : (1 : G) * a = a := by
  rw [G.mul_comm, mul_one]

theorem sub_eq_add_neg (a b : G) : a - b = a + (0 - b) := by
  apply Field.ext
  rw [G.sub_n, G.add_n, G.sub_n, Field.zero_value, Nat.zero_add]
  rw [Nat.add_mod_mod]
  have bound := Field.value_lt b
  congr 1
  omega

theorem add_sub_assoc (a b c : G) : (a + b) - c = a + (b - c) := by
  rw [sub_eq_add_neg, sub_eq_add_neg b c, add_assoc]

end Compilatrix.Aiur.CounterAnalysis
