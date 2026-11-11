import Aiur.Library.U32
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

/-! Explicit field selection for the IxVM word implementation. The host hints
and source assertions remain ordinary Aiur operations. Other fields can select
another implementation at this module boundary without changing the compiler.
The current implementation only needs the weaker `U32.Compatible` bound. -/
namespace Aiur.Library.U32.Goldilocks

abbrev modulus := 18446744069414584321
abbrev F := ZMod modulus

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem modulus_prime : Nat.Prime modulus := by
  apply lucas_primality modulus (7 : F)
  · reduce_mod_char
  · intro q hq hd
    have factors : modulus - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

theorem compatible : U32.Compatible F := U32.compatible_of_charP F modulus (by decide)

def program : Modules.Program F := U32.program F compatible

end Aiur.Library.U32.Goldilocks
