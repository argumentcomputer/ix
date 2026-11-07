import IxCC.Rt.Rc.Layout
import IxCC.Rt.Proof.Words

namespace IxCC.Rt.Rc.Procs
open Lir

theorem truncate32_toNat (word : Word) :
    (X86.Width.w32.truncate word).toNat = word.toNat % 2^32 := by
  simp only [X86.Width.truncate, X86.Width.mask, UInt64.toNat_and]
  rw [show (UInt64.toNat 0xffffffff) = 2^32-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The machine add followed by the actual 32-bit store represents one more
logical reference. Input is the count-minus-one live-header invariant. -/
theorem increment_count {refs : Nat} {count : Word}
    (hpositive : 0 < refs) (hroom : refs < maxCount)
    (hcount : count.toNat = refs-1) :
    (X86.Width.w32.truncate (count+1)).toNat = (refs+1)-1 := by
  rw [truncate32_toNat, UInt64.toNat_add, hcount]
  change ((refs-1+1) % 2^64) % 2^32 = (refs+1)-1
  unfold maxCount at hroom
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- Shared decrement retains a positive logical count and writes its exact
count-minus-one encoding. No modular underflow is hidden in this equation. -/
theorem shared_decrement_count {refs : Nat} {count : Word}
    (hshared : 1 < refs) (hbounded : refs ≤ maxCount)
    (hcount : count.toNat = refs-1) :
    (X86.Width.w32.truncate (count-1)).toNat = (refs-1)-1 := by
  rw [truncate32_toNat, IxCC.Rt.Proof.sub_toNat_of_le (by simp; omega), hcount]
  change (refs-1-1) % 2^32 = (refs-1)-1
  unfold maxCount at hbounded
  exact Nat.mod_eq_of_lt (by omega)



end IxCC.Rt.Rc.Procs
