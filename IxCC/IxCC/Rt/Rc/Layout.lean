import IxCC.Rt.Layout

/-! Dynamic RC headers extend the existing runtime layout. The abstract heap
stores the number of references; the runtime stores one less. These encodings
preserve the immortal layout and do not establish heap liveness by themselves. -/

namespace IxCC.Rt.Rc

open IxCC.Lir (Word)

/-- Largest abstract count representable by a nonnegative signed rc field. -/
def maxCount : Nat := 2 ^ 31

/-- The physical header of a live dynamic constructor. Callers establish
positive bounded `refs` and a valid class; this is not an admission check. -/
def dynamicHeader (scan cls tag refs : Nat) : Word :=
  header scan cls tag (refs - 1)

/-- A small allocation includes its header word. -/
def smallClass (fields : Nat) : Nat := fields + 1

theorem header_toNat {scan cls tag rc : Nat}
    (hs : scan < 256) (hc : cls < 256) (ht : tag < 65536) (hr : rc < 2 ^ 32) :
    (header scan cls tag rc).toNat = scan + 256 * cls + 65536 * tag + 2 ^ 32 * rc := by
  unfold header headerLow
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  omega

theorem header_scan {scan cls tag rc : Nat}
    (hs : scan < 256) (hc : cls < 256) (ht : tag < 65536) (hr : rc < 2 ^ 32) :
    ((header scan cls tag rc) &&& 0xFF).toNat = scan := by
  rw [UInt64.toNat_and, header_toNat hs hc ht hr]
  rw [show (UInt64.toNat 0xFF) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem header_class {scan cls tag rc : Nat}
    (hs : scan < 256) (hc : cls < 256) (ht : tag < 65536) (hr : rc < 2 ^ 32) :
    (((header scan cls tag rc) >>> 8) &&& 0xFF).toNat = cls := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, header_toNat hs hc ht hr]
  rw [show (UInt64.toNat 0xFF) = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  simp
  omega

theorem header_tag {scan cls tag rc : Nat}
    (hs : scan < 256) (hc : cls < 256) (ht : tag < 65536) (hr : rc < 2 ^ 32) :
    (((header scan cls tag rc) >>> 16) &&& 0xFFFF).toNat = tag := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, header_toNat hs hc ht hr]
  rw [show (UInt64.toNat 0xFFFF) = 2 ^ 16 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  simp
  omega

theorem header_rc {scan cls tag rc : Nat}
    (hs : scan < 256) (hc : cls < 256) (ht : tag < 65536) (hr : rc < 2 ^ 32) :
    ((header scan cls tag rc) >>> 32).toNat = rc := by
  rw [UInt64.toNat_shiftRight, header_toNat hs hc ht hr, Nat.shiftRight_eq_div_pow]
  simp
  omega

theorem dynamicHeader_count {scan cls tag refs : Nat}
    (hs : scan < 256) (hc : cls < 256) (ht : tag < 65536)
    (hpos : 0 < refs) (hmax : refs ≤ maxCount) :
    ((dynamicHeader scan cls tag refs) >>> 32).toNat + 1 = refs := by
  unfold dynamicHeader
  rw [header_rc hs hc ht]
  · omega
  · unfold maxCount at hmax
    omega

theorem dynamicHeader_unique {scan cls tag : Nat} :
    dynamicHeader scan cls tag 1 = header scan cls tag 0 := by
  rfl

theorem smallClass_bounds {fields : Nat} (hf : fields < 32) :
    1 ≤ smallClass fields ∧ smallClass fields ≤ 32 := by
  unfold smallClass
  omega

theorem smallClass_bytes (fields : Nat) :
    8 * smallClass fields = cellBytes fields := by
  simp [smallClass, cellBytes, Nat.add_comm]

end IxCC.Rt.Rc
