import IxCC.Vendor.Ix.Aiur.Goldilocks

/-! Small algebraic bridges for the exact pinned field representation. No
abstract field-law instance or primality axiom is assumed. -/

namespace IxCC.Aiur.Field

open _root_.IxCC.Vendor.Aiur

theorem ext {a b : G} (h : a.n = b.n) : a = b := by
  apply Subtype.ext
  exact UInt64.toNat_inj.mp h

theorem value_lt (a : G) : a.n < gSize.toNat := by
  simpa only [G.n, UInt64.lt_iff_toNat_lt] using a.property

@[simp] theorem zero_value : (0 : G).n = 0 := by decide

@[simp] theorem zero_add (a : G) : (0 : G) + a = a := by
  apply ext
  simp [G.add_n, Nat.mod_eq_of_lt (value_lt a)]

@[simp] theorem add_zero (a : G) : a + (0 : G) = a := by
  rw [G.add_comm, zero_add]

theorem ofNat_ne_zero {n : Nat} (positive : 0 < n) (bound : n < gSize.toNat) :
    G.ofNat n ≠ (0 : G) := by
  intro equal
  have := congrArg G.n equal
  simp only [G.ofNat_n, Nat.mod_eq_of_lt bound, zero_value] at this
  omega

end IxCC.Aiur.Field
