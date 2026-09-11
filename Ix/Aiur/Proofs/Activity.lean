/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Goldilocks

/-! Local arithmetic for the function and memory AIR's activity constraint.
The Rust constraint emitter uses `multiplicity * (1 - selector)` on every
function and memory circuit. This theorem rules out a nonzero return/pull
multiplicity on an inactive row. It is not the full AIR/execution reflection
theorem, nor a proof of the Rust field implementation or constraint emitter.
-/

namespace Aiur

theorem G.ofNat_n (a : G) : G.ofNat a.n = a := by
  have h : a.n < gSize.toNat := UInt64.lt_iff_toNat_lt.mp a.property
  simp only [G.ofNat, Nat.mod_eq_of_lt h, Nat.toUInt64, UInt64.ofNat_toNat]
  split
  · rfl
  · contradiction

theorem G.mul_one (a : G) : a * 1 = a := by
  change G.ofNat (a.n * (1 : G).n) = a
  have h : (1 : G).n = 1 := rfl
  rw [h, Nat.mul_one]
  exact G.ofNat_n a

theorem G.mul_zero (a : G) : a * 0 = 0 := by
  change G.ofNat (a.n * (0 : G).n) = 0
  have h : (0 : G).n = 0 := rfl
  rw [h, Nat.mul_zero]
  rfl

namespace AIR

/-- Exact polynomial appended by both the function and memory emitters. -/
def activityConstraint (multiplicity selector : G) : G :=
  multiplicity * (1 - selector)

theorem inactive_multiplicity_zero {multiplicity selector : G}
    (inactive : selector = 0) (satisfied : activityConstraint multiplicity selector = 0) :
    multiplicity = 0 := by
  subst selector
  have h : (1 : G) - 0 = 1 := by decide
  simpa only [activityConstraint, h, G.mul_one] using satisfied

theorem nonzero_multiplicity_active {multiplicity selector : G}
    (satisfied : activityConstraint multiplicity selector = 0)
    (nonzero : multiplicity ≠ 0) : selector ≠ 0 := by
  intro inactive
  exact nonzero (inactive_multiplicity_zero inactive satisfied)

theorem active_satisfies (multiplicity : G) : activityConstraint multiplicity 1 = 0 := by
  have h : (1 : G) - 1 = 0 := by decide
  simp only [activityConstraint, h, G.mul_zero]

end AIR
end Aiur
