import IxCC.Aiur.AIR.Memory.Model

/-! Local polynomial extraction for the exact pinned field representation.
No primality or no-zero-divisors axiom is used. -/

namespace IxCC.Aiur.AIR.Memory

open _root_.IxCC.Vendor.Aiur (G gSize)

theorem mul_one (a : G) : a * 1 = a := by
  apply Field.ext
  change (G.ofNat (a.n * (1 : G).n)).n = a.n
  rw [G.ofNat_n]
  have one : (1 : G).n = 1 := rfl
  simp only [one, Nat.mul_one, Nat.mod_eq_of_lt (Field.value_lt a)]

theorem one_mul (a : G) : (1 : G) * a = a := by
  rw [G.mul_comm, mul_one]

theorem mul_zero (a : G) : a * 0 = 0 := by
  change G.ofNat (a.n * 0) = G.ofNat 0
  rw [Nat.mul_zero]

theorem sub_eq_zero {a b : G} (equal : a - b = 0) : a = b := by
  apply Field.ext
  have ha := Field.value_lt a
  have hb := Field.value_lt b
  have h := congrArg G.n equal
  rw [G.sub_n, Field.zero_value] at h
  by_cases large : gSize.toNat ≤ a.n + gSize.toNat - b.n
  · rw [Nat.mod_eq_sub_mod large,
      Nat.mod_eq_of_lt (show a.n + gSize.toNat - b.n - gSize.toNat < gSize.toNat by omega)] at h
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

theorem satisfied_iff (bucket : Nat) (row next : Row) (transition : Bool) :
    (build bucket).Satisfied (row.window next transition) ↔ row.Equations next transition := by
  simp [Circuit.Satisfied, build, Expr.eval, Row.window, Row.columns, Row.Equations]

theorem selected_predecessor {row next : Row}
    (satisfied : row.Equations next true) (selected : next.selector = 1) :
    row.selector = 1 ∧ next.pointer = row.pointer + 1 := by
  rcases satisfied with ⟨_, _, initial, step⟩
  simp only [selected, ↓reduceIte, mul_one, one_mul] at initial step
  exact ⟨sub_eq_zero initial, (sub_eq_zero step).symm⟩

theorem row_activity {row next : Row} {transition : Bool}
    (satisfied : row.Equations next transition)
    (boolean : row.selector = 0 ∨ row.selector = 1)
    (nonzero : row.multiplicity ≠ 0) : row.active = true := by
  rcases boolean with zero | one
  · have h := satisfied.2.1
    rw [zero] at h
    have difference : (1 : G) - 0 = 1 := by decide
    rw [difference, mul_one] at h
    exact False.elim (nonzero h)
  · simp [Row.active, one]

end IxCC.Aiur.AIR.Memory
