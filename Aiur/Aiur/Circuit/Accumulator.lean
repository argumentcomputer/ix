import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Perm.Basic

namespace Aiur.Circuit

/-- A finite ledger of signed changes. Its value is the sum at each claim,
not the length of the ledger. Negative intermediate balances are permitted. -/
abbrev Accumulator (α : Type) := List (α × Int)

namespace Accumulator

def value [DecidableEq α] (entries : Accumulator α) (claim : α) : Int :=
  (entries.map fun entry => if entry.1 = claim then entry.2 else 0).sum

def isZero [DecidableEq α] (entries : Accumulator α) : Bool :=
  entries.all fun entry => decide (value entries entry.1 = 0)

@[simp] theorem value_nil [DecidableEq α] (claim : α) : value [] claim = 0 := rfl

@[simp] theorem value_cons [DecidableEq α] (entry : α × Int) (entries : Accumulator α) (claim : α) :
    value (entry :: entries) claim = (if entry.1 = claim then entry.2 else 0) + value entries claim := by
  simp [value]

@[simp] theorem value_append [DecidableEq α] (xs ys : Accumulator α) (claim : α) :
    value (xs ++ ys) claim = value xs claim + value ys claim := by simp [value]

theorem value_of_absent [DecidableEq α] {entries : Accumulator α} {claim : α}
    (absent : ∀ entry ∈ entries, entry.1 ≠ claim) : value entries claim = 0 := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp [absent entry (by simp), ih (fun next h => absent next (by simp [h]))]

theorem isZero_iff [DecidableEq α] (entries : Accumulator α) :
    entries.isZero = true ↔ ∀ claim, entries.value claim = 0 := by
  simp only [isZero, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro zero claim
    by_cases present : ∃ entry ∈ entries, entry.1 = claim
    · obtain ⟨entry, member, rfl⟩ := present
      exact zero entry member
    · exact value_of_absent (fun entry member same => present ⟨entry, member, same⟩)
  · intro zero entry _; exact zero entry.1

/-- Add one occurrence of each requirement. -/
def requires (claims : List α) : Accumulator α := claims.map (fun claim => (claim, 1))

/-- A provide subtracts its integer weight; requirements are never scaled. -/
def provides (claims : List (α × Int)) : Accumulator α := claims.map (fun entry => (entry.1, -entry.2))

@[simp] theorem value_requires [DecidableEq α] (claims : List α) (claim : α) :
    value (requires claims) claim = (claims.count claim : Int) := by
  induction claims with
  | nil => rfl
  | cons head tail ih =>
      change value ((head, 1) :: requires tail) claim = _
      rw [value_cons, ih]
      by_cases same : head = claim <;> simp [same, eq_comm, Int.add_comm]

@[simp] theorem value_provides [DecidableEq α] (claims : List (α × Int)) (claim : α) :
    value (provides claims) claim = -value claims claim := by
  induction claims with
  | nil => simp [provides]
  | cons head tail ih =>
      change value ((head.1, -head.2) :: provides tail) claim = _
      rw [value_cons, value_cons, ih]
      by_cases same : head.1 = claim <;> simp [same, neg_add_rev, Int.add_comm]

/-- Exact integer balance with unit provides is exactly multiset equality. -/
theorem unit_balance_iff [DecidableEq α] (required provided : List α) :
    (requires required ++ provides (requires provided)).isZero = true ↔ required.Perm provided := by
  rw [isZero_iff, List.perm_iff_count]
  simp only [value_append, value_requires, value_provides]
  constructor
  · intro balanced claim
    have := balanced claim
    omega
  · intro balanced claim
    rw [balanced claim]
    omega

end Accumulator
end Aiur.Circuit
