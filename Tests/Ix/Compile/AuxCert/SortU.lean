/-! H1: an inductive in `Sort u` (not provably non-zero) with two constructors.
Lean's kernel gives it a recursor that eliminates only into Prop
(`elim_only_at_universe_zero`), so `SU.rec` has no extra universe parameter.
aux-gen's `compute_is_large_and_k` overrides `is_large := true` whenever the
result level is not literally zero (recursor.rs:2520, Recursor.lean:1632). -/
namespace SortU
inductive SU : Sort u
  | a
  | b

theorem su_cases (x : SU.{u}) : x = SU.a ∨ x = SU.b := by
  cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- One constructor with a non-Prop field not in the indices: also Prop-only. -/
inductive SW : Sort u
  | mk : Nat → SW

theorem sw_nat (x : SW.{u}) : ∃ n, x = SW.mk n := by
  cases x with
  | mk n => exact ⟨n, rfl⟩
end SortU
