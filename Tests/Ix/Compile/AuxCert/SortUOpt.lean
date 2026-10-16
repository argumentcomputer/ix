/-! H1 from Lean source: `bootstrap.inductiveCheckResultingUniverse false`
admits a `Sort u` inductive that may be Prop; Lean's kernel gives it a
Prop-only recursor, aux-gen forces large elimination (recursor.rs:2520). -/
namespace SortUOpt
set_option bootstrap.inductiveCheckResultingUniverse false in
inductive SU : Sort u
  | a
  | b

theorem su_cases (x : SU.{u}) : x = SU.a ∨ x = SU.b := by
  cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive SR : Sort u
  | leaf
  | node : SR → SR

theorem sr_triv (x : SR.{u}) : True := by
  cases x <;> trivial
end SortUOpt
