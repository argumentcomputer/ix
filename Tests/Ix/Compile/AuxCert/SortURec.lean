/-! H1b: a recursive inductive in `Sort u` with two constructors (Prop-only
eliminator, but not a Prop former, so Lean runs the Type-level `mkBelow`). -/
namespace SortURec
inductive SR : Sort u
  | leaf
  | node : SR → SR

theorem sr_triv (x : SR.{u}) : True := by
  induction x <;> trivial
end SortURec
