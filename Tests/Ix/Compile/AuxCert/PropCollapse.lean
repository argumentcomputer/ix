/-! Collapsed Prop mutual pair (the Canonicity.lean PropCollapseA fixture
shape): the non-representative's `.below.casesOn` (seam audit H1; the
nestedprop fix says it fixes this) plus a user `cases` (recursor universe). -/
namespace PropCollapse
mutual
inductive P : Nat → Prop
  | step : ∀ n, Q n → P n
inductive Q : Nat → Prop
  | step : ∀ n, P n → Q n
end

theorem p_cases (h : P 0) : Q 0 := by
  cases h with
  | step q => exact q
end PropCollapse
