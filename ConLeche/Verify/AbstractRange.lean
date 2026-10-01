module

public import ConLeche.Verify.Shift

public section

/-!
# Bulk abstraction equals the `abstract1` fold (task #72)

`Expr.abstractRange` closes a contiguous fvar-level range in one
traversal; `abstractRange_succ` identifies it with the innermost-first
`abstract1` chain a telescope rebuild folds over (see
`ConLeche/Verify/BinderLoop.lean`), and `abstractRange_zero` is the empty
range.  Kept below `ConLeche/Verify/IExpr.lean` in the import DAG: the
interned `abstractRangeIGo` spec consumes these.
-/

namespace ConLeche

open Expr

/-- An empty range abstracts nothing. -/
theorem abstractRange_zero : ∀ (e : Expr) (d c : Nat),
    e.abstractRange d 0 c = e := by
  intro e
  induction e <;> intro d c <;>
    simp_all [Expr.abstractRange] <;> omega

/-- Peeling the innermost binder off a bulk abstraction: one
`abstract1` at the top of the range, then the shorter range one cursor
deeper — the fold `abstractRange` implements in one pass. -/
theorem abstractRange_succ :
    ∀ (e : Expr) (d k c : Nat),
      e.abstractRange d (k + 1) c
        = (e.abstract1 (d + k) c).abstractRange d k (c + 1) := by
  intro e
  induction e with
  | fvar idx ty _ih =>
    intro d k c
    by_cases htop : idx = d + k
    · subst htop
      simp only [Expr.abstractRange, Expr.abstract1]
      have : d ≤ d + k ∧ d + k < d + (k + 1) := by omega
      simp [this, Expr.abstractRange]
    · by_cases hin : d ≤ idx ∧ idx < d + k
      · have hin1 : d ≤ idx ∧ idx < d + (k + 1) := by omega
        simp only [Expr.abstractRange, Expr.abstract1, if_neg htop,
          if_pos hin, if_pos hin1]
        congr 1
        omega
      · have hout : ¬ (d ≤ idx ∧ idx < d + (k + 1)) := by omega
        simp [Expr.abstractRange, Expr.abstract1, htop, hin, hout]
  | _ =>
    intro d k c <;>
    simp_all [Expr.abstractRange, Expr.abstract1]

/-- Abstracting a range at or above a term's fvar range is the
identity (the fvar-range cutoff of the interned traversal, task #86;
`Expr.fvarsBelow` is the annotation-free fvar bound of
`ConLeche/Verify/Shift.lean`). -/
theorem abstractRange_eq_self : ∀ {e : Expr} {d k c : Nat},
    e.fvarsBelow d → e.abstractRange d k c = e := by
  intro e
  induction e <;> intro d k c hb <;>
    simp_all only [Expr.fvarsBelow, Expr.abstractRange]
  rw [if_neg (by omega)]

end ConLeche
