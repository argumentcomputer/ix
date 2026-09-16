import Compilatrix.Aiur.AIR.Memory.Local

/-! The physical memory channel is one. Selected lookup arguments preserve
the full bucket, pointer and contents; the pull weight is minus multiplicity. -/

namespace Compilatrix.Aiur.AIR.Memory

open _root_.Aiur (G)

theorem eval_scale (window : Window) (expression : Expr) (constant value : G)
    (evaluated : expression.eval window = some value) :
    (scale expression constant).eval window = some (value * constant) := by
  unfold scale
  by_cases zero : constant = 0
  · simp only [zero, ↓reduceIte, Expr.eval, mul_zero]
  · by_cases one : constant = 1
    · simp only [one, G.one_ne_zero, ↓reduceIte, evaluated, mul_one]
    · simp [if_neg zero, if_neg one, Expr.eval, evaluated]

private theorem mapM_congr {α β : Type} (values : List α) (left right : α → Option β)
    (same : ∀ value ∈ values, left value = right value) : values.mapM left = values.mapM right := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    rw [List.mapM_cons, List.mapM_cons, same head List.mem_cons_self,
      ih (fun value member => same value (List.mem_cons_of_mem head member))]

private theorem mapM_get (values : List G) :
    (List.range values.length).mapM (fun index => values[index]?) = some values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp [List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Function.comp_def, ih]

theorem pull_weight (bucket : Nat) (row next : Row) (transition : Bool) :
    (pull bucket).multiplicity.eval (row.window next transition) = some (0 - row.multiplicity) := by
  simp [pull, Expr.eval, Row.window, Row.columns]

theorem pull_arguments (bucket : Nat) (row next : Row) (transition : Bool)
    (shape : row.values.length = bucket) (selected : row.selector = 1) :
    (pull bucket).arguments.mapM (Expr.eval (row.window next transition)) =
      some ([1, G.ofNat bucket, row.pointer] ++ row.values) := by
  have selectorEval : (Expr.main 1).eval (row.window next transition) = some 1 := by
    simp [Expr.eval, Row.window, Row.columns, selected]
  have scalar := eval_scale (row.window next transition) (.main 1) (G.ofNat bucket) 1 selectorEval
  rw [one_mul] at scalar
  have payload : ((List.range bucket).map (fun i => Expr.mul (.main 1) (.main (3 + i)))).mapM
      (Expr.eval (row.window next transition)) = some row.values := by
    rw [List.mapM_map]
    calc
      _ = (List.range bucket).mapM (fun i => row.values[i]?) := by
        apply mapM_congr
        intro i _
        simp only [Function.comp_def, Expr.eval, Row.window, Row.columns,
          List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
        rw [selected]
        cases found : row.values[i]? <;>
          simp [Nat.add_comm 3 i, found, one_mul]
      _ = some row.values := by rw [← shape]; exact mapM_get row.values
  simp only [pull, List.mapM_append, List.mapM_cons, List.mapM_nil, selectorEval, scalar,
    payload]
  simp [Expr.eval, Row.window, Row.columns, selected, one_mul]

end Compilatrix.Aiur.AIR.Memory
