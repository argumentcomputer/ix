import IxCC.Aiur.AIR.Rank.Graph
import IxCC.Aiur.AIR.Memory.Local

/-! Selected rank expressions and complete physical messages. Missing
columns continue to fail evaluation, including within a selected gate. -/

namespace IxCC.Aiur.AIR.Rank

open _root_.Aiur (G)

theorem pack_eval (window : Window) (low middle high : Expr) (limbs : Limbs)
    (hl : low.eval window = some limbs.low) (hm : middle.eval window = some limbs.middle)
    (hh : high.eval window = some limbs.high) :
    (pack low middle high).eval window = some limbs.packed := by
  simp [pack, Expr.eval, hl, hm, hh, Limbs.packed]

theorem orderedExpr_eval (window : Window) (parent gap : Expr) (p g : Limbs)
    (hp : parent.eval window = some p.packed) (hg : gap.eval window = some g.packed) :
    (orderedExpr parent gap).eval window = some (ordered p g) := by
  simp [orderedExpr, Expr.eval, hp, hg, ordered]

theorem callExpr_eval (window : Window) (mode : CallMode) (parent gap boundary : Expr)
    (p g : Limbs) (b : G) (hp : parent.eval window = some p.packed)
    (hg : gap.eval window = some g.packed) (hb : boundary.eval window = some b) :
    (callExpr mode parent gap boundary).eval window = some (callValue mode p g b) := by
  cases mode <;> simp [callExpr, callValue, orderedExpr, Expr.eval, hp, hg, hb, ordered]

theorem gate_eval (window : Window) (branchless : Bool) (selector argument : Expr)
    (selected : selector.eval window = some 1) :
    (gate branchless selector argument).eval window = argument.eval window := by
  cases branchless with
  | true => rfl
  | false =>
    cases argument with
    | constant value =>
      by_cases zero : value = 0
      · simp [gate, zero, Expr.eval]
      · by_cases one : value = 1
        · simp [gate, one, Expr.eval, selected, G.one_ne_zero]
        · simp [gate, zero, one, Expr.eval, selected, Memory.one_mul]
    | main column | next column | preprocessed column =>
      simp only [gate, Bool.false_eq_true, ↓reduceIte, Expr.eval, selected]
      simp [Option.bind_eq_bind, Memory.one_mul]
    | transition => simp [gate, Expr.eval, selected, Memory.one_mul]
    | add left right | sub left right | mul left right | neg left =>
      simp only [gate, Bool.false_eq_true, ↓reduceIte, Expr.eval, selected]
      simp [Option.bind_eq_bind, Memory.one_mul]

theorem gate_list_eval (window : Window) (branchless : Bool) (selector : Expr)
    (selected : selector.eval window = some 1) (arguments : List Expr) :
    (arguments.map (gate branchless selector)).mapM (Expr.eval window) =
      arguments.mapM (Expr.eval window) := by
  induction arguments with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, List.mapM_cons, gate_eval _ _ _ _ selected, ih]

theorem rangePush_arguments (window : Window) (branchless : Bool) (selector limb : Expr) (value : G)
    (selected : selector.eval window = some 1) (evaluated : limb.eval window = some value) :
    (rangePush branchless selector limb).arguments.mapM (Expr.eval window) = some [15, value] := by
  simp [rangePush, gate_eval _ _ _ _ selected, Expr.eval, evaluated]

theorem rangePush_weight (window : Window) (branchless : Bool) (selector limb : Expr)
    (selected : selector.eval window = some 1) :
    (rangePush branchless selector limb).multiplicity.eval window = some 1 := selected

theorem functionArguments_eval (window : Window) (branchless : Bool) (selector : Expr)
    (function : G) (inputs outputs : List Expr) (rank : Expr)
    (inputValues outputValues : List G) (rankValue : G)
    (selected : selector.eval window = some 1)
    (hi : inputs.mapM (Expr.eval window) = some inputValues)
    (ho : outputs.mapM (Expr.eval window) = some outputValues)
    (hr : rank.eval window = some rankValue) :
    (functionArguments branchless selector function inputs outputs rank).mapM (Expr.eval window) =
      some (functionMessage function inputValues outputValues rankValue) := by
  rw [functionArguments, gate_list_eval _ _ _ selected]
  simp [List.mapM_append, Expr.eval, hi, ho, hr, functionMessage, List.append_assoc]

theorem functionPull_weight (window : Window) (branchless : Bool) (selector weight : Expr)
    (function : G) (inputs outputs : List Expr) (rank : Expr) (value : G)
    (evaluated : weight.eval window = some value) :
    (functionPull branchless selector weight function inputs outputs rank).multiplicity.eval window =
      some (0 - value) := by
  simp [functionPull, Expr.eval, evaluated]

end IxCC.Aiur.AIR.Rank
