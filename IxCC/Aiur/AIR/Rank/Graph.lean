import IxCC.Aiur.AIR.Rank.Model

/-! Rank and scalar-range expression fragments. Constant-zero/one folding
matches the pinned Rust multiplication constructor used by selector gating. -/

namespace IxCC.Aiur.AIR.Rank

open _root_.IxCC.Vendor.Aiur (G)

def gate (branchless : Bool) (selector argument : Expr) : Expr :=
  if branchless then argument
  else match argument with
    | .constant value =>
        if value = 0 then .constant 0
        else if value = 1 then selector
        else .mul selector argument
    | _ => .mul selector argument

def packColumns (base : Nat) : Expr := pack (.main base) (.main (base + 1)) (.main (base + 2))

def callExpr (mode : CallMode) (parent gap boundary : Expr) : Expr :=
  match mode with
  | .zero => .constant 0
  | .bound => boundary
  | .ordered => orderedExpr parent gap

def rangePush (branchless : Bool) (selector limb : Expr) : Lookup :=
  { multiplicity := selector
    arguments := [gate branchless selector (.constant 15), gate branchless selector limb] }

def functionArguments (branchless : Bool) (selector : Expr) (function : G)
    (inputs outputs : List Expr) (rank : Expr) : List Expr :=
  ([Expr.constant 0, Expr.constant function] ++ inputs ++ outputs ++ [rank]).map (gate branchless selector)

def functionPush (branchless : Bool) (selector : Expr) (function : G)
    (inputs outputs : List Expr) (rank : Expr) : Lookup :=
  { multiplicity := selector
    arguments := functionArguments branchless selector function inputs outputs rank }

def functionPull (branchless : Bool) (selector weight : Expr) (function : G)
    (inputs outputs : List Expr) (rank : Expr) : Lookup :=
  { multiplicity := .neg weight
    arguments := functionArguments branchless selector function inputs outputs rank }

end IxCC.Aiur.AIR.Rank
