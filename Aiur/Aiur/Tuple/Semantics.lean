import Aiur.Tuple.Eval

namespace Aiur.Tuple

mutual
  /-- Finite successful evaluation, with structured results and no fuel parameter. -/
  inductive EvalExpr [Field F] [DecidableEq F] (program : Program F) :
      Environment F → Expr F → Value F → Prop where
    | literal : EvalExpr program locals (.literal value) (.field value)
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        EvalExpr program locals (.var name) value
    | tuple (items : EvalArgs program locals exprs values) :
        EvalExpr program locals (.tuple exprs) (.tuple values)
    | project (value : EvalExpr program locals expr input)
        (projected : projectValue input index = .ok result) :
        EvalExpr program locals (.project expr index) result
    | letValue (value : EvalExpr program locals expr input)
        (matched : pattern.bindings input = some bindings)
        (body : EvalExpr program (bindings ++ locals) rest result) :
        EvalExpr program locals (.letValue pattern expr rest) result
    | neg (value : EvalExpr program locals expr input) (operation : evalNeg input = .ok result) :
        EvalExpr program locals (.neg expr) result
    | binary (left : EvalExpr program locals lhs x) (right : EvalExpr program locals rhs y)
        (operation : evalBinOp op x y = .ok result) :
        EvalExpr program locals (.binary op lhs rhs) result
    | call (arguments : EvalArgs program locals args values)
        (callee : EvalCall program name values result) :
        EvalExpr program locals (.call name args) result
    | matchValue (value : EvalExpr program locals expr input)
        (selected : selectArm input arms = some (bindings, body))
        (branch : EvalExpr program (bindings ++ locals) body result) :
        EvalExpr program locals (.matchValue expr arms) result

  inductive EvalArgs [Field F] [DecidableEq F] (program : Program F) :
      Environment F → List (Expr F) → List (Value F) → Prop where
    | nil : EvalArgs program locals [] []
    | cons (head : EvalExpr program locals expr value)
        (tail : EvalArgs program locals exprs values) :
        EvalArgs program locals (expr :: exprs) (value :: values)

  inductive EvalCall [Field F] [DecidableEq F] (program : Program F) :
      String → List (Value F) → Value F → Prop where
    | intro (prepared : prepareCall program name args = .ok (locals, expr))
        (body : EvalExpr program locals expr result) : EvalCall program name args result
end

end Aiur.Tuple
