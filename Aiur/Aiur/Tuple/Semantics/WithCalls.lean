import Aiur.Tuple.Semantics

namespace Aiur.Tuple

/-- Interpret each function call by a supplied premise relation. -/
abbrev CallRelation (F : Type) := String → List (Value F) → Value F → Prop

mutual
  inductive EvalExprWith [Field F] [DecidableEq F] (calls : CallRelation F) :
      Environment F → Expr F → Value F → Prop where
    | literal : EvalExprWith calls locals (.literal value) (.field value)
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        EvalExprWith calls locals (.var name) value
    | tuple (items : EvalArgsWith calls locals exprs values) :
        EvalExprWith calls locals (.tuple exprs) (.tuple values)
    | project (value : EvalExprWith calls locals expr input)
        (projected : projectValue input index = .ok result) :
        EvalExprWith calls locals (.project expr index) result
    | letValue (value : EvalExprWith calls locals expr input)
        (matched : pattern.bindings input = some bindings)
        (body : EvalExprWith calls (bindings ++ locals) rest result) :
        EvalExprWith calls locals (.letValue pattern expr rest) result
    | neg (value : EvalExprWith calls locals expr input) (operation : evalNeg input = .ok result) :
        EvalExprWith calls locals (.neg expr) result
    | binary (left : EvalExprWith calls locals lhs x) (right : EvalExprWith calls locals rhs y)
        (operation : evalBinOp op x y = .ok result) :
        EvalExprWith calls locals (.binary op lhs rhs) result
    | call (arguments : EvalArgsWith calls locals args values) (callee : calls name values result) :
        EvalExprWith calls locals (.call name args) result
    | matchValue (value : EvalExprWith calls locals expr input)
        (selected : selectArm input arms = some (bindings, body))
        (branch : EvalExprWith calls (bindings ++ locals) body result) :
        EvalExprWith calls locals (.matchValue expr arms) result

  inductive EvalArgsWith [Field F] [DecidableEq F] (calls : CallRelation F) :
      Environment F → List (Expr F) → List (Value F) → Prop where
    | nil : EvalArgsWith calls locals [] []
    | cons (head : EvalExprWith calls locals expr value)
        (tail : EvalArgsWith calls locals exprs values) :
        EvalArgsWith calls locals (expr :: exprs) (value :: values)
end

theorem EvalExprWith.toEvalExpr [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F} {expr : Expr F} {result : Value F}
    (evaluates : EvalExprWith (EvalCall program) locals expr result) :
    EvalExpr program locals expr result := by
  induction evaluates using EvalExprWith.rec
    (motive_2 := fun locals exprs values _ => EvalArgs program locals exprs values) with
  | literal => exact .literal
  | var lookup => exact .var lookup
  | tuple _ ih => exact .tuple ih
  | project _ projected ih => exact .project ih projected
  | letValue _ matched _ valueIH bodyIH => exact .letValue valueIH matched bodyIH
  | neg _ operation ih => exact .neg ih operation
  | binary _ _ operation leftIH rightIH => exact .binary leftIH rightIH operation
  | call _ callee ih => exact .call ih callee
  | matchValue _ selected _ valueIH bodyIH => exact .matchValue valueIH selected bodyIH
  | nil => exact .nil
  | cons _ _ headIH tailIH => exact .cons headIH tailIH

theorem EvalExpr.toEvalExprWith [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F} {expr : Expr F} {result : Value F}
    (evaluates : EvalExpr program locals expr result) :
    EvalExprWith (EvalCall program) locals expr result := by
  induction evaluates using EvalExpr.rec
    (motive_2 := fun locals exprs values _ => EvalArgsWith (EvalCall program) locals exprs values)
    (motive_3 := fun _ _ _ _ => True) with
  | literal => exact .literal
  | var lookup => exact .var lookup
  | tuple _ ih => exact .tuple ih
  | project _ projected ih => exact .project ih projected
  | letValue _ matched _ valueIH bodyIH => exact .letValue valueIH matched bodyIH
  | neg _ operation ih => exact .neg ih operation
  | binary _ _ operation leftIH rightIH => exact .binary leftIH rightIH operation
  | call _ callee ih _ => exact .call ih callee
  | matchValue _ selected _ valueIH bodyIH => exact .matchValue valueIH selected bodyIH
  | nil => exact .nil
  | cons _ _ headIH tailIH => exact .cons headIH tailIH
  | intro => trivial

end Aiur.Tuple
