import Aiur.Scalar.Semantics

namespace Aiur.Scalar

/-- Interpret a call by a supplied relation while evaluating the surrounding body. -/
abbrev CallRelation (F : Type) := String → List F → F → Prop

mutual
  /-- One function body's semantics, with calls supplied as premises. -/
  inductive EvalExprWith [Field F] (calls : CallRelation F) :
      Environment F → Expr F → F → Prop where
    | literal : EvalExprWith calls locals (.literal value) value
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        EvalExprWith calls locals (.var name) value
    | neg (operand : EvalExprWith calls locals expr value) :
        EvalExprWith calls locals (.neg expr) (-value)
    | add (left : EvalExprWith calls locals lhs x) (right : EvalExprWith calls locals rhs y) :
        EvalExprWith calls locals (.binary .add lhs rhs) (x + y)
    | sub (left : EvalExprWith calls locals lhs x) (right : EvalExprWith calls locals rhs y) :
        EvalExprWith calls locals (.binary .sub lhs rhs) (x - y)
    | mul (left : EvalExprWith calls locals lhs x) (right : EvalExprWith calls locals rhs y) :
        EvalExprWith calls locals (.binary .mul lhs rhs) (x * y)
    | div (left : EvalExprWith calls locals lhs x) (right : EvalExprWith calls locals rhs y)
        (nonzero : y ≠ 0) :
        EvalExprWith calls locals (.binary .div lhs rhs) (x / y)
    | call (arguments : EvalArgsWith calls locals args values) (callee : calls name values result) :
        EvalExprWith calls locals (.call name args) result
    | matchValue (scrutinee : EvalExprWith calls locals expr value)
        (selected : SelectArm value arms body) (branch : EvalExprWith calls locals body result) :
        EvalExprWith calls locals (.matchValue expr arms) result

  inductive EvalArgsWith [Field F] (calls : CallRelation F) :
      Environment F → List (Expr F) → List F → Prop where
    | nil : EvalArgsWith calls locals [] []
    | cons (head : EvalExprWith calls locals expr value)
        (tail : EvalArgsWith calls locals exprs values) :
        EvalArgsWith calls locals (expr :: exprs) (value :: values)
end

/-- Supplying actual source call proofs recovers the original expression relation. -/
theorem EvalExprWith.toEvalExpr [Field F] {program : Program F}
    {locals : Environment F} {expr : Expr F} {result : F}
    (evaluates : EvalExprWith (EvalCall program) locals expr result) :
    EvalExpr program locals expr result := by
  induction evaluates using EvalExprWith.rec
    (motive_2 := fun locals exprs values _ => EvalArgs program locals exprs values) with
  | literal => exact .literal
  | var lookup => exact .var lookup
  | neg _ ih => exact .neg ih
  | add _ _ leftIH rightIH => exact .add leftIH rightIH
  | sub _ _ leftIH rightIH => exact .sub leftIH rightIH
  | mul _ _ leftIH rightIH => exact .mul leftIH rightIH
  | div _ _ nonzero leftIH rightIH => exact .div leftIH rightIH nonzero
  | call _ callee argumentsIH => exact .call argumentsIH callee
  | matchValue _ selected _ scrutineeIH branchIH => exact .matchValue scrutineeIH selected branchIH
  | nil => exact .nil
  | cons _ _ headIH tailIH => exact .cons headIH tailIH

theorem EvalExpr.toEvalExprWith [Field F] {program : Program F}
    {locals : Environment F} {expr : Expr F} {result : F}
    (evaluates : EvalExpr program locals expr result) :
    EvalExprWith (EvalCall program) locals expr result := by
  induction evaluates using EvalExpr.rec
    (motive_2 := fun locals exprs values _ => EvalArgsWith (EvalCall program) locals exprs values)
    (motive_3 := fun _ _ _ _ => True) with
  | literal => exact .literal
  | var lookup => exact .var lookup
  | neg _ ih => exact .neg ih
  | add _ _ leftIH rightIH => exact .add leftIH rightIH
  | sub _ _ leftIH rightIH => exact .sub leftIH rightIH
  | mul _ _ leftIH rightIH => exact .mul leftIH rightIH
  | div _ _ nonzero leftIH rightIH => exact .div leftIH rightIH nonzero
  | call _ callee argumentsIH _ => exact .call argumentsIH callee
  | matchValue _ selected _ scrutineeIH branchIH => exact .matchValue scrutineeIH selected branchIH
  | nil => exact .nil
  | cons _ _ headIH tailIH => exact .cons headIH tailIH
  | intro => trivial

theorem evalExprWith_iff_evalExpr [Field F] {program : Program F}
    {locals : Environment F} {expr : Expr F} {result : F} :
    EvalExprWith (EvalCall program) locals expr result ↔ EvalExpr program locals expr result :=
  ⟨EvalExprWith.toEvalExpr, EvalExpr.toEvalExprWith⟩

end Aiur.Scalar
