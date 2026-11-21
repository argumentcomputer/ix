import Aiur.Runtime

namespace Aiur

mutual
  /-- Finite successful evaluation, with structured results and no fuel parameter. -/
  inductive ROMEvalExpr [Field F] [DecidableEq F] (rom : ROM F) (program : Program F) :
      Environment F → Expr F → Value F → Prop where
    | literal : ROMEvalExpr rom program locals (.literal value) (.field value)
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        ROMEvalExpr rom program locals (.var name) value
    | tuple (items : ROMEvalArgs rom program locals exprs values) :
        ROMEvalExpr rom program locals (.tuple exprs) (.tuple values)
    | construct (items : ROMEvalArgs rom program locals exprs values) :
        ROMEvalExpr rom program locals (.construct name ctor exprs) (.construct name ctor values)
    | project (value : ROMEvalExpr rom program locals expr input)
        (projected : projectValue input index = .ok result) :
        ROMEvalExpr rom program locals (.project expr index) result
    | letValue (value : ROMEvalExpr rom program locals expr input)
        (matched : pattern.bindings input = some bindings)
        (body : ROMEvalExpr rom program (bindings ++ locals) rest result) :
        ROMEvalExpr rom program locals (.letValue pattern expr rest) result
    | store (value : ROMEvalExpr rom program locals expr input)
        (cell : (address, input) ∈ rom.entries) :
        ROMEvalExpr rom program locals (.store expr) (.ptr input.type address)
    | load (pointer : ROMEvalExpr rom program locals expr (.ptr target address))
        (cell : (address, result) ∈ rom.entries) (typed : result.type = target) :
        ROMEvalExpr rom program locals (.load expr) result
    | hint (key : ROMEvalExpr rom program locals expr input)
        {value : Constant F} (typed : value.WellTyped program.enums type) :
        ROMEvalExpr rom program locals (.hint type expr channel) value.toValue
    | neg (value : ROMEvalExpr rom program locals expr input) (operation : evalNeg input = .ok result) :
        ROMEvalExpr rom program locals (.neg expr) result
    | assertEq (left : ROMEvalExpr rom program locals lhs x) (right : ROMEvalExpr rom program locals rhs y)
        (operation : evalAssertEq op x y = .ok result) :
        ROMEvalExpr rom program locals (.assertEq op lhs rhs) result
    | binary (left : ROMEvalExpr rom program locals lhs x) (right : ROMEvalExpr rom program locals rhs y)
        (operation : evalBinOp op x y = .ok result) :
        ROMEvalExpr rom program locals (.binary op lhs rhs) result
    | call (arguments : ROMEvalArgs rom program locals args values)
        (callee : ROMEvalCall rom program name values result) :
        ROMEvalExpr rom program locals (.call name args) result
    | matchValue (value : ROMEvalExpr rom program locals expr input)
        (selected : selectArm input arms = some (bindings, body))
        (branch : ROMEvalExpr rom program (bindings ++ locals) body result) :
        ROMEvalExpr rom program locals (.matchValue expr arms) result

  inductive ROMEvalArgs [Field F] [DecidableEq F] (rom : ROM F) (program : Program F) :
      Environment F → List (Expr F) → List (Value F) → Prop where
    | nil : ROMEvalArgs rom program locals [] []
    | cons (head : ROMEvalExpr rom program locals expr value)
        (tail : ROMEvalArgs rom program locals exprs values) :
        ROMEvalArgs rom program locals (expr :: exprs) (value :: values)

  inductive ROMEvalCall [Field F] [DecidableEq F] (rom : ROM F) (program : Program F) :
      String → List (Value F) → Value F → Prop where
    | intro (prepared : prepareCall program name args = .ok (locals, expr))
        (body : ROMEvalExpr rom program locals expr result) : ROMEvalCall rom program name args result
end

end Aiur
