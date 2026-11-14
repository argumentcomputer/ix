import Aiur.ROMSemantics

namespace Aiur

variable {F : Type} {rom : ROM F}

/-- Interpret each function call by a supplied premise relation. -/
abbrev CallRelation (F : Type) := String → List (Value F) → Value F → Prop

mutual
  inductive ROMEvalExprWith [Field F] [DecidableEq F] (decls : Declarations) (rom : ROM F) (calls : CallRelation F) :
      Environment F → Expr F → Value F → Prop where
    | literal : ROMEvalExprWith decls rom calls locals (.literal value) (.field value)
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        ROMEvalExprWith decls rom calls locals (.var name) value
    | tuple (items : ROMEvalArgsWith decls rom calls locals exprs values) :
        ROMEvalExprWith decls rom calls locals (.tuple exprs) (.tuple values)
    | construct (items : ROMEvalArgsWith decls rom calls locals exprs values) :
        ROMEvalExprWith decls rom calls locals (.construct name ctor exprs) (.construct name ctor values)
    | project (value : ROMEvalExprWith decls rom calls locals expr input)
        (projected : projectValue input index = .ok result) :
        ROMEvalExprWith decls rom calls locals (.project expr index) result
    | letValue (value : ROMEvalExprWith decls rom calls locals expr input)
        (matched : pattern.bindings input = some bindings)
        (body : ROMEvalExprWith decls rom calls (bindings ++ locals) rest result) :
        ROMEvalExprWith decls rom calls locals (.letValue pattern expr rest) result
    | store (value : ROMEvalExprWith decls rom calls locals expr input)
        (cell : (address, input) ∈ rom.entries) :
        ROMEvalExprWith decls rom calls locals (.store expr) (.ptr input.type address)
    | load (pointer : ROMEvalExprWith decls rom calls locals expr (.ptr target address))
        (cell : (address, result) ∈ rom.entries) (typed : result.type = target) :
        ROMEvalExprWith decls rom calls locals (.load expr) result
    | hint (key : ROMEvalExprWith decls rom calls locals expr input)
        {value : Constant F} (typed : value.WellTyped decls type) :
        ROMEvalExprWith decls rom calls locals (.hint type expr channel) value.toValue
    | neg (value : ROMEvalExprWith decls rom calls locals expr input) (operation : evalNeg input = .ok result) :
        ROMEvalExprWith decls rom calls locals (.neg expr) result
    | assertEq (left : ROMEvalExprWith decls rom calls locals lhs x) (right : ROMEvalExprWith decls rom calls locals rhs y)
        (operation : evalAssertEq op x y = .ok result) :
        ROMEvalExprWith decls rom calls locals (.assertEq op lhs rhs) result
    | binary (left : ROMEvalExprWith decls rom calls locals lhs x) (right : ROMEvalExprWith decls rom calls locals rhs y)
        (operation : evalBinOp op x y = .ok result) :
        ROMEvalExprWith decls rom calls locals (.binary op lhs rhs) result
    | call (arguments : ROMEvalArgsWith decls rom calls locals args values) (callee : calls name values result) :
        ROMEvalExprWith decls rom calls locals (.call name args) result
    | matchValue (value : ROMEvalExprWith decls rom calls locals expr input)
        (selected : selectArm input arms = some (bindings, body))
        (branch : ROMEvalExprWith decls rom calls (bindings ++ locals) body result) :
        ROMEvalExprWith decls rom calls locals (.matchValue expr arms) result

  inductive ROMEvalArgsWith [Field F] [DecidableEq F] (decls : Declarations) (rom : ROM F) (calls : CallRelation F) :
      Environment F → List (Expr F) → List (Value F) → Prop where
    | nil : ROMEvalArgsWith decls rom calls locals [] []
    | cons (head : ROMEvalExprWith decls rom calls locals expr value)
        (tail : ROMEvalArgsWith decls rom calls locals exprs values) :
        ROMEvalArgsWith decls rom calls locals (expr :: exprs) (value :: values)
end

theorem ROMEvalExprWith.toEvalExpr [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F} {expr : Expr F} {result : Value F}
    (evaluates : ROMEvalExprWith program.enums rom (ROMEvalCall rom program) locals expr result) :
    ROMEvalExpr rom program locals expr result := by
  induction evaluates using ROMEvalExprWith.rec
    (motive_2 := fun locals exprs values _ => ROMEvalArgs rom program locals exprs values) with
  | literal => exact .literal
  | var lookup => exact .var lookup
  | tuple _ ih => exact .tuple ih
  | construct _ ih => exact .construct ih
  | project _ projected ih => exact .project ih projected
  | letValue _ matched _ valueIH bodyIH => exact .letValue valueIH matched bodyIH
  | store _ cell ih => exact .store ih cell
  | load _ cell typed ih => exact .load ih cell typed
  | hint _ typed ih => exact .hint ih typed
  | neg _ operation ih => exact .neg ih operation
  | assertEq _ _ operation leftIH rightIH => exact .assertEq leftIH rightIH operation
  | binary _ _ operation leftIH rightIH => exact .binary leftIH rightIH operation
  | call _ callee ih => exact .call ih callee
  | matchValue _ selected _ valueIH bodyIH => exact .matchValue valueIH selected bodyIH
  | nil => exact .nil
  | cons _ _ headIH tailIH => exact .cons headIH tailIH

theorem ROMEvalExpr.toEvalExprWith [Field F] [DecidableEq F] {program : Program F}
    {locals : Environment F} {expr : Expr F} {result : Value F}
    (evaluates : ROMEvalExpr rom program locals expr result) :
    ROMEvalExprWith program.enums rom (ROMEvalCall rom program) locals expr result := by
  induction evaluates using ROMEvalExpr.rec
    (motive_2 := fun locals exprs values _ => ROMEvalArgsWith program.enums rom (ROMEvalCall rom program) locals exprs values)
    (motive_3 := fun _ _ _ _ => True) with
  | literal => exact .literal
  | var lookup => exact .var lookup
  | tuple _ ih => exact .tuple ih
  | construct _ ih => exact .construct ih
  | project _ projected ih => exact .project ih projected
  | letValue _ matched _ valueIH bodyIH => exact .letValue valueIH matched bodyIH
  | store _ cell ih => exact .store ih cell
  | load _ cell typed ih => exact .load ih cell typed
  | hint _ typed ih => exact .hint ih typed
  | neg _ operation ih => exact .neg ih operation
  | assertEq _ _ operation leftIH rightIH => exact .assertEq leftIH rightIH operation
  | binary _ _ operation leftIH rightIH => exact .binary leftIH rightIH operation
  | call _ callee ih _ => exact .call ih callee
  | matchValue _ selected _ valueIH bodyIH => exact .matchValue valueIH selected bodyIH
  | nil => exact .nil
  | cons _ _ headIH tailIH => exact .cons headIH tailIH
  | intro => trivial

end Aiur
