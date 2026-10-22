import Aiur.Eval

namespace Aiur

mutual
  /-- Finite source evaluation threads a fresh-allocation heap, with no fuel. -/
  inductive EvalExpr [Field F] [DecidableEq F] (program : Program F) :
      Environment F Nat → Expr F → Heap F → SourceValue F → Heap F → Prop where
    | literal : EvalExpr program locals (.literal value) heap (.field value) heap
    | var (lookup : locals.find? (·.1 == name) = some (name, value)) :
        EvalExpr program locals (.var name) heap value heap
    | tuple (items : EvalArgs program locals exprs before values after) :
        EvalExpr program locals (.tuple exprs) before (.tuple values) after
    | construct (items : EvalArgs program locals exprs before values after) :
        EvalExpr program locals (.construct name ctor exprs) before (.construct name ctor values) after
    | project (value : EvalExpr program locals expr before input after)
        (projected : projectValue input index = .ok result) :
        EvalExpr program locals (.project expr index) before result after
    | letValue (value : EvalExpr program locals expr before input middle)
        (matched : pattern.bindings input = some bindings)
        (body : EvalExpr program (bindings ++ locals) rest middle result after) :
        EvalExpr program locals (.letValue pattern expr rest) before result after
    | store (value : EvalExpr program locals expr before input middle) :
        EvalExpr program locals (.store expr) before (.ptr input.type middle.length) (middle ++ [input])
    | load (pointer : EvalExpr program locals expr before input after)
        (loaded : loadValue after input = .ok result) :
        EvalExpr program locals (.load expr) before result after
    | hint (key : EvalExpr program locals expr before input after)
        {value : Constant F} (typed : value.WellTyped program.enums type) :
        EvalExpr program locals (.hint type expr channel) before value.toValue after
    | neg (value : EvalExpr program locals expr before input after)
        (operation : evalNeg input = .ok result) :
        EvalExpr program locals (.neg expr) before result after
    | assertEq (left : EvalExpr program locals lhs before x middle)
        (right : EvalExpr program locals rhs middle y after)
        (operation : evalAssertEq op x y = .ok result) :
        EvalExpr program locals (.assertEq op lhs rhs) before result after
    | binary (left : EvalExpr program locals lhs before x middle)
        (right : EvalExpr program locals rhs middle y after)
        (operation : evalBinOp op x y = .ok result) :
        EvalExpr program locals (.binary op lhs rhs) before result after
    | call (arguments : EvalArgs program locals args before values middle)
        (callee : EvalFn program name values middle result after) :
        EvalExpr program locals (.call name args) before result after
    | matchValue (value : EvalExpr program locals expr before input middle)
        (selected : selectArm input arms = some (bindings, body))
        (branch : EvalExpr program (bindings ++ locals) body middle result after) :
        EvalExpr program locals (.matchValue expr arms) before result after

  inductive EvalArgs [Field F] [DecidableEq F] (program : Program F) :
      Environment F Nat → List (Expr F) → Heap F → List (SourceValue F) → Heap F → Prop where
    | nil : EvalArgs program locals [] heap [] heap
    | cons (head : EvalExpr program locals expr before value middle)
        (tail : EvalArgs program locals exprs middle values after) :
        EvalArgs program locals (expr :: exprs) before (value :: values) after

  /-- Internal calls share the caller's heap and may receive pointers. -/
  inductive EvalFn [Field F] [DecidableEq F] (program : Program F) :
      String → List (SourceValue F) → Heap F → SourceValue F → Heap F → Prop where
    | intro (prepared : prepareCall program name args = .ok (locals, expr))
        (body : EvalExpr program locals expr before result after) :
        EvalFn program name args before result after
end

/-- Public entry calls start with an empty heap and well-formed arguments of pointer-free types. -/
def EvalCall [Field F] [DecidableEq F] (program : Program F)
    (name : String) (args : List (SourceValue F)) (result : SourceValue F) : Prop :=
  checkEntry program name = .ok () ∧ ∃ heap, EvalFn program name args [] result heap

end Aiur
