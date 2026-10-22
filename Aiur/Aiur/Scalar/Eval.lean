import Aiur.Scalar.Typecheck
import Mathlib.Algebra.Field.Defs

namespace Aiur.Scalar

inductive EvalError where
  | invalidProgram (error : CheckError)
  | unknownFunction (name : String)
  | arityMismatch (function : String) (expected actual : Nat)
  | unboundVariable (name : String)
  | divisionByZero
  | noMatchingArm
  | outOfFuel
  deriving Repr, BEq, DecidableEq

instance : ToString EvalError where
  toString
    | .invalidProgram error => toString error
    | .unknownFunction name => s!"unknown function '{name}'"
    | .arityMismatch fn expected actual =>
        s!"function '{fn}' received {actual} arguments; expected {expected}"
    | .unboundVariable name => s!"unbound variable '{name}'"
    | .divisionByZero => "division by zero"
    | .noMatchingArm => "no matching arm"
    | .outOfFuel => "evaluation ran out of fuel"

def Pattern.matches [DecidableEq F] : Pattern F → F → Bool
  | .literal value, input => decide (value = input)
  | .wildcard, _ => true

/-- Arithmetic execution, exposed for the evaluator/semantics correspondence proof. -/
def evalBinOp [Field F] [DecidableEq F] (op : BinOp) (left right : F) :
    Except EvalError F :=
  match op with
  | .add => .ok (left + right)
  | .sub => .ok (left - right)
  | .mul => .ok (left * right)
  | .div => if right = 0 then .error .divisionByZero else .ok (left / right)

/--
A total reference evaluator. Fuel bounds expression nesting and recursive call depth;
each child receives the parent's remaining fuel. It is not a global step counter.
-/
def evalExpr [Field F] [DecidableEq F] (program : Program F)
    (locals : List (String × F)) : Nat → Expr F → Except EvalError F
  | 0, _ => .error .outOfFuel
  | fuel + 1, expr => do
      match expr with
      | .literal value => pure value
      | .var name =>
          let some (_, value) := locals.find? (·.1 == name) | throw (.unboundVariable name)
          pure value
      | .neg value => return -(← evalExpr program locals fuel value)
      | .binary op left right =>
          let left ← evalExpr program locals fuel left
          let right ← evalExpr program locals fuel right
          evalBinOp op left right
      | .call name args =>
          let some fn := program.findFunction? name | throw (.unknownFunction name)
          if fn.params.length != args.length then
            throw (.arityMismatch name fn.params.length args.length)
          let values ← args.mapM (evalExpr program locals fuel)
          evalExpr program (fn.params.zip values) fuel fn.body
      | .matchValue scrutinee arms =>
          let value ← evalExpr program locals fuel scrutinee
          let some (_, body) := arms.find? (fun (pat, _) => pat.matches value)
            | throw .noMatchingArm
          evalExpr program locals fuel body

/-- Evaluate an entry function with field arguments, checking the whole program first. -/
def eval [Field F] [DecidableEq F] (program : Program F) (function : String)
    (args : List F) (fuel : Nat := 1000) : Except EvalError F := do
  match typecheck program with
  | .error error => throw (.invalidProgram error)
  | .ok () => pure ()
  let some fn := program.findFunction? function | throw (.unknownFunction function)
  if fn.params.length != args.length then
    throw (.arityMismatch function fn.params.length args.length)
  evalExpr program (fn.params.zip args) fuel fn.body

end Aiur.Scalar
