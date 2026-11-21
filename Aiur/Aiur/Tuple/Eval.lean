import Aiur.Tuple.Typecheck
import Mathlib.Algebra.Field.Defs

namespace Aiur.Tuple

abbrev Environment (F : Type) := List (String × Value F)

inductive EvalError where
  | invalidProgram (error : CheckError)
  | unknownFunction (name : String)
  | arityMismatch (function : String) (expected actual : Nat)
  | argumentTypeMismatch (function : String) (expected actual : Ty)
  | unboundVariable (name : String)
  | expectedField
  | expectedTuple
  | projectionBounds (index size : Nat)
  | patternMismatch
  | divisionByZero
  | noMatchingArm
  | outOfFuel
  deriving Repr, BEq, DecidableEq

mutual
  /-- Match the whole value and collect bindings in left-to-right order. -/
  def Pattern.bindings [DecidableEq F] : Pattern F → Value F → Option (Environment F)
    | .literal x, .field y => if x = y then some [] else none
    | .wildcard, _ => some []
    | .bind name, value => some [(name, value)]
    | .tuple patterns, .tuple values => Pattern.bindingsList patterns values
    | _, _ => none
  termination_by pattern _ => sizeOf pattern

  def Pattern.bindingsList [DecidableEq F] : List (Pattern F) → List (Value F) →
      Option (Environment F)
    | [], [] => some []
    | pattern :: patterns, value :: values => do
        return (← pattern.bindings value) ++ (← Pattern.bindingsList patterns values)
    | _, _ => none
  termination_by patterns _ => sizeOf patterns
end

def selectArm [DecidableEq F] (value : Value F) :
    List (Pattern F × Expr F) → Option (Environment F × Expr F)
  | [] => none
  | (pattern, body) :: rest =>
      match pattern.bindings value with
      | some bindings => some (bindings, body)
      | none => selectArm value rest

def evalNeg [Field F] : Value F → Except EvalError (Value F)
  | .field x => .ok (.field (-x))
  | .tuple _ => .error .expectedField

def evalBinOp [Field F] [DecidableEq F] (op : BinOp) :
    Value F → Value F → Except EvalError (Value F)
  | .field x, .field y =>
      match op with
      | .add => .ok (.field (x + y))
      | .sub => .ok (.field (x - y))
      | .mul => .ok (.field (x * y))
      | .div => if y = 0 then .error .divisionByZero else .ok (.field (x / y))
  | _, _ => .error .expectedField

def projectValue (value : Value F) (index : Nat) : Except EvalError (Value F) := do
  let .tuple items := value | throw .expectedTuple
  let some result := items[index]? | throw (.projectionBounds index items.length)
  return result

/-- Resolve a call and check the complete shapes of its arguments. -/
def prepareCall (program : Program F) (name : String) (args : List (Value F)) :
    Except EvalError (Environment F × Expr F) := do
  let some fn := program.findFunction? name | throw (.unknownFunction name)
  if fn.params.length != args.length then
    throw (.arityMismatch name fn.params.length args.length)
  for (param, arg) in fn.params.zip args do
    if param.2 ≠ arg.type then throw (.argumentTypeMismatch name param.2 arg.type)
  return ((fn.params.map Prod.fst).zip args, fn.body)

/-- Eager tuples and call arguments; only the first selected match body runs. -/
def evalExpr [Field F] [DecidableEq F] (program : Program F)
    (locals : Environment F) : Nat → Expr F → Except EvalError (Value F)
  | 0, _ => .error .outOfFuel
  | fuel + 1, expr => do
      match expr with
      | .literal value => return .field value
      | .var name =>
          let some (_, value) := locals.find? (·.1 == name) | throw (.unboundVariable name)
          return value
      | .tuple items => return .tuple (← items.mapM (evalExpr program locals fuel))
      | .project value index => projectValue (← evalExpr program locals fuel value) index
      | .letValue pattern value body =>
          let value ← evalExpr program locals fuel value
          let some bindings := pattern.bindings value | throw .patternMismatch
          evalExpr program (bindings ++ locals) fuel body
      | .neg value => evalNeg (← evalExpr program locals fuel value)
      | .binary op left right =>
          evalBinOp op (← evalExpr program locals fuel left) (← evalExpr program locals fuel right)
      | .call name args =>
          let values ← args.mapM (evalExpr program locals fuel)
          let (bindings, body) ← prepareCall program name values
          evalExpr program bindings fuel body
      | .matchValue scrutinee arms =>
          let value ← evalExpr program locals fuel scrutinee
          let some (bindings, body) := selectArm value arms | throw .noMatchingArm
          evalExpr program (bindings ++ locals) fuel body

/-- Entry arguments and results retain their complete tuple structure. -/
def eval [Field F] [DecidableEq F] (program : Program F) (name : String)
    (args : List (Value F)) (fuel : Nat := 1000) : Except EvalError (Value F) := do
  match typecheck program with
  | .error error => throw (.invalidProgram error)
  | .ok () => pure ()
  let (bindings, body) ← prepareCall program name args
  evalExpr program bindings fuel body

end Aiur.Tuple
