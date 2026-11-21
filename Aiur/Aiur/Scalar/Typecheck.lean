import Aiur.Scalar.AST

namespace Aiur.Scalar

inductive CheckError where
  | duplicateFunction (name : String)
  | duplicateParameter (function name : String)
  | unboundVariable (function name : String)
  | unknownFunction (caller callee : String)
  | arityMismatch (caller callee : String) (expected actual : Nat)
  | emptyMatch (function : String)
  deriving Repr, BEq, DecidableEq

instance : ToString CheckError where
  toString
    | .duplicateFunction name => s!"duplicate function '{name}'"
    | .duplicateParameter fn name => s!"duplicate parameter '{name}' in function '{fn}'"
    | .unboundVariable fn name => s!"unbound variable '{name}' in function '{fn}'"
    | .unknownFunction caller callee => s!"unknown function '{callee}' in function '{caller}'"
    | .arityMismatch caller callee expected actual =>
        s!"function '{caller}' calls '{callee}' with {actual} arguments; expected {expected}"
    | .emptyMatch fn => s!"empty match in function '{fn}'"

private def findDuplicate : List String → List String → Option String
  | [], _ => none
  | name :: rest, seen =>
      if name ∈ seen then some name else findDuplicate rest (name :: seen)

mutual
  /-- With only field values, inference checks variable scope and function signatures. -/
  def inferType (program : Program α) (caller : String) (locals : List String)
      (expr : Expr α) : Except CheckError Ty := do
    match expr with
    | .literal _ => pure .field
    | .var name =>
        if name ∈ locals then pure .field else throw (.unboundVariable caller name)
    | .neg value => inferType program caller locals value
    | .binary _ left right =>
        let _ ← inferType program caller locals left
        inferType program caller locals right
    | .call name args =>
        let some fn := program.findFunction? name | throw (.unknownFunction caller name)
        if fn.params.length != args.length then
          throw (.arityMismatch caller name fn.params.length args.length)
        checkArgs program caller locals args
        pure .field
    | .matchValue scrutinee arms =>
        let _ ← inferType program caller locals scrutinee
        if arms.isEmpty then throw (.emptyMatch caller)
        checkArms program caller locals arms
        pure .field
  termination_by sizeOf expr

  private def checkArgs (program : Program α) (caller : String) (locals : List String)
      (args : List (Expr α)) : Except CheckError Unit := do
    match args with
    | [] => pure ()
    | arg :: rest =>
        let _ ← inferType program caller locals arg
        checkArgs program caller locals rest
  termination_by sizeOf args

  private def checkArms (program : Program α) (caller : String) (locals : List String)
      (arms : List (Pattern α × Expr α)) : Except CheckError Unit := do
    match arms with
    | [] => pure ()
    | (_, body) :: rest =>
        let _ ← inferType program caller locals body
        checkArms program caller locals rest
  termination_by sizeOf arms
end

/-- Check every body against the complete signature table, without choosing a field. -/
def typecheck (program : Program α) : Except CheckError Unit := do
  if let some name := findDuplicate (program.functions.map (·.name)) [] then
    throw (.duplicateFunction name)
  for fn in program.functions do
    if let some name := findDuplicate fn.params [] then
      throw (.duplicateParameter fn.name name)
    let _ ← inferType program fn.name fn.params fn.body

end Aiur.Scalar
