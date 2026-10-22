import Aiur.Tuple.AST

namespace Aiur.Tuple

inductive CheckError where
  | duplicateFunction (name : String)
  | duplicateParameter (function name : String)
  | duplicateBinding (function name : String)
  | unboundVariable (function name : String)
  | unknownFunction (caller callee : String)
  | arityMismatch (caller callee : String) (expected actual : Nat)
  | typeMismatch (function : String) (expected actual : Ty)
  | expectedTuple (function : String)
  | tupleArity (function : String) (expected actual : Nat)
  | projectionBounds (function : String) (index size : Nat)
  | refutableBinding (function : String)
  | emptyMatch (function : String)
  deriving Repr, BEq, DecidableEq

instance : ToString CheckError where
  toString
    | .duplicateFunction name => s!"duplicate function '{name}'"
    | .duplicateParameter fn name => s!"duplicate parameter '{name}' in function '{fn}'"
    | .duplicateBinding fn name => s!"duplicate pattern binding '{name}' in function '{fn}'"
    | .unboundVariable fn name => s!"unbound variable '{name}' in function '{fn}'"
    | .unknownFunction caller callee => s!"unknown function '{callee}' in function '{caller}'"
    | .arityMismatch caller callee expected actual =>
        s!"function '{caller}' calls '{callee}' with {actual} arguments; expected {expected}"
    | .typeMismatch fn expected actual =>
        s!"type mismatch in function '{fn}': expected {repr expected}, got {repr actual}"
    | .expectedTuple fn => s!"expected a tuple in function '{fn}'"
    | .tupleArity fn expected actual =>
        s!"tuple pattern in function '{fn}' has {actual} components; expected {expected}"
    | .projectionBounds fn index size =>
        s!"tuple projection .{index} is out of bounds for size {size} in function '{fn}'"
    | .refutableBinding fn => s!"let and parameter patterns must be irrefutable in function '{fn}'"
    | .emptyMatch fn => s!"empty match in function '{fn}'"

def findDuplicate : List String → List String → Option String
  | [], _ => none
  | name :: rest, seen =>
      if name ∈ seen then some name else findDuplicate rest (name :: seen)

def requireType (caller : String) (expected actual : Ty) : Except CheckError Unit :=
  if expected = actual then .ok () else .error (.typeMismatch caller expected actual)

mutual
  def patternTypes (caller : String) (pattern : Pattern α) (type : Ty) :
      Except CheckError (List (String × Ty)) := do
    match pattern with
    | .wildcard => return []
    | .bind name => return [(name, type)]
    | .literal _ => requireType caller .field type; return []
    | .tuple patterns =>
        let .tuple types := type | throw (.expectedTuple caller)
        if patterns.length != types.length then
          throw (.tupleArity caller types.length patterns.length)
        patternTypesList caller patterns types
  termination_by sizeOf pattern

  def patternTypesList (caller : String) (patterns : List (Pattern α)) (types : List Ty) :
      Except CheckError (List (String × Ty)) := do
    match patterns, types with
    | [], [] => return []
    | pattern :: patterns, type :: types =>
        return (← patternTypes caller pattern type) ++ (← patternTypesList caller patterns types)
    | _, _ => throw (.tupleArity caller types.length patterns.length)
  termination_by sizeOf patterns
end

def checkPattern (caller : String) (pattern : Pattern α) (type : Ty) :
    Except CheckError (List (String × Ty)) := do
  let bindings ← patternTypes caller pattern type
  if let some name := findDuplicate (bindings.map Prod.fst) [] then
    throw (.duplicateBinding caller name)
  return bindings

mutual
  def inferType (program : Program α) (caller : String) (locals : List (String × Ty))
      (expr : Expr α) : Except CheckError Ty := do
    match expr with
    | .literal _ => return .field
    | .var name =>
        let some (_, type) := locals.find? (·.1 == name) | throw (.unboundVariable caller name)
        return type
    | .tuple items => return .tuple (← inferTypes program caller locals items)
    | .project value index =>
        let .tuple types ← inferType program caller locals value | throw (.expectedTuple caller)
        let some type := types[index]? | throw (.projectionBounds caller index types.length)
        return type
    | .letValue pattern value body =>
        let type ← inferType program caller locals value
        let bindings ← checkPattern caller pattern type
        if !pattern.irrefutable then throw (.refutableBinding caller)
        inferType program caller (bindings ++ locals) body
    | .neg value =>
        requireType caller .field (← inferType program caller locals value)
        return .field
    | .binary _ left right =>
        requireType caller .field (← inferType program caller locals left)
        requireType caller .field (← inferType program caller locals right)
        return .field
    | .call name args =>
        let some fn := program.findFunction? name | throw (.unknownFunction caller name)
        if fn.params.length != args.length then
          throw (.arityMismatch caller name fn.params.length args.length)
        let types ← inferTypes program caller locals args
        for (expected, actual) in (fn.params.map Prod.snd).zip types do
          requireType caller expected actual
        return fn.result
    | .matchValue scrutinee arms =>
        let type ← inferType program caller locals scrutinee
        match arms with
        | [] => throw (.emptyMatch caller)
        | (pattern, body) :: rest =>
            let bindings ← checkPattern caller pattern type
            let result ← inferType program caller (bindings ++ locals) body
            checkArms program caller locals type result rest
            return result
  termination_by sizeOf expr

  def inferTypes (program : Program α) (caller : String) (locals : List (String × Ty))
      (exprs : List (Expr α)) : Except CheckError (List Ty) := do
    match exprs with
    | [] => return []
    | expr :: rest =>
        return (← inferType program caller locals expr) :: (← inferTypes program caller locals rest)
  termination_by sizeOf exprs

  def checkArms (program : Program α) (caller : String) (locals : List (String × Ty))
      (scrutinee result : Ty) (arms : List (Pattern α × Expr α)) : Except CheckError Unit := do
    match arms with
    | [] => return ()
    | (pattern, body) :: rest =>
        let bindings ← checkPattern caller pattern scrutinee
        requireType caller result (← inferType program caller (bindings ++ locals) body)
        checkArms program caller locals scrutinee result rest
  termination_by sizeOf arms
end

def typecheck (program : Program α) : Except CheckError Unit := do
  if let some name := findDuplicate (program.functions.map (·.name)) [] then
    throw (.duplicateFunction name)
  for fn in program.functions do
    if let some name := findDuplicate (fn.params.map Prod.fst) [] then
      throw (.duplicateParameter fn.name name)
    requireType fn.name fn.result (← inferType program fn.name fn.params fn.body)

end Aiur.Tuple
