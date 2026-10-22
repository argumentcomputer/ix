import Aiur.Declarations
import Aiur.TableUniqueness

namespace Aiur

inductive CheckError where
  | invalidDeclarations (error : DeclError)
  | pointerType (context : String) (type : Ty)
  | unknownConstructor (enumName constructor : String)
  | constructorArity (enumName constructor : String) (expected actual : Nat)
  | duplicateFunction (name : String)
  | duplicateParameter (function name : String)
  | duplicateBinding (function name : String)
  | unboundVariable (function name : String)
  | unknownFunction (caller callee : String)
  | arityMismatch (caller callee : String) (expected actual : Nat)
  | typeMismatch (function : String) (expected actual : Ty)
  | expectedPointer (function : String)
  | expectedTuple (function : String)
  | tupleArity (function : String) (expected actual : Nat)
  | projectionBounds (function : String) (index size : Nat)
  | emptyMatch (function : String)
  | duplicateTable (name : String)
  | unknownTable (map table : String)
  | malformedTableRow (table : String) (index : Nat)
  | tableRowType (table : String) (index : Nat) (expected actual : Ty)
  | tableLength (map : String) (inputs outputs : Nat)
  | duplicateInput (map table : String)
  deriving Repr, BEq, DecidableEq

instance : ToString CheckError where
  toString
    | .invalidDeclarations error => toString error
    | .pointerType context type => s!"{context} requires a pointer-free type; got {repr type}"
    | .unknownConstructor name ctor => s!"unknown constructor '{name}::{ctor}'"
    | .constructorArity name ctor expected actual =>
        s!"constructor '{name}::{ctor}' has {actual} arguments; expected {expected}"
    | .duplicateFunction name => s!"duplicate function '{name}'"
    | .duplicateParameter fn name => s!"duplicate parameter '{name}' in function '{fn}'"
    | .duplicateBinding fn name => s!"duplicate pattern binding '{name}' in function '{fn}'"
    | .unboundVariable fn name => s!"unbound variable '{name}' in function '{fn}'"
    | .unknownFunction caller callee => s!"unknown function '{callee}' in function '{caller}'"
    | .arityMismatch caller callee expected actual =>
        s!"function '{caller}' calls '{callee}' with {actual} arguments; expected {expected}"
    | .typeMismatch fn expected actual =>
        s!"type mismatch in function '{fn}': expected {repr expected}, got {repr actual}"
    | .expectedPointer fn => s!"expected a pointer in function '{fn}'"
    | .expectedTuple fn => s!"expected a tuple in function '{fn}'"
    | .tupleArity fn expected actual =>
        s!"tuple pattern in function '{fn}' has {actual} components; expected {expected}"
    | .projectionBounds fn index size =>
        s!"tuple projection .{index} is out of bounds for size {size} in function '{fn}'"
    | .emptyMatch fn => s!"empty match in function '{fn}'"
    | .duplicateTable name => s!"duplicate table '{name}'"
    | .unknownTable map table => s!"map '{map}' refers to unknown table '{table}'"
    | .malformedTableRow table index => s!"malformed value in table '{table}', row {index}"
    | .tableRowType table index expected actual =>
        s!"table '{table}', row {index}: expected {repr expected}, got {repr actual}"
    | .tableLength map inputs outputs =>
        s!"map '{map}' has {inputs} input rows and {outputs} output rows"
    | .duplicateInput map table => s!"map '{map}' uses repeated input rows in table '{table}'"

def findDuplicate : List String → List String → Option String
  | [], _ => none
  | name :: rest, seen =>
      if name ∈ seen then some name else findDuplicate rest (name :: seen)

def requireType (caller : String) (expected actual : Ty) : Except CheckError Unit :=
  if expected = actual then .ok () else .error (.typeMismatch caller expected actual)

/-- Check the declared type even when no value or table row is supplied. -/
def requirePointerFree (decls : Declarations) (context : String) (type : Ty) : Except CheckError Unit :=
  if type.pointerFree decls then .ok () else .error (.pointerType context type)

def checkHintType (decls : Declarations) (caller : String) (type : Ty) : Except CheckError Ty := do
  (type.checkNames decls).mapError CheckError.invalidDeclarations
  requirePointerFree decls s!"hint in '{caller}'" type
  return type

mutual
  def patternTypes (decls : Declarations) (caller : String) (pattern : Pattern α) (type : Ty) :
      Except CheckError (List (String × Ty)) := do
    match pattern with
    | .wildcard => return []
    | .bind name => return [(name, type)]
    | .literal _ => requireType caller .field type; return []
    | .tuple patterns =>
        let .tuple types := type | throw (.expectedTuple caller)
        if patterns.length != types.length then
          throw (.tupleArity caller types.length patterns.length)
        patternTypesList decls caller patterns types
    | .construct name ctor patterns =>
        requireType caller (.enum name) type
        let some definition := decls.findConstructor? name ctor
          | throw (.unknownConstructor name ctor)
        if patterns.length != definition.fields.length then
          throw (.constructorArity name ctor definition.fields.length patterns.length)
        patternTypesList decls caller patterns definition.fields
  termination_by sizeOf pattern

  def patternTypesList (decls : Declarations) (caller : String) (patterns : List (Pattern α)) (types : List Ty) :
      Except CheckError (List (String × Ty)) := do
    match patterns, types with
    | [], [] => return []
    | pattern :: patterns, type :: types =>
        return (← patternTypes decls caller pattern type) ++ (← patternTypesList decls caller patterns types)
    | _, _ => throw (.tupleArity caller types.length patterns.length)
  termination_by sizeOf patterns
end

def checkPattern (decls : Declarations) (caller : String) (pattern : Pattern α) (type : Ty) :
    Except CheckError (List (String × Ty)) := do
  let bindings ← patternTypes decls caller pattern type
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
    | .construct name ctor args =>
        let some definition := program.enums.findConstructor? name ctor
          | throw (.unknownConstructor name ctor)
        if args.length != definition.fields.length then
          throw (.constructorArity name ctor definition.fields.length args.length)
        let types ← inferTypes program caller locals args
        for (expected, actual) in definition.fields.zip types do
          requireType caller expected actual
        return .enum name
    | .project value index =>
        let .tuple types ← inferType program caller locals value | throw (.expectedTuple caller)
        let some type := types[index]? | throw (.projectionBounds caller index types.length)
        return type
    | .letValue pattern value body =>
        let type ← inferType program caller locals value
        let bindings ← checkPattern program.enums caller pattern type
        inferType program caller (bindings ++ locals) body
    | .store value => return .ptr (← inferType program caller locals value)
    | .load pointer =>
        let .ptr target ← inferType program caller locals pointer | throw (.expectedPointer caller)
        return target
    | .hint type key channel =>
        let keyType ← inferType program caller locals key
        requirePointerFree program.enums s!"hint key in '{caller}'" keyType
        checkHintType program.enums caller type
    | .neg value =>
        requireType caller .field (← inferType program caller locals value)
        return .field
    | .assertEq _ left right =>
        let type ← inferType program caller locals left
        requireType caller type (← inferType program caller locals right)
        if !type.pointerFree program.enums then throw (.pointerType "assert_eq!" type)
        return .tuple []
    | .binary _ left right =>
        requireType caller .field (← inferType program caller locals left)
        requireType caller .field (← inferType program caller locals right)
        return .field
    | .call name args =>
        let some fn := program.findSignature? name | throw (.unknownFunction caller name)
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
            let bindings ← checkPattern program.enums caller pattern type
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
        let bindings ← checkPattern program.enums caller pattern scrutinee
        requireType caller result (← inferType program caller (bindings ++ locals) body)
        checkArms program caller locals scrutinee result rest
  termination_by sizeOf arms
end

def checkFunction (program : Program α) (fn : Function α) : Except CheckError Unit := do
  for (_, type) in fn.params do
    (type.checkNames program.enums).mapError CheckError.invalidDeclarations
  (fn.result.checkNames program.enums).mapError CheckError.invalidDeclarations
  if let some name := findDuplicate (fn.params.map Prod.fst) [] then
    throw (.duplicateParameter fn.name name)
  requireType fn.name fn.result (← inferType program fn.name fn.params fn.body)

def checkTableRow (program : Program α) (table : Table α)
    (entry : Constant α × Nat) : Except CheckError Unit := do
  let (row, index) := entry
  if row.type ≠ table.rowType then
    throw (.tableRowType table.name index table.rowType row.type)
  if !row.wellFormed program.enums then throw (.malformedTableRow table.name index)

def checkTable (program : Program α) (table : Table α) : Except CheckError Unit := do
  (table.rowType.checkNames program.enums).mapError CheckError.invalidDeclarations
  requirePointerFree program.enums s!"table '{table.name}'" table.rowType
  for entry in table.rows.zipIdx do checkTableRow program table entry

def checkMap [DecidableEq α] (program : Program α) (map : MapDecl) : Except CheckError Unit := do
  for (_, type) in map.params do
    (type.checkNames program.enums).mapError CheckError.invalidDeclarations
  (map.result.checkNames program.enums).mapError CheckError.invalidDeclarations
  requirePointerFree program.enums s!"map '{map.name}' inputs" (.tuple (map.params.map Prod.snd))
  requirePointerFree program.enums s!"map '{map.name}' result" map.result
  if let some name := findDuplicate (map.params.map Prod.fst) [] then
    throw (.duplicateParameter map.name name)
  let some inputs := program.findTable? map.input | throw (.unknownTable map.name map.input)
  let some outputs := program.findTable? map.output | throw (.unknownTable map.name map.output)
  requireType map.name (.tuple (map.params.map Prod.snd)) inputs.rowType
  requireType map.name map.result outputs.rowType
  if inputs.rows.length != outputs.rows.length then
    throw (.tableLength map.name inputs.rows.length outputs.rows.length)
  if !tableRowsNodup inputs.rows then throw (.duplicateInput map.name map.input)

def checkTables [DecidableEq α] (program : Program α) : Except CheckError Unit := do
  if let some name := findDuplicate (program.tables.map (·.name)) [] then
    throw (.duplicateTable name)
  for table in program.tables do checkTable program table
  for map in program.maps do checkMap program map

def typecheck [DecidableEq α] (program : Program α) : Except CheckError Unit := do
  (checkDeclarations program.enums).mapError CheckError.invalidDeclarations
  if let some name := findDuplicate (program.functions.map (·.name) ++ program.maps.map (·.name)) [] then
    throw (.duplicateFunction name)
  checkTables program
  for fn in program.functions do checkFunction program fn

end Aiur
