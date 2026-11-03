import Aiur.Tuple.Circuit.Basic
import Aiur.Tuple.Typecheck

namespace Aiur.Tuple.Circuit

inductive CompileError where
  | invalidProgram (error : CheckError)
  | duplicatePattern (function : String)
  | invalidShape
  deriving Repr, BEq, DecidableEq

namespace Compiler

structure BuildState (F : Type) where
  nextVar : Nat := 0
  constraints : Array (Constraint F) := #[]
  sends : Array (Send F) := #[]

abbrev Build (F : Type) := StateT (BuildState F) (Except CompileError)
abbrev Symbolic (F : Type) := Value (ArithExpr F)
abbrev Locals (F : Type) := List (String × Symbolic F)

def fresh : Build F Var := do
  let state ← get
  set { state with nextVar := state.nextVar + 1 }
  return state.nextVar

def constrain (polynomial : ArithExpr F) : Build F Unit :=
  modify fun state => { state with constraints := state.constraints.push polynomial }

def guarded (enable polynomial : ArithExpr F) : Build F Unit := constrain (.mul enable polynomial)

def boolean [Field F] (selector : ArithExpr F) : Build F Unit :=
  constrain (.mul selector (.sub selector (.const 1)))

mutual
  def freshValue (type : Ty) : Build F (Value Var) := do
    match type with
    | .field => return .field (← fresh)
    | .tuple types => return .tuple (← freshValues types)
  termination_by sizeOf type

  def freshValues (types : List Ty) : Build F (List (Value Var)) := do
    match types with
    | [] => return []
    | type :: rest => return (← freshValue type) :: (← freshValues rest)
  termination_by sizeOf types
end

def checkPatterns [DecidableEq F] (function : String) :
    List (Pattern F × Expr F) → List (Pattern F) → Except CompileError Unit
  | [], _ => pure ()
  | (pattern, _) :: rest, seen => do
      if seen.any (fun other => decide (pattern.condition = other)) then
        throw (.duplicatePattern function)
      if pattern.irrefutable then return ()
      checkPatterns function rest (pattern.condition :: seen)

/-- A zero test is exact in every field; its inverse is a witness, never division in a constraint. -/
def equalIndicator [Field F] (difference : ArithExpr F) : Build F (ArithExpr F) := do
  let equal := ArithExpr.var (← fresh)
  let inverse := ArithExpr.var (← fresh)
  boolean equal
  constrain (.mul difference equal)
  constrain (.sub (.mul difference inverse) (.sub (.const 1) equal))
  return equal

mutual
  /-- A pattern's indicator and bindings, including nested conjunctions of leaf tests. -/
  def lowerPattern [Field F] (pattern : Pattern F) (value : Symbolic F) :
      Build F (ArithExpr F × Locals F) := do
    match pattern, value with
    | .wildcard, _ => return (.const 1, [])
    | .bind name, value => return (.const 1, [(name, value)])
    | .literal literal, .field value =>
        return (← equalIndicator (.sub value (.const literal)), [])
    | .tuple patterns, .tuple values => lowerPatterns patterns values
    | _, _ => throw .invalidShape
  termination_by sizeOf pattern

  def lowerPatterns [Field F] (patterns : List (Pattern F)) (values : List (Symbolic F)) :
      Build F (ArithExpr F × Locals F) := do
    match patterns, values with
    | [], [] => return (.const 1, [])
    | pattern :: patterns, value :: values =>
        let (test, bindings) ← lowerPattern pattern value
        let (tests, rest) ← lowerPatterns patterns values
        return (.mul test tests, bindings ++ rest)
    | _, _ => throw .invalidShape
  termination_by sizeOf patterns
end

mutual
  def constrainValue (enable : ArithExpr F) (left right : Symbolic F) : Build F Unit := do
    match left, right with
    | .field left, .field right => guarded enable (.sub left right)
    | .tuple left, .tuple right => constrainValues enable left right
    | _, _ => throw .invalidShape
  termination_by sizeOf left

  def constrainValues (enable : ArithExpr F) (left right : List (Symbolic F)) : Build F Unit := do
    match left, right with
    | [], [] => return ()
    | left :: ls, right :: rs =>
        constrainValue enable left right
        constrainValues enable ls rs
    | _, _ => throw .invalidShape
  termination_by sizeOf left
end

def asField : Symbolic F → Build F (ArithExpr F)
  | .field value => pure value
  | .tuple _ => throw .invalidShape

def excludePairs (selectors : List (ArithExpr F)) : Build F Unit := do
  match selectors with
  | [] => return ()
  | selector :: rest =>
      for other in rest do constrain (.mul selector other)
      excludePairs rest

mutual
  def lowerExpr [Field F] [DecidableEq F] (program : Program F) (function : String)
      (locals : Locals F) (enable : ArithExpr F) (expr : Expr F) : Build F (Symbolic F) := do
    match expr with
    | .literal value => return .field (.const value)
    | .var name =>
        let some (_, value) := locals.find? (·.1 == name)
          | throw (.invalidProgram (.unboundVariable function name))
        return value
    | .tuple items => return .tuple (← lowerArgs program function locals enable items)
    | .project value index =>
        let .tuple items ← lowerExpr program function locals enable value | throw .invalidShape
        let some value := items[index]? | throw .invalidShape
        return value
    | .letValue pattern value body =>
        let value ← lowerExpr program function locals enable value
        let (test, bindings) ← lowerPattern pattern value
        guarded enable (.sub test (.const 1))
        lowerExpr program function (bindings ++ locals) enable body
    | .neg value =>
        return .field (.sub (.const 0) (← asField (← lowerExpr program function locals enable value)))
    | .binary op left right =>
        let left ← asField (← lowerExpr program function locals enable left)
        let right ← asField (← lowerExpr program function locals enable right)
        match op with
        | .add => return .field (.add left right)
        | .sub => return .field (.sub left right)
        | .mul => return .field (.mul left right)
        | .div =>
            let inverse ← fresh
            guarded enable (.sub (.mul right (.var inverse)) (.const 1))
            return .field (.mul left (.var inverse))
    | .call name args =>
        let some callee := program.findFunction? name
          | throw (.invalidProgram (.unknownFunction function name))
        let args ← lowerArgs program function locals enable args
        let result ← freshValue callee.result
        boolean enable
        modify fun state => { state with sends := state.sends.push ⟨name, args, result, enable⟩ }
        return result.map ArithExpr.var
    | .matchValue scrutinee arms =>
        liftM (checkPatterns function arms [])
        let type ← liftM ((inferType program function
          (locals.map fun (name, value) => (name, value.type)) expr).mapError CompileError.invalidProgram)
        let scrutinee ← lowerExpr program function locals enable scrutinee
        let result ← freshValue type
        let selectors ← lowerArms program function locals scrutinee
          (result.map ArithExpr.var) enable arms
        excludePairs selectors
        constrain (.sub (selectors.foldl ArithExpr.add (.const 0)) enable)
        return result.map ArithExpr.var
  termination_by sizeOf expr

  def lowerArgs [Field F] [DecidableEq F] (program : Program F) (function : String)
      (locals : Locals F) (enable : ArithExpr F) (args : List (Expr F)) :
      Build F (List (Symbolic F)) := do
    match args with
    | [] => return []
    | arg :: rest =>
        return (← lowerExpr program function locals enable arg) ::
          (← lowerArgs program function locals enable rest)
  termination_by sizeOf args

  def lowerArms [Field F] [DecidableEq F] (program : Program F) (function : String)
      (locals : Locals F) (scrutinee result : Symbolic F) (remaining : ArithExpr F)
      (arms : List (Pattern F × Expr F)) : Build F (List (ArithExpr F)) := do
    match arms with
    | [] => return []
    | (pattern, body) :: rest =>
        let (test, bindings) ← lowerPattern pattern scrutinee
        let selector := ArithExpr.var (← fresh)
        boolean selector
        constrain (.sub selector (.mul remaining test))
        let body ← lowerExpr program function (bindings ++ locals) selector body
        constrainValue selector result body
        if pattern.irrefutable then return [selector]
        let rest ← lowerArms program function locals scrutinee result
          (.mul remaining (.sub (.const 1) test)) rest
        return selector :: rest
  termination_by sizeOf arms
end

def lowerFunction [Field F] [DecidableEq F] (program : Program F) (fn : Function F) :
    Except CompileError (Chip F) := do
  let build : Build F (List (Value Var) × Value Var) := do
    let inputs ← freshValues (fn.params.map Prod.snd)
    let output ← freshValue fn.result
    let locals := (fn.params.map Prod.fst).zip (inputs.map (Value.map ArithExpr.var))
    let body ← lowerExpr program fn.name locals (.const 1) fn.body
    constrainValue (.const 1) (output.map ArithExpr.var) body
    return (inputs, output)
  let ((inputs, output), state) ← build.run {}
  return ⟨fn.name, inputs, output, state.nextVar, state.constraints.toList, state.sends.toList⟩

end Compiler

/-- One chip per function, with one fresh variable for each field leaf of a call result. -/
def compile [Field F] [DecidableEq F] (program : Program F) : Except CompileError (System F) := do
  match typecheck program with
  | .error error => throw (.invalidProgram error)
  | .ok () => pure ()
  return ⟨← program.functions.mapM (Compiler.lowerFunction program)⟩

end Aiur.Tuple.Circuit
