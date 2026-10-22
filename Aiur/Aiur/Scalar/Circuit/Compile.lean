import Aiur.Scalar.Circuit.Basic
import Aiur.Scalar.Typecheck

namespace Aiur.Scalar.Circuit

inductive CompileError where
  | invalidProgram (error : CheckError)
  | duplicatePattern (function : String)
  deriving Repr, BEq, DecidableEq

instance : ToString CompileError where
  toString
    | .invalidProgram error => toString error
    | .duplicatePattern name => s!"duplicate field pattern in function '{name}'"

-- The lowering implementation is exposed here for compiler correctness proofs.
namespace Compiler

structure BuildState (F : Type) where
  nextVar : Nat
  constraints : Array (Constraint F) := #[]
  sends : Array (Send F) := #[]

abbrev Build (F : Type) := StateT (BuildState F) (Except CompileError)

def fresh : Build F Var := do
  let state ← get
  set { state with nextVar := state.nextVar + 1 }
  return state.nextVar

def constrain (polynomial : ArithExpr F) : Build F Unit :=
  modify fun state => { state with constraints := state.constraints.push polynomial }

def guarded (enable polynomial : ArithExpr F) : Build F Unit :=
  constrain (.mul enable polynomial)

def boolean [Field F] (selector : ArithExpr F) : Build F Unit :=
  constrain (.mul selector (.sub selector (.const 1)))

/-- Stop at the wildcard: any later arms are unreachable and are not lowered. -/
def literalPatterns : List (Pattern F × Expr F) → List F
  | [] => []
  | (.literal value, _) :: rest => value :: literalPatterns rest
  | (.wildcard, _) :: _ => []

def checkPatterns [DecidableEq F] (function : String) :
    List (Pattern F × Expr F) → List F → Except CompileError Unit
  | [], _ => pure ()
  | (.wildcard, _) :: _, _ => pure ()
  | (.literal value, _) :: rest, seen => do
      if value ∈ seen then throw (.duplicatePattern function)
      checkPatterns function rest (value :: seen)

/-- One product equation for each pair of distinct selector occurrences. -/
def exclusionConstraints : List (ArithExpr F) → List (Constraint F)
  | [] => []
  | selector :: rest => rest.map (ArithExpr.mul selector) ++ exclusionConstraints rest

def selectionConstraints [Field F] (parent : ArithExpr F)
    (selectors : List (ArithExpr F)) : List (Constraint F) :=
  selectors.map (fun selector => .mul selector (.sub selector (.const 1))) ++
    exclusionConstraints selectors ++
    [.sub (selectors.foldl ArithExpr.add (.const 0)) parent]

/-- Boolean selectors, pairwise exclusion, and exactly one when the parent is active. -/
def selectOne [Field F] (parent : ArithExpr F) (selectors : List (ArithExpr F)) :
    Build F Unit :=
  modify fun state => { state with
    constraints := state.constraints ++ (selectionConstraints parent selectors).toArray }

/-- A selected default excludes each explicit literal using a fresh inverse witness. -/
def excludeLiterals [Field F] (selector scrutinee : ArithExpr F) : List F → Build F Unit
  | [] => pure ()
  | value :: rest => do
      let inverse ← fresh
      guarded selector
        (.sub (.mul (.sub scrutinee (.const value)) (.var inverse)) (.const 1))
      excludeLiterals selector scrutinee rest

mutual
  def lowerExpr [Field F] [DecidableEq F] (function : String)
      (locals : List (String × Var)) (enable : ArithExpr F) (expr : Expr F) :
      Build F (ArithExpr F) := do
    match expr with
    | .literal value => return .const value
    | .var name =>
        let some (_, id) := locals.find? (·.1 == name)
          | throw (.invalidProgram (.unboundVariable function name))
        return .var id
    | .neg value => return .sub (.const 0) (← lowerExpr function locals enable value)
    | .binary op left right =>
        let left ← lowerExpr function locals enable left
        let right ← lowerExpr function locals enable right
        match op with
        | .add => return .add left right
        | .sub => return .sub left right
        | .mul => return .mul left right
        | .div =>
            let inverse ← fresh
            guarded enable (.sub (.mul right (.var inverse)) (.const 1))
            return .mul left (.var inverse)
    | .call name args =>
        let args ← lowerArgs function locals enable args
        let result ← fresh
        boolean enable
        modify fun state => { state with
          sends := state.sends.push ⟨name, args, result, enable⟩ }
        return .var result
    | .matchValue scrutinee arms =>
        checkPatterns function arms []
        let scrutinee ← lowerExpr function locals enable scrutinee
        let result ← fresh
        let selectors ← lowerArms function locals scrutinee result (literalPatterns arms) arms
        selectOne enable selectors
        return .var result
  termination_by sizeOf expr

  def lowerArgs [Field F] [DecidableEq F] (function : String)
      (locals : List (String × Var)) (enable : ArithExpr F) (args : List (Expr F)) :
      Build F (List (ArithExpr F)) := do
    match args with
    | [] => pure []
    | arg :: rest =>
        let arg ← lowerExpr function locals enable arg
        let rest ← lowerArgs function locals enable rest
        return arg :: rest
  termination_by sizeOf args

  def lowerArms [Field F] [DecidableEq F] (function : String)
      (locals : List (String × Var)) (scrutinee : ArithExpr F) (result : Var)
      (literals : List F) (arms : List (Pattern F × Expr F)) :
      Build F (List (ArithExpr F)) := do
    match arms with
    | [] => pure []
    | (pattern, body) :: rest =>
        let selector := ArithExpr.var (← fresh)
        match pattern with
        | .literal value => guarded selector (.sub scrutinee (.const value))
        | .wildcard =>
            excludeLiterals selector scrutinee literals
        let body ← lowerExpr function locals selector body
        guarded selector (.sub (.var result) body)
        match pattern with
        | .wildcard => return [selector]
        | .literal _ =>
            let rest ← lowerArms function locals scrutinee result literals rest
            return selector :: rest
  termination_by sizeOf arms
end

def lowerFunction [Field F] [DecidableEq F] (defn : Function F) :
    Except CompileError (Chip F) := do
  let arity := defn.params.length
  let output := arity
  let (body, state) ←
    (lowerExpr defn.name (defn.params.zip (List.range arity)) (.const 1) defn.body).run
      { nextVar := arity + 1 }
  return {
    name := defn.name
    arity
    output
    numVars := state.nextVar
    constraints := (state.constraints.push (.sub (.var output) body)).toList
    sends := state.sends.toList
  }

end Compiler

/--
Compile a field-specialized program to one chip per function. Calls remain channel sends,
so recursive definitions are never unfolded. Matching is validated in the chosen field.
-/
def compile [Field F] [DecidableEq F] (program : Program F) : Except CompileError (System F) := do
  match typecheck program with
  | .error error => throw (.invalidProgram error)
  | .ok () => pure ()
  return ⟨← program.functions.mapM Compiler.lowerFunction⟩

end Aiur.Scalar.Circuit
