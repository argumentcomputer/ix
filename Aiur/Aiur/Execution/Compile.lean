import Aiur.Execution.Bytecode
import Aiur.Runtime
import Aiur.Generic.Specialize
import Aiur.Generic.Circuit
import Aiur.Inlining.Program
import Aiur.Modules.Link

namespace Aiur.Execution

namespace Compiler

abbrev Value := WireValue Register
abbrev Locals := List (String × Value)

structure State (F : Type) where
  registers : Nat := 0
  code : Array (Instruction F) := #[]

abbrev Build (F : Type) := StateT (State F) (Except String)

def need (value : Option α) (message : String) : Except String α :=
  match value with | some x => .ok x | none => .error message

def emit (instruction : Instruction F) : Build F Nat := do
  let state ← get
  set { state with code := state.code.push instruction }
  return state.code.size

def patch (pc : Nat) (instruction : Instruction F) : Build F Unit := do
  let state ← get
  if pc ≥ state.code.size then throw "invalid bytecode patch"
  set { state with code := state.code.set! pc instruction }

def fresh (type : Ty) (decls : Declarations) : Build F Value := do
  let layout ← liftM ((decls.layout type).mapError reprStr)
  let start := (← get).registers
  modify fun state => { state with registers := start + layout.width }
  return ⟨type, (List.range layout.width).map (start + ·)⟩

def scalar (value : Value) : Except String Register :=
  match value.words with
  | [word] => return word
  | _ => throw "expected one execution register"

def split (decls : Declarations) : List Ty → List Register → Except String (List Value)
  | [], [] => return []
  | type :: types, words => do
      let layout ← (decls.layout type).mapError reprStr
      if words.length < layout.width then throw "short execution value"
      return ⟨type, words.take layout.width⟩ :: (← split decls types (words.drop layout.width))
  | [], _ :: _ => throw "long execution value"

mutual
  def pattern [NatCast F] (decls : Declarations) (pat : Pattern F) (value : Value) :
      Except String (List (Register × F) × Locals) := do
    match pat with
    | .wildcard => return ([], [])
    | .bind name => return ([], [(name, value)])
    | .literal constant => return ([(← scalar value, constant)], [])
    | .tuple items =>
        let .tuple types := value.type | throw "tuple pattern on non-tuple"
        patterns decls items (← split decls types value.words)
    | .construct name ctor args =>
        let some decl := decls.findEnum? name | throw s!"unknown enum {name}"
        let some constructor := decls.findConstructor? name ctor | throw s!"unknown constructor {ctor}"
        let layout ← (decls.layout (.tuple constructor.fields)).mapError reprStr
        let tagged := decl.constructors.length > 1
        let tests := if tagged then
          [(value.words.headD 0, (decl.constructors.findIdx (·.name == ctor) : F))]
          else []
        let payload := (value.words.drop (if tagged then 1 else 0)).take layout.width
        let (more, bindings) ← patterns decls args (← split decls constructor.fields payload)
        return (tests ++ more, bindings)
  termination_by sizeOf pat

  def patterns [NatCast F] (decls : Declarations) (pats : List (Pattern F))
      (values : List Value) : Except String (List (Register × F) × Locals) := do
    match pats, values with
    | [], [] => return ([], [])
    | pat :: pats, value :: values =>
        let (tests, bindings) ← pattern decls pat value
        let (rest, locals) ← patterns decls pats values
        return (tests ++ rest, bindings ++ locals)
    | _, _ => throw "execution pattern arity mismatch"
  termination_by sizeOf pats
end

def callable (program : Aiur.Program F) (name : String) : Except String Nat := do
  let names := program.functions.map (·.name) ++ program.maps.map (·.name)
  if !names.contains name then throw s!"unknown callable {name}"
  return names.idxOf name

mutual
  def expression [NatCast F] [Zero F] (program : Aiur.Program F) (caller : String)
      (locals : Locals) (expr : Expr F) : Build F Value := do
    let type ← liftM ((inferType program caller (locals.map fun (n, v) => (n, v.type)) expr).mapError reprStr)
    match expr with
    | .var name =>
        let some (_, value) := locals.find? (·.1 == name) | throw s!"unbound register {name}"
        return value
    | .literal constant =>
        let value ← fresh .field program.enums
        let _ ← emit (.literal (← liftM (scalar value)) constant)
        return value
    | .tuple items => return WireValue.tuple (← expressions program caller locals items)
    | .construct name ctor args =>
        let values ← expressions program caller locals args
        let some decl := program.enums.findEnum? name | throw s!"unknown enum {name}"
        let result ← fresh type program.enums
        let tagged := decl.constructors.length > 1
        let payload := values.flatMap (·.words)
        if tagged then
          let _ ← emit (.literal (← liftM (need result.words.head? "missing enum tag"))
            (decl.constructors.findIdx (·.name == ctor) : F))
        let dest := result.words.drop (if tagged then 1 else 0)
        let _ ← emit (.copy (dest.take payload.length) payload)
        for reg in dest.drop payload.length do let _ ← emit (.literal reg 0)
        return result
    | .project expr index =>
        let value ← expression program caller locals expr
        let .tuple types := value.type | throw "projection on non-tuple"
        let values ← liftM (split program.enums types value.words)
        liftM (need values[index]? "projection out of bounds")
    | .letValue pat value body =>
        let value ← expression program caller locals value
        let (tests, bindings) ← liftM (pattern program.enums pat value)
        let _ ← emit (.guard tests "let pattern mismatch")
        expression program caller (bindings ++ locals) body
    | .neg expr =>
        let value ← expression program caller locals expr
        let result ← fresh type program.enums
        let _ ← emit (.neg (← liftM (scalar result)) (← liftM (scalar value)))
        return result
    | .binary op left right =>
        let left ← expression program caller locals left
        let right ← expression program caller locals right
        let result ← fresh type program.enums
        let _ ← emit (.binary (← liftM (scalar result)) op (← liftM (scalar left)) (← liftM (scalar right)))
        return result
    | .assertEq message left right =>
        let left ← expression program caller locals left
        let right ← expression program caller locals right
        let _ ← emit (.assertEq left.words right.words message)
        return ⟨.tuple [], []⟩
    | .call name args =>
        let values ← expressions program caller locals args
        let result ← fresh type program.enums
        let _ ← emit (.call (← liftM (callable program name)) (values.flatMap (·.words)) result.words)
        return result
    | .store expr =>
        let value ← expression program caller locals expr
        let result ← fresh type program.enums
        let _ ← emit (.store value.type value.words (← liftM (scalar result)))
        return result
    | .load expr =>
        let pointer ← expression program caller locals expr
        let result ← fresh type program.enums
        let _ ← emit (.load type (← liftM (scalar pointer)) result.words)
        return result
    | .hint type key channel =>
        let key ← expression program caller locals key
        let result ← fresh type program.enums
        let _ ← emit (.hint type key.type key.words result.words channel)
        return result
    | .matchValue scrutinee arms =>
        let value ← expression program caller locals scrutinee
        let result ← fresh type program.enums
        let exits ← branches program caller locals value result arms
        let _ ← emit (.fail "no matching arm")
        let target := (← get).code.size
        for exit in exits do patch exit (.jump target)
        return result
  termination_by sizeOf expr

  def expressions [NatCast F] [Zero F] (program : Aiur.Program F) (caller : String)
      (locals : Locals) (items : List (Expr F)) : Build F (List Value) := do
    match items with
    | [] => return []
    | item :: items =>
        let value ← expression program caller locals item
        return value :: (← expressions program caller locals items)
  termination_by sizeOf items

  def branches [NatCast F] [Zero F] (program : Aiur.Program F) (caller : String)
      (locals : Locals) (value result : Value) (arms : List (Pattern F × Expr F)) : Build F (List Nat) := do
    match arms with
    | [] => return []
    | (pat, body) :: arms =>
        let (tests, bindings) ← liftM (pattern program.enums pat value)
        let branch ← emit (.branch tests 0)
        let output ← expression program caller (bindings ++ locals) body
        let _ ← emit (.copy result.words output.words)
        let exit ← emit (.jump 0)
        patch branch (.branch tests (← get).code.size)
        return exit :: (← branches program caller locals value result arms)
  termination_by sizeOf arms
end

def function [NatCast F] [Zero F] (program : Aiur.Program F) (fn : Aiur.Function F) :
    Except String (Function F) := do
  let build : Build F Unit := do
    let inputs ← fn.params.mapM fun (name, type) => return (name, ← fresh type program.enums)
    let result ← expression program fn.name inputs fn.body
    let _ ← emit (.ret result.words)
  let (_, state) ← build.run {}
  return ⟨fn.name, fn.params.map Prod.snd, fn.result, state.registers, state.code⟩

end Compiler

/-- Executor compilation changes neither the source predicate nor the circuit
compiler. No circuit data or circuit layout is exported here. -/
def compile [NatCast F] [Zero F] [DecidableEq F] (program : Aiur.Program F)
    (entries : List String) : Except String (Bytecode F) := do
  let _ ← (typecheck program).mapError reprStr
  if !program.enums.tagsValid F then throw "enum tags collide in the execution field"
  for entry in entries do let _ ← (checkEntry program entry).mapError reprStr
  let functions ← program.functions.mapM (Compiler.function program)
  let tables ← program.tables.mapM fun table => do
    let layout ← (program.enums.layout table.rowType).mapError reprStr
    let rows ← table.rows.mapM fun row =>
      Compiler.need (layout.encode row.toValue) s!"cannot encode table {table.name}"
    return ⟨table.name, table.rowType, rows⟩
  let tableNames := program.tables.map (·.name)
  let maps := program.maps.map fun map =>
    ⟨map.name, map.params.map Prod.snd, map.result, tableNames.idxOf map.input, tableNames.idxOf map.output⟩
  let entries ← entries.mapM fun name => return (name, ← Compiler.callable program name)
  return ⟨functions, program.enums, tables, maps, entries⟩

end Aiur.Execution

namespace Aiur.Modules

/-- Reuse source preparation, specialization and mandatory inlining. -/
def Prepared.compileExecution [NatCast F] [Zero F] [DecidableEq F]
    (prepared : Prepared (program : Program F)) : Except String (Execution.Bytecode F) := do
  let specialized ← Generic.specialize prepared.environment.source prepared.entries
  let inlined ← Inlining.prepare specialized.program specialized.inlineNames prepared.entries
  let code ← Execution.compile inlined.program prepared.entries
  let entries ← prepared.selections.mapM fun entry => do
    return (entry.external, ← Execution.Compiler.callable inlined.program entry.resolved.name)
  return { code with entries }

end Aiur.Modules
