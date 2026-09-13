import Lean
import Ix.Ixby

/-! Construction of ordinary Ixby functions. This module is used by the
experimental typed frontend; it makes no source-refinement claim. -/

namespace Compilatrix.Ixby.Runtime

open Lean
open Ix.Ixby

structure FunctionSlot where
  name : Name
  arity : Nat
  value : Option Function := none
  deriving Inhabited

structure BuildState where
  limits : Limits
  functions : Array FunctionSlot := #[]
  functionNames : Std.HashMap Name Nat := {}
  constructors : Array CtorDecl := #[]
  constructorNames : Std.HashMap Name Nat := {}
  pending : Array Name := #[]
  remaining : Nat := 1000000

abbrev BuildM := StateT BuildState (ExceptT String CoreM)

def reserveFunction (name : Name) (arity : Nat) : BuildM Nat := do
  let state ← get
  if let some id := state.functionNames[name]? then
    unless state.functions[id]!.arity == arity do throwThe String s!"conflicting arity for {name}"
    return id
  if state.functions.size ≥ state.limits.functions then throwThe String "typed Ixby function limit"
  if arity > state.limits.operands then throwThe String s!"typed Ixby arity limit: {name}: {arity}"
  let id := state.functions.size
  set { state with
    functions := state.functions.push { name, arity }
    functionNames := state.functionNames.insert name id }
  return id

def functionId (name : Name) : BuildM Nat := do
  let some id := (← get).functionNames[name]? | throwThe String s!"unregistered Ixby function {name}"
  return id

def constructor (name : Name) (fields : Nat) : BuildM Nat := do
  let state ← get
  if let some id := state.constructorNames[name]? then
    unless state.constructors[id]!.fields == fields do throwThe String s!"conflicting layout for {name}"
    return id
  if state.constructors.size ≥ state.limits.constructors then throwThe String "typed Ixby constructor limit"
  if fields > state.limits.operands then throwThe String s!"typed Ixby constructor field limit: {name}"
  let index := state.constructors.size
  let id : CtorId := { block := 1, member := 0, tag := index }
  set { state with
    constructors := state.constructors.push { id, fields }
    constructorNames := state.constructorNames.insert name index }
  return index

structure CodeState where
  blocks : Array (Option Block) := #[none]
  current : Nat := 0
  locals : Nat
  terminated : Bool := false

abbrev CodeM := StateT CodeState BuildM

def reserveBlock : CodeM Nat := do
  let state ← get
  if state.blocks.size ≥ (← getThe BuildState).limits.blocks then throwThe String "typed Ixby block limit"
  set { state with blocks := state.blocks.push none }
  return state.blocks.size

def terminate (instruction : Instr) : CodeM Unit := do
  let state ← get
  if state.terminated then throwThe String "Ixby builder: instruction after terminator"
  set { state with
    terminated := true
    blocks := state.blocks.set! state.current (some { locals := state.locals, instruction }) }

def enter (block locals : Nat) : CodeM Unit :=
  modify fun state => { state with current := block, locals, terminated := false }

def emit (operation : Op) : CodeM Operand := do
  let locals := (← get).locals
  if locals ≥ (← getThe BuildState).limits.locals then throwThe String "typed Ixby local limit"
  let next ← reserveBlock
  terminate (.letOp operation next)
  enter next (locals + 1)
  return .local locals

def ret (value : Operand) : CodeM Unit := terminate (.ret value)

def trap : CodeM Unit := terminate (.caseCtor .erased [])

def primitive (operation : Primitive) (args : List Operand) : CodeM Operand :=
  emit (.primitive operation args)

def call (name : Name) (args : List Operand) : CodeM Operand := do
  emit (.call (← functionId name) args)

def tailCall (name : Name) (args : List Operand) : CodeM Unit := do
  terminate (.tailCall (← functionId name) args)

def make (name : Name) (fields : List Operand) : CodeM Operand := do
  emit (.construct (← constructor name fields.length) fields)

def project (value : Operand) (field : Nat) : CodeM Operand := emit (.project value field)

def branch (condition : Operand) (ifTrue ifFalse : CodeM Unit) : CodeM Unit := do
  let locals := (← get).locals
  let yes ← reserveBlock
  let no ← reserveBlock
  terminate (.branch condition yes no)
  enter yes locals
  ifTrue
  unless (← get).terminated do throwThe String "Ixby builder: unterminated true branch"
  enter no locals
  ifFalse
  unless (← get).terminated do throwThe String "Ixby builder: unterminated false branch"

def caseCtor (value : Operand) (alternatives : Array (Name × Nat × (Array Operand → CodeM Unit))) :
    CodeM Unit := do
  let locals := (← get).locals
  let mut branches := #[]
  let mut blocks := #[]
  for (name, fields, _) in alternatives do
    let id ← constructor name fields
    let block ← reserveBlock
    branches := branches.push { ctor := id, target := block : Alternative }
    blocks := blocks.push block
  terminate (.caseCtor value branches.toList)
  for i in [:alternatives.size] do
    let (_, fields, body) := alternatives[i]!
    enter blocks[i]! (locals + fields)
    body ((Array.range fields).map fun field => Operand.local (locals + field))
    unless (← get).terminated do throwThe String "Ixby builder: unterminated constructor branch"

def defineFunction (name : Name) (arity : Nat) (body : CodeM Unit) : BuildM Nat := do
  let id ← reserveFunction name arity
  let (_, state) ← body.run { locals := arity }
  unless state.terminated do throwThe String s!"unterminated Ixby function {name}"
  let blocks ← state.blocks.mapM fun block => do
    let some block := block | throwThe String s!"unfilled Ixby block in {name}"
    return block
  modify fun state => { state with functions := state.functions.modify id fun slot =>
    { slot with value := some { arity, blocks } } }
  return id

def finishProgram (entry : Nat) : BuildM Program := do
  let state ← get
  let functions ← state.functions.mapM fun slot => do
    let some fn := slot.value | throwThe String s!"unfilled Ixby function {slot.name}"
    return fn
  let program : Program := { entry, functions, constructors := state.constructors }
  match validateProgram state.limits program with
  | .error error => throwThe String s!"typed Ixby image validation: {reprStr error}"
  | .ok () => return program

def rawNat (n : Nat) : Operand := .literal (.nat n)
def word (n : Nat) : Operand := .literal (.word32 n.toUInt32)
def boolean (b : Bool) : Operand := .literal (.bool b)

def number (value : Nat) : CodeM Operand :=
  make `Ixby.Runtime.Number [rawNat value, word value]

def lowWord (value : Operand) : CodeM Operand := call `Ixby.Runtime.lowWord [value]

def numberParts (value : Operand) : CodeM (Operand × Operand) := do
  return (← project value 0, ← lowWord value)

def packedBytes (bytes : Array UInt8) : CodeM Operand := do
  make `Ixby.Runtime.Bytes [.literal (.bytes bytes), ← number bytes.size]

end Compilatrix.Ixby.Runtime
