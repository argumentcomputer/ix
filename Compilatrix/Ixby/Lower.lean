import Compilatrix.Ixby.Basic

/-! Closure conversion and explicit curried calls. No evaluator is called by
the compiler. Every emitted image passes the upstream whole-program validator. -/

namespace Compilatrix.Ixby

open Ixon (Address)
open Ix.Ixby (Operand Function Block Op Instr)

private structure Global where
  decl : IxIR0.Decl
  stages : Array Nat
  constructor : Nat := 0

private structure State where
  source : Source
  config : Config
  functions : Array (Option Function) := #[]
  globals : Std.HashMap Address Global := {}
  projections : Std.HashMap Nat Nat := {}
  remaining : Nat

private abbrev M := StateT State (Except String)

private def spend : M Unit := do
  let state ← get
  if state.remaining == 0 then throw "Ixby compiler work limit"
  set { state with remaining := state.remaining - 1 }

private def reserve : M Nat := do
  spend
  let state ← get
  if state.functions.size ≥ state.config.limits.functions then
    throw "Ixby function count limit"
  set { state with functions := state.functions.push none }
  return state.functions.size

private def finish (id : Nat) (fn : Function) : M Unit := do
  let state ← get
  if fn.blocks.size > state.config.limits.blocks then throw "Ixby block count limit"
  modify fun state => { state with functions := state.functions.set! id (some fn) }

private structure Code where
  blocks : Array Block := #[]
  locals : Nat

private def Code.emit (code : Code) (op : Op) : M (Operand × Code) := do
  spend
  let limits := (← get).config.limits
  if code.locals ≥ limits.locals then throw "Ixby local count limit"
  if code.blocks.size ≥ limits.blocks then throw "Ixby block count limit"
  return (.local code.locals, {
    blocks := code.blocks.push { locals := code.locals, instruction := .letOp op (code.blocks.size + 1) }
    locals := code.locals + 1 })

private def Code.ret (code : Code) (operand : Operand) : Code :=
  { code with blocks := code.blocks.push { locals := code.locals, instruction := .ret operand } }

private def locals (count : Nat) : List Operand := (List.range count).map .local

private def boxFunction (code : Code) (id : Nat) (captured : List Operand) :
    M (Operand × Code) := do
  let (raw, code) ← code.emit (.closure id captured)
  code.emit (.construct 3 [raw])

private def projection (field : Nat) : M Nat := do
  if let some id := (← get).projections[field]? then return id
  let id ← reserve
  let mut blocks : Array Block := #[{ locals := 1, instruction := .ret (.local 0) }]
  let mut alternatives := []
  let source := (← get).source
  for i in [:source.constructors.size] do
    spend
    let ctor := source.constructors[i]!
    if field < ctor.fields then
      alternatives := alternatives ++ [{ ctor := i + 4, target := blocks.size }]
      blocks := blocks.push { locals := 1 + ctor.fields, instruction := .ret (.local (1 + field)) }
  let erased := blocks.size
  blocks := blocks.push { locals := 1, instruction := .ret (.local 0) }
  blocks := blocks.set! 0 { locals := 1, instruction := .caseCtor (.local 0) ({ ctor := 0, target := erased } :: alternatives) }
  finish id { arity := 1, blocks }
  modify fun state => { state with projections := state.projections.insert field id }
  return id

private def expression : Nat → List Operand → Code → IxIR0.Expr → M (Operand × Code)
  | 0, _, _, _ => throw "Ixby expression depth limit"
  | fuel + 1, env, code, expr => do
    spend
    match expr with
    | .var index =>
        let some operand := env[index]? | throw s!"Ixby unbound variable {index}"
        return (operand, code)
    | .erased => code.emit (.construct 0 [])
    | .lit literal =>
        if (← get).config.proving then throw "Ixby proving profile excludes Nat/String literals"
        match literal with
        | .nat n => code.emit (.construct 1 [.literal (.nat n)])
        | .str s => code.emit (.construct 2 [.literal (.str s)])
    | .ref address =>
        let some global := (← get).globals[address]? |
          throw s!"Ixby unknown reference {address}"
        let id := global.stages[0]!
        match global.decl with
        | .defn .. | .ctor _ 0 => code.emit (.call id [])
        | _ => boxFunction code id []
    | .lam _ body =>
        let id ← reserve
        let captures := env.length
        let (value, inner) ← expression fuel
          (.local captures :: locals captures) { locals := captures + 1 } body
        finish id { arity := captures + 1, blocks := (inner.ret value).blocks }
        boxFunction code id env
    | .letE _ value body =>
        let (value, code) ← expression fuel env code value
        expression fuel (value :: env) code body
    | .app fn arg =>
        let (fn, code) ← expression fuel env code fn
        let (arg, code) ← expression fuel env code arg
        code.emit (.call 1 [fn, arg])
    | .proj field value =>
        let (value, code) ← expression fuel env code value
        let id ← projection field
        code.emit (.call id [value])

private def rule (global : Global) (arity : Nat) (fields : List Operand)
    (code : Code) (rhs : IxIR0.Expr) : M Code := do
  let (self, code) ← boxFunction code global.stages[0]! []
  let env := fields.reverse ++ (locals (arity - 1)).reverse ++ [self]
  let (value, code) ← expression (← get).config.depth env code rhs
  return code.ret value

private def recursor (global : Global) (numArgs : Nat) (natLit : Bool)
    (rules : Array IxIR0.RecRule) : M Function := do
  let arity := numArgs + 1
  let mut blocks : Array Block := #[{ locals := arity, instruction := .ret .erased }]
  let mut alternatives := []
  let source := (← get).source
  for i in [:source.constructors.size] do
    spend
    let ctor := source.constructors[i]!
    if let some branch := rules[ctor.tag]? then
      if branch.fields == ctor.fields then
        alternatives := alternatives ++ [{ ctor := i + 4, target := blocks.size }]
        let fields := (List.range ctor.fields).map (fun i => Operand.local (arity + i))
        let code ← rule global arity fields { blocks, locals := arity + ctor.fields } branch.rhs
        blocks := code.blocks
  if natLit && !(← get).config.proving then
    alternatives := alternatives ++ [{ ctor := 1, target := blocks.size }]
    let natCase := blocks.size
    blocks := blocks.push { locals := arity + 1, instruction := .ret .erased }
    let zeroBlock := blocks.size
    if let some branch := rules[0]? then
      if branch.fields == 0 then
        blocks := (← rule global arity [] { blocks, locals := arity + 1 } branch.rhs).blocks
      else
        blocks := blocks.push { locals := arity + 1, instruction := .caseCtor .erased [] }
    else
      blocks := blocks.push { locals := arity + 1, instruction := .caseCtor .erased [] }
    let succ := blocks.size
    if let some branch := rules[1]? then
      if branch.fields == 1 then
        let (pred, code) ← Code.emit { blocks, locals := arity + 2 }
          (.construct 1 [.local (arity + 1)])
        blocks := (← rule global arity [pred] code branch.rhs).blocks
      else
        blocks := blocks.push { locals := arity + 2, instruction := .caseCtor .erased [] }
    else
      blocks := blocks.push { locals := arity + 2, instruction := .caseCtor .erased [] }
    blocks := blocks.set! natCase { locals := arity + 1, instruction := .caseNat (.local arity) zeroBlock succ }
  blocks := blocks.set! 0 { locals := arity, instruction := .caseCtor (.local numArgs) alternatives }
  return { arity, blocks }

private def globalBody (global : Global) : M Unit := do
  match global.decl with
  | .extern _ => throw "Ixby backend rejects extern declarations"
  | .defn _ body =>
      let (value, code) ← expression (← get).config.depth [] { locals := 0 } body
      finish global.stages[0]! { arity := 0, blocks := (code.ret value).blocks }
  | .ctor _ arity =>
      for stage in [:global.stages.size] do
        let supplied := if arity == 0 then 0 else stage + 1
        let code : Code := { locals := supplied }
        let (value, code) ← if supplied == arity then
            code.emit (.construct global.constructor (locals supplied))
          else boxFunction code global.stages[stage + 1]! (locals supplied)
        finish global.stages[stage]! { arity := supplied, blocks := (code.ret value).blocks }
  | .recursor numArgs natLit rules =>
      for stage in [:numArgs] do
        let supplied := stage + 1
        let (value, code) ← boxFunction { locals := supplied }
          global.stages[stage + 1]! (locals supplied)
        finish global.stages[stage]! { arity := supplied, blocks := (code.ret value).blocks }
      finish global.stages[numArgs]! (← recursor global numArgs natLit rules)

private def build : M Ix.Ixby.Program := do
  let source := (← get).source
  let limits := (← get).config.limits
  if source.parameters > limits.operands then throw "Ixby entry arity limit"
  if source.constructors.size + 4 > limits.constructors then throw "Ixby constructor count limit"
  let _ ← reserve -- entry
  let _ ← reserve -- curried apply, always exactly one argument
  finish 1 { arity := 2, blocks := #[
    { locals := 2, instruction := .caseCtor (.local 0) [{ ctor := 3, target := 1 }, { ctor := 0, target := 2 }] },
    { locals := 3, instruction := .tailApply (.local 2) [.local 1] },
    { locals := 2, instruction := .ret (.local 0) }] }
  let mut ctorIndex := 4
  for (address, decl) in source.declarations do
    spend
    if (← get).globals.contains address then throw s!"Ixby duplicate declaration {address}"
    let arity ← match decl with
      | .defn .. => pure 0
      | .ctor _ arity => pure arity
      | .recursor pre .. => pure (pre + 1)
      | .extern _ => throw "Ixby backend rejects extern declarations"
    if arity > limits.operands then throw "Ixby global arity limit"
    let mut stages := #[]
    for _ in [:max arity 1] do stages := stages.push (← reserve)
    let global : Global := { decl, stages, constructor := ctorIndex }
    modify fun state => { state with globals := state.globals.insert address global }
    if let .ctor .. := decl then ctorIndex := ctorIndex + 1
  for (address, _) in source.declarations do
    let some global := (← get).globals[address]? | throw "Ixby internal global table error"
    globalBody global
  let (value, code) ← expression (← get).config.depth (locals source.parameters).reverse
    { locals := source.parameters } source.main
  finish 0 { arity := source.parameters, blocks := (code.ret value).blocks }
  let functions ← (← get).functions.mapM fun fn =>
    match fn with
    | some fn => pure fn
    | none => throw "Ixby internal unfinished function"
  return { functions, constructors := constructorTable source }

/-- Actual code generation, independent of source and target execution. -/
def lower (source : Source) (config : Config := {}) : Except String Ix.Ixby.Program := do
  let (program, _) ← build.run { source, config, remaining := config.work }
  return program

structure Compiled (source : Source) (config : Config) where
  program : Ix.Ixby.Program
  lowered : lower source config = .ok program
  admitted : Ix.Ixby.validateProgram config.limits program = .ok ()

def compile (source : Source) (config : Config := {}) : Except String (Compiled source config) := do
  match lowered : lower source config with
  | .error message => throw message
  | .ok program =>
    match admitted : Ix.Ixby.validateProgram config.limits program with
    | .error error => throw s!"Ixby image validation: {reprStr error}"
    | .ok () => return { program, lowered, admitted }

def Compiled.execute {source config} (compiled : Compiled source config)
    (input : Array Data := #[]) (fuel : Nat := 1000000) : Except String Ix.Ixby.Value := do
  if input.size != source.parameters then throw "Ixby input arity mismatch"
  admitData config.limits config.limits.inputNodes input.toList
  let input ← input.mapM (encodeData source config config.depth)
  (Ix.Ixby.execute config.limits compiled.program input fuel).mapError reprStr

end Compilatrix.Ixby
