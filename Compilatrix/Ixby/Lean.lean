import Compilatrix.Ixby.Runtime.Array
import Compilatrix.Ixby.Runtime.Field

/-! Experimental lowering of Lean's pure monomorphic LCNF to the Ixby
reference machine. Lean performs typed proof erasure and specialization.
Neither those passes nor this frontend have a source-refinement certificate.
The certified Ixon pipeline does not use this entry point. -/

namespace Compilatrix.Ixby.LeanFrontend

open Lean Lean.Compiler Ix.Ixby _root_.Compilatrix.Ixby.Runtime

private abbrev Locals := Array (FVarId × Operand)

private def lookup (locals : Locals) (id : FVarId) : CodeM Operand := do
  let some (_, value) := locals.findRev? (·.1 == id) |
    throwThe String s!"typed Ixby unbound local {id.name}"
  return value

private def argument (locals : Locals) : LCNF.Arg .pure → CodeM Operand
  | .fvar id => lookup locals id
  | .erased | .type .. => pure .erased

private def arguments (locals : Locals) (args : Array (LCNF.Arg .pure)) : CodeM (List Operand) :=
  args.toList.mapM (argument locals)

private def applyNamed (name : Name) (arity : Nat) (args : List Operand) : CodeM Operand := do
  let id ← functionId name
  if args.length < arity then emit (.closure id args)
  else
    let value ← emit (.call id (args.take arity))
    if args.length == arity then return value
    emit (.apply value (args.drop arity))

private def ensureFunction (name : Name) : BuildM Nat := do
  if let some id := (← get).functionNames[name]? then return (← get).functions[id]!.arity
  let env ← getEnv
  if let some (.ctorInfo info) := env.find? name then
    let arity := info.numParams + info.numFields
    discard <| defineFunction name arity do
      if name == ``Bool.false then ret (boolean false)
      else if name == ``Bool.true then ret (boolean true)
      else if name == ``Nat.zero then ret (← number 0)
      else if name == ``Nat.succ then tailCall `Nat.add [.local 0, ← number 1]
      else
        ret (← make name ((List.range info.numFields).map fun i => .local (info.numParams + i)))
    return arity
  let some decl ← LCNF.getMonoDecl? name |
    throwThe String s!"no typed runtime declaration for {name}"
  match decl.value with
  | .extern .. => throwThe String s!"unsupported typed runtime extern {name}"
  | .code .. => pure ()
  discard <| reserveFunction name decl.params.size
  modify fun state => { state with pending := state.pending.push name }
  return decl.params.size

private structure Join where
  name : Name
  captures : Array FVarId

private abbrev Joins := Array (FVarId × Join)

private def paramsLocals (params : Array (LCNF.Param .pure)) (start : Nat := 0) : Locals :=
  params.mapIdx fun i param => (param.fvarId, .local (start + i))

private def spend : CodeM Unit := do
  let state ← getThe BuildState
  if state.remaining == 0 then throwThe String "typed Ixby compiler work limit"
  modifyThe BuildState fun _ => { state with remaining := state.remaining - 1 }

private def letValue (locals : Locals) : LCNF.LetValue .pure → CodeM Operand
  | .erased => pure .erased
  | .lit literal => match literal with
    | .nat n => number n
    | .str s => packedBytes s.toUTF8.data
    | .uint8 n => pure (word n.toNat)
    | .uint16 n => pure (word n.toNat)
    | .uint32 n => pure (word n.toNat)
    | .uint64 n | .usize n => number n.toNat
  | .proj name field value _ => do
    let value ← lookup locals value
    if let some getters := (← getThe BuildState).projections[name]? then
      let some getter := getters[field]? | throwThe String s!"unsupported scalar projection {name}.{field}"
      call getter [value]
    else project value field
  | .fvar value args => do
    let value ← lookup locals value
    if args.isEmpty then return value
    emit (.apply value (← arguments locals args))
  | .const name _ args _ => do
    let arity ← ensureFunction name
    applyNamed name arity (← arguments locals args)

private def tailValue (locals : Locals) (value : LCNF.LetValue .pure) : CodeM Unit := do
  match value with
  | .const name _ args _ =>
    let arity ← ensureFunction name
    let args ← arguments locals args
    if args.length == arity then tailCall name args
    else if args.length > arity then
      let first ← call name (args.take arity)
      terminate (.tailApply first (args.drop arity))
    else ret (← applyNamed name arity args)
  | .fvar fn args =>
    let fn ← lookup locals fn
    if args.isEmpty then ret fn else terminate (.tailApply fn (← arguments locals args))
  | _ => ret (← letValue locals value)

private def findAlt (alternatives : Array (LCNF.Alt .pure)) (name : Name) :
    Option (Array (LCNF.Param .pure) × LCNF.Code .pure) :=
  (alternatives.findSome? fun alt => match alt with
    | .alt ctor params body _ => if ctor == name then some (params, body) else none
    | _ => none).orElse fun _ => alternatives.findSome? fun alt => match alt with
      | .default body => some (#[], body)
      | _ => none

mutual
  private def code : Nat → Locals → Joins → LCNF.Code .pure → CodeM Unit
    | 0, _, _, _ => throwThe String "typed Ixby expression depth limit"
    | fuel + 1, locals, joins, body => do
      spend
      match body with
      | .let decl next =>
        if let .return returned := next then
          if returned == decl.fvarId then
            tailValue locals decl.value
            return
        let value ← letValue locals decl.value
        code fuel (locals.push (decl.fvarId, value)) joins next
      | .return value => ret (← lookup locals value)
      | .unreach _ => trap
      | .jmp name args =>
        let some (_, join) := joins.findRev? (·.1 == name) |
          throwThe String s!"typed Ixby unbound join {name.name}"
        let captures ← join.captures.toList.mapM (lookup locals)
        tailCall join.name (captures ++ (← arguments locals args))
      | .jp decl next =>
        let join ← liftLocal fuel locals joins decl true
        code fuel locals (joins.push (decl.fvarId, join)) next
      | .fun decl next _ =>
        let lifted ← liftLocal fuel locals joins decl false
        let captures ← lifted.captures.toList.mapM (lookup locals)
        let value ← applyNamed lifted.name (captures.length + decl.params.size) captures
        code fuel (locals.push (decl.fvarId, value)) joins next
      | .cases cases =>
        let value ← lookup locals cases.discr
        if cases.typeName == ``Bool then
          let some (_, no) := findAlt cases.alts ``Bool.false |
            throwThe String "typed Ixby missing false branch"
          let some (_, yes) := findAlt cases.alts ``Bool.true |
            throwThe String "typed Ixby missing true branch"
          branch value (code fuel locals joins yes) (code fuel locals joins no)
        else if cases.typeName == ``Nat then
          let some (_, zero) := findAlt cases.alts ``Nat.zero |
            throwThe String "typed Ixby missing zero branch"
          let some (params, succ) := findAlt cases.alts ``Nat.succ |
            throwThe String "typed Ixby missing successor branch"
          let count := (← get).locals
          let zeroBlock ← reserveBlock
          let succBlock ← reserveBlock
          terminate (.caseNat value zeroBlock succBlock)
          enter zeroBlock count
          code fuel locals joins zero
          enter succBlock (count + 1)
          let pred := Operand.local count
          let locals := if params.isEmpty then locals else locals.push (params[0]!.fvarId, pred)
          code fuel locals joins succ
        else
          let some (.inductInfo info) := (← getEnv).find? cases.typeName |
            throwThe String s!"typed Ixby unknown case type {cases.typeName}"
          if let some getters := (← getThe BuildState).projections[cases.typeName]? then
            let [ctor] := info.ctors | throwThe String "scalar layout requires one constructor"
            let some (params, body) := findAlt cases.alts ctor |
              throwThe String s!"typed Ixby missing scalar branch {ctor}"
            unless params.isEmpty || params.size == getters.size do
              throwThe String s!"typed Ixby scalar case field count {ctor}"
            let mut captured := locals
            for i in [:params.size] do
              captured := captured.push (params[i]!.fvarId, ← call getters[i]! [value])
            code fuel captured joins body
            return
          let mut alternatives := #[]
          for name in info.ctors do
            let some (.ctorInfo ctor) := (← getEnv).find? name |
              throwThe String s!"typed Ixby missing constructor {name}"
            if let some (params, body) := findAlt cases.alts name then
              if !params.isEmpty && params.size != ctor.numFields then
                throwThe String s!"typed Ixby case field count for {name}: {params.size}/{ctor.numFields}"
              alternatives := alternatives.push (name, ctor.numFields, fun fields =>
                code fuel (locals ++ (params.mapIdx fun i p => (p.fvarId, fields[i]!))) joins body)
          caseCtor value alternatives

  private def liftLocal (fuel : Nat) (locals : Locals) (joins : Joins)
      (decl : LCNF.FunDecl .pure) (isJoin : Bool) : CodeM Join := do
    let count := (← getThe BuildState).functions.size
    let name := Name.num `Ixby.Runtime.Lifted count
    let captured := locals.map (·.1)
    let join := { name, captures := captured : Join }
    let liftedLocals := (captured.mapIdx fun i fvar => (fvar, Operand.local i)) ++
      paramsLocals decl.params captured.size
    let liftedJoins := if isJoin then joins.push (decl.fvarId, join) else joins
    discard <| defineFunction name (captured.size + decl.params.size)
      (code fuel liftedLocals liftedJoins decl.value)
    return join
end

structure Image where
  program : Program
  state : BuildState
  sourceEntry : Name

/-- This API deliberately returns no source certificate. It cannot be used as
an `IxonCompilation` or as a Stage2 byte-execution refinement. -/
def compile (entry : Name) (limits : Limits := {}) (depth : Nat := 10000)
    (setup : BuildM Unit := pure ()) : CoreM (Except String Image) := do
  if limits.byteArrayBytes ≥ 2 ^ 32 then
    return .error "typed Ixby packed byte capacity must fit Word32 indices"
  let build : BuildM Program := do
    buildNumbers
    buildArrays
    buildFields
    setup
    discard <| ensureFunction entry
    let mut next := 0
    while next < (← get).pending.size do
      let name := (← get).pending[next]!
      next := next + 1
      let some decl ← LCNF.getMonoDecl? name | throwThe String s!"lost typed declaration {name}"
      let .code body := decl.value | throwThe String s!"unexpected runtime extern {name}"
      discard <| defineFunction name decl.params.size (code depth (paramsLocals decl.params) #[] body)
    finishProgram (← functionId entry)
  let result ← (build.run { limits }).run
  return result.map fun (program, state) => { program, state, sourceEntry := entry }

def Image.ctorId (image : Image) (name : Name) : Except String CtorId := do
  let some index := image.state.constructorNames[name]? | throw s!"missing output layout {name}"
  return image.program.constructors[index]!.id

def Image.number (_image : Image) (n : Nat) : Except String Value :=
  .ok (.scalar (.nat n))

def Image.word (_image : Image) (word : UInt32) : Value := .scalar (.word32 word)

def Image.bytes (image : Image) (bytes : Array UInt8) : Except String Value := do
  return .ctor (← image.ctorId `Ixby.Runtime.Bytes) #[.scalar (.bytes bytes), ← image.number bytes.size]

def Image.decodeNumber (_image : Image) : Value → Except String Nat
  | .scalar (.nat n) => .ok n
  | _ => .error "typed Ixby output is not a Nat scalar"

def Image.decodeWord (_image : Image) : Value → Except String UInt32
  | .scalar (.word32 word) => .ok word
  | _ => .error "typed Ixby output is not a Word32 scalar"

end Compilatrix.Ixby.LeanFrontend
