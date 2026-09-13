import Compilatrix.Ixby.Basic

/-! Symbolic execution of the unchanged Ixby reference machine. Runtime
parameters are opaque leaves. Successful checking proves one finite control
path for every substitution; examining an opaque leaf is rejected. -/

namespace Compilatrix.Ixby.SymbolicTarget

open Ix.Ixby (Program Limits Error Operand Op Instr Function Block CtorId)

inductive Value where
  | parameter (index : Nat)
  | scalar (value : Ix.Ixby.Scalar)
  | ctor (id : CtorId) (fields : Array Value)
  | pap (function : Nat) (captured : Array Value)
  | erased
  deriving Repr, Inhabited

def Value.instantiate (input : Nat → Ix.Ixby.Value) : Value → Ix.Ixby.Value
  | .parameter index => input index
  | .scalar value => .scalar value
  | .ctor id fields => .ctor id (fields.map (Value.instantiate input))
  | .pap function captured => .pap function (captured.map (Value.instantiate input))
  | .erased => .erased

structure Frame where
  function : Nat
  block : Nat
  locals : Array Value
  deriving Repr, Inhabited

def Frame.instantiate (input : Nat → Ix.Ixby.Value) (frame : Frame) : Ix.Ixby.Frame :=
  { function := frame.function, block := frame.block,
    locals := frame.locals.map (Value.instantiate input) }

def Frame.check (frame : Frame) (limits : Limits) (program : Program) : Except Error Block :=
  (frame.instantiate (fun _ => .erased)).check limits program

def Frame.read (frame : Frame) : Operand → Except Error Value
  | .local index => match frame.locals[index]? with
      | some value => .ok value
      | none => .error (.invalidLocal index)
  | .literal value => .ok (.scalar value)
  | .erased => .ok .erased

def Frame.readOperands (frame : Frame) : List Operand → Except Error (List Value)
  | [] => .ok []
  | operand :: rest => do
      let value ← frame.read operand
      let values ← frame.readOperands rest
      return value :: values

def enter (limits : Limits) (program : Program) (callee : Nat)
    (args : Array Value) : Except Error Frame := do
  let function ← program.getFunction callee
  if args.size != function.arity then throw (.arityMismatch function.arity args.size)
  let frame : Frame := { function := callee, block := function.entry, locals := args }
  let _ ← frame.check limits program
  return frame

def Frame.transfer (frame : Frame) (limits : Limits) (program : Program)
    (target : Nat) (extra : Array Value := #[]) : Except Error Frame := do
  let next := { frame with block := target, locals := frame.locals ++ extra }
  let _ ← next.check limits program
  return next

inductive Action where
  | value (value : Value)
  | call (function : Nat) (args : Array Value)
  | apply (function : Value) (args : Array Value)
  deriving Repr, Inhabited

def Action.instantiate (input : Nat → Ix.Ixby.Value) : Action → Ix.Ixby.Action
  | .value result => .value (result.instantiate input)
  | .call function args => .call function (args.map (Value.instantiate input))
  | .apply function args => .apply (function.instantiate input) (args.map (Value.instantiate input))

def evalOp (_limits : Limits) (program : Program) (frame : Frame) : Op → Except Error Action
  | .copy operand => return .value (← frame.read operand)
  | .primitive _ _ => .error .invalidValue
  | .construct ctor args => do
      let decl ← program.getConstructor ctor
      let fields ← frame.readOperands args
      if fields.length != decl.fields then throw (.arityMismatch decl.fields fields.length)
      return .value (.ctor decl.id fields.toArray)
  | .project operand field => do
      match ← frame.read operand with
      | .ctor _ fields =>
          let some value := fields[field]? | throw (.invalidProjection field)
          return .value value
      | .erased => return .value .erased
      | _ => throw .notConstructor
  | .closure callee operands => do
      let function ← program.getFunction callee
      let captured ← frame.readOperands operands
      if captured.length ≥ function.arity then throw (.invalidClosure callee)
      return .value (.pap callee captured.toArray)
  | .call callee operands => return .call callee (← frame.readOperands operands).toArray
  | .callSelf operands => return .call frame.function (← frame.readOperands operands).toArray
  | .apply operand operands =>
      return .apply (← frame.read operand) (← frame.readOperands operands).toArray

inductive Control where
  | eval (frame : Frame)
  | apply (value : Value) (args : Array Value)
  | ret (value : Value)
  deriving Repr, Inhabited

def Control.instantiate (input : Nat → Ix.Ixby.Value) : Control → Ix.Ixby.Control
  | .eval frame => .eval (frame.instantiate input)
  | .apply value args => .apply (value.instantiate input) (args.map (Value.instantiate input))
  | .ret value => .ret (value.instantiate input)

inductive Continuation where
  | resume (frame : Frame)
  | apply (args : Array Value)
  deriving Repr, Inhabited

def Continuation.instantiate (input : Nat → Ix.Ixby.Value) : Continuation → Ix.Ixby.Continuation
  | .resume frame => .resume (frame.instantiate input)
  | .apply args => .apply (args.map (Value.instantiate input))

structure State where
  control : Control
  continuation : Array Continuation := #[]
  deriving Repr, Inhabited

def State.instantiate (input : Nat → Ix.Ixby.Value) (state : State) : Ix.Ixby.State :=
  { control := state.control.instantiate input,
    continuation := state.continuation.map (Continuation.instantiate input) }

def State.push (state : State) (limits : Limits) (next : Continuation) : Except Error State :=
  if state.continuation.size ≥ limits.continuations then .error (.limit .continuations)
  else .ok { state with continuation := state.continuation.push next }

inductive Transition where
  | next (state : State)
  | halted (value : Value)
  deriving Repr, Inhabited

def Transition.instantiate (input : Nat → Ix.Ixby.Value) : Transition → Ix.Ixby.Transition
  | .next state => .next (state.instantiate input)
  | .halted value => .halted (value.instantiate input)

def stepEval (limits : Limits) (program : Program) (state : State) (frame : Frame) :
    Except Error Transition := do
  let block ← frame.check limits program
  match block.instruction with
  | .letOp op target =>
      match ← evalOp limits program frame op with
      | .value value =>
          let next ← frame.transfer limits program target #[value]
          return .next { state with control := .eval next }
      | .call callee args =>
          let next ← state.push limits (.resume { frame with block := target })
          return .next { next with control := .eval (← enter limits program callee args) }
      | .apply fn args =>
          let next ← state.push limits (.resume { frame with block := target })
          return .next { next with control := .apply fn args }
  | .ret operand => return .next { state with control := .ret (← frame.read operand) }
  | .tailCall callee operands =>
      let args ← frame.readOperands operands
      return .next { state with control := .eval (← enter limits program callee args.toArray) }
  | .tailCallSelf operands =>
      let args ← frame.readOperands operands
      return .next { state with control := .eval (← enter limits program frame.function args.toArray) }
  | .tailApply operand operands =>
      return .next { state with control := .apply (← frame.read operand) (← frame.readOperands operands).toArray }
  | .caseCtor operand alternatives =>
      match ← frame.read operand with
      | .ctor id fields =>
          let target ← Ix.Ixby.selectCase program id alternatives
          let next ← frame.transfer limits program target fields
          return .next { state with control := .eval next }
      | _ => throw .notConstructor
  | .caseNat operand ifZero ifSucc =>
      match ← frame.read operand with
      | .scalar (.nat n) =>
          let next ← match n with
            | 0 => frame.transfer limits program ifZero
            | pred + 1 => frame.transfer limits program ifSucc #[.scalar (.nat pred)]
          return .next { state with control := .eval next }
      | _ => throw .notNat
  | .branch operand yes no =>
      match ← frame.read operand with
      | .scalar (.bool condition) =>
          let next ← frame.transfer limits program (if condition then yes else no)
          return .next { state with control := .eval next }
      | _ => throw .notBool

def stepApply (limits : Limits) (program : Program) (state : State)
    (value : Value) (args : Array Value) : Except Error Transition := do
  if args.isEmpty then return .next { state with control := .ret value }
  match value with
  | .erased => return .next { state with control := .ret .erased }
  | .pap callee captured =>
      let function ← program.getFunction callee
      if captured.size ≥ function.arity then throw (.invalidClosure callee)
      let supplied := captured ++ args
      if supplied.size < function.arity then
        return .next { state with control := .ret (.pap callee supplied) }
      else
        let direct := supplied.extract 0 function.arity
        let rest := supplied.extract function.arity supplied.size
        let next ← if rest.isEmpty then pure state else state.push limits (.apply rest)
        return .next { next with control := .eval (← enter limits program callee direct) }
  | _ => throw .notFunction

def step (limits : Limits) (program : Program) (state : State) : Except Error Transition :=
  match state.control with
  | .eval frame => stepEval limits program state frame
  | .apply value args => stepApply limits program state value args
  | .ret value => do
      match state.continuation.back? with
      | none => return .halted value
      | some continuation =>
          let next := { state with continuation := state.continuation.pop }
          match continuation with
          | .apply args => return .next { next with control := .apply value args }
          | .resume frame =>
              let resumed ← frame.transfer limits program frame.block #[value]
              return .next { next with control := .eval resumed }

def run (limits : Limits) (program : Program) : Nat → State → Except Error Value
  | 0, _ => .error .outOfFuel
  | fuel + 1, state => do
      match ← step limits program state with
      | .halted value => return value
      | .next state => run limits program fuel state

end Compilatrix.Ixby.SymbolicTarget
