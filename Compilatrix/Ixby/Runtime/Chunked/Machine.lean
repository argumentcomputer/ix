import Ix.Ixby.Eval
import Compilatrix.Ixby.Runtime.Chunked.Primitive

namespace Compilatrix.Ixby.Runtime.Chunked

open Ix.Ixby (Scalar CtorId FunctionId BlockId Limits Program Error Operand
  Block Op Alternative selectCase)

structure Frame where
  function : FunctionId
  block : BlockId
  locals : Array Value
  deriving Repr, Inhabited

inductive Control where
  | eval (frame : Frame)
  | apply (function : Value) (args : Array Value)
  | ret (value : Value)
  deriving Repr, Inhabited

inductive Continuation where
  /-- Resume at this block after appending the returned value to saved locals. -/
  | resume (frame : Frame)
  /-- Over-application first calls the saturated function, then applies its
  result to these arguments before resuming the original caller. -/
  | apply (args : Array Value)
  deriving Repr, Inhabited

structure State where
  control : Control
  continuation : Array Continuation := #[]
  deriving Repr, Inhabited

inductive Transition where
  | next (state : State)
  | halted (value : Value)
  deriving Repr, Inhabited

def Frame.read (frame : Frame) : Operand → Except Error Value
  | .local slot =>
    match frame.locals[slot]? with
    | some value => .ok value
    | none => .error (.invalidLocal slot)
  | .literal value => .ok (.scalar value)
  | .erased => .ok .erased

def Frame.readOperands (frame : Frame) : List Operand → Except Error (List Value)
  | [] => .ok []
  | arg :: rest => do
    let value ← frame.read arg
    let values ← frame.readOperands rest
    return value :: values

def Frame.check (frame : Frame) (limits : Limits) (program : Program) : Except Error Block := do
  let function ← program.getFunction frame.function
  let some block := function.blocks[frame.block]?
    | throw (.invalidBlock frame.function frame.block)
  if frame.locals.size > limits.locals then throw (.limit .locals)
  if frame.locals.size != block.locals then throw (.frameSize block.locals frame.locals.size)
  return block

def enter (limits : Limits) (program : Program) (callee : FunctionId)
    (args : Array Value) : Except Error Frame := do
  let function ← program.getFunction callee
  if args.size != function.arity then throw (.arityMismatch function.arity args.size)
  let frame : Frame := { function := callee, block := function.entry, locals := args }
  let _ ← frame.check limits program
  return frame

def Frame.transfer (frame : Frame) (limits : Limits) (program : Program)
    (target : BlockId) (extra : Array Value := #[]) : Except Error Frame := do
  let next := { frame with block := target, locals := frame.locals ++ extra }
  let _ ← next.check limits program
  return next

inductive Action where
  | value (result : Value)
  | call (callee : FunctionId) (args : Array Value)
  | apply (function : Value) (args : Array Value)
  deriving Repr, Inhabited

def evalOp (limits : Limits) (program : Program) (frame : Frame) :
    Op → Except Error Action
  | .copy value => return .value (← frame.read value)
  | .primitive prim args => return .value (← Chunked.eval limits prim (← frame.readOperands args))
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

def State.push (state : State) (limits : Limits) (next : Continuation) : Except Error State :=
  if state.continuation.size ≥ limits.continuations then .error (.limit .continuations)
  else .ok { state with continuation := state.continuation.push next }

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
      let saved := { frame with block := target }
      let next ← state.push limits (.resume saved)
      return .next { next with control := .eval (← enter limits program callee args) }
    | .apply function args =>
      let saved := { frame with block := target }
      let next ← state.push limits (.resume saved)
      return .next { next with control := .apply function args }
  | .ret operand => return .next { state with control := .ret (← frame.read operand) }
  | .tailCall callee operands =>
    let args ← frame.readOperands operands
    return .next { state with control := .eval (← enter limits program callee args.toArray) }
  | .tailCallSelf operands =>
    let args ← frame.readOperands operands
    return .next { state with
      control := .eval (← enter limits program frame.function args.toArray) }
  | .tailApply operand operands =>
    return .next { state with
      control := .apply (← frame.read operand) (← frame.readOperands operands).toArray }
  | .caseCtor operand alternatives =>
    match ← frame.read operand with
    | .ctor id fields =>
      let target ← selectCase program id alternatives
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
  | .branch operand ifTrue ifFalse =>
    match ← frame.read operand with
    | .scalar (.bool condition) =>
      let next ← frame.transfer limits program (if condition then ifTrue else ifFalse)
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

/-- Return frames restore the caller's function, code position, and immutable
locals. Tail calls add no frame; over-application uses a separate apply frame.
Even a terminal return requires one transition and therefore positive fuel. -/
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

end Compilatrix.Ixby.Runtime.Chunked
