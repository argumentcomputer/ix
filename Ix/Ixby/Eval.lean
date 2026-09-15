module
public import Ix.Ixby.Validate

/-!
# Total reference execution for functional IxBy

Only execute constructs and validates a whole-program initial state. The
intermediate step/run interfaces support simulation proofs; arbitrary states
passed to them are not authenticated program executions. One transition is a
logical operation, not a unit of prover work: operand vectors, Nat arithmetic,
and object representation must be arithmetized separately.
-/

public section
@[expose] section

namespace Ix.Ixby

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

def initialState (limits : Limits) (program : Program) (input : Array Value) :
    Except Error State := do
  validateProgram limits program
  let frame ← enter limits program program.entry input
  validateInputValues limits program limits.inputNodes input.toList
  return { control := .eval frame }

/-- A pure instruction can produce a value immediately or request a call.
The scheduler, not recursive host evaluation, handles all function execution. -/
inductive Action where
  | value (result : Value)
  | call (callee : FunctionId) (args : Array Value)
  | apply (function : Value) (args : Array Value)
  deriving BEq, Repr, Inhabited

def evalOp (limits : Limits) (program : Program) (frame : Frame) :
    Op → Except Error Action
  | .copy value => return .value (← frame.read value)
  | .primitive prim args => return .value (← prim.eval limits (← frame.readOperands args))
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

def selectCase (program : Program) (id : CtorId) : List Alternative → Except Error BlockId
  | [] => .error (.missingCase id)
  | alternative :: rest => do
    let ctor ← program.getConstructor alternative.ctor
    if ctor.id == id then return alternative.target
    selectCase program id rest

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

/-- Exhaustion is not termination. A nonterminating guest has no successful
finite-fuel execution merely because its local calls can be described. -/
def run (limits : Limits) (program : Program) : Nat → State → Except Error Value
  | 0, _ => .error .outOfFuel
  | fuel + 1, state =>
    match step limits program state with
    | .error error => .error error
    | .ok (.halted value) => .ok value
    | .ok (.next next) => run limits program fuel next

def execute (limits : Limits) (program : Program) (input : Array Value) (fuel : Nat) :
    Except Error Value :=
  match initialState limits program input with
  | .error error => .error error
  | .ok state => run limits program fuel state

/-- Successful whole-program execution under exact program, input, and limits.
The final value is logical data, not yet a canonical output commitment. -/
def Evaluates (limits : Limits) (program : Program) (input : Array Value) (output : Value) : Prop :=
  ∃ fuel, execute limits program input fuel = .ok output

theorem run_add_fuel {limits : Limits} {program : Program} {output : Value}
    {fuel : Nat} {state : State}
    (accepted : run limits program fuel state = .ok output) (extra : Nat) :
    run limits program (fuel + extra) state = .ok output := by
  induction fuel generalizing state with
  | zero => simp [run] at accepted
  | succ fuel ih =>
    cases hs : step limits program state with
    | error error => simp [run, hs] at accepted
    | ok transition =>
      cases transition with
      | halted result => simpa [run, hs, Nat.succ_add] using accepted
      | next next =>
        have acceptedNext : run limits program fuel next = .ok output := by
          simpa [run, hs] using accepted
        simpa [run, hs, Nat.succ_add] using ih acceptedNext

theorem execute_add_fuel {limits : Limits} {program : Program} {input : Array Value}
    {output : Value} {fuel : Nat}
    (accepted : execute limits program input fuel = .ok output) (extra : Nat) :
    execute limits program input (fuel + extra) = .ok output := by
  cases hi : initialState limits program input with
  | error error => simp [execute, hi] at accepted
  | ok state =>
    have acceptedRun : run limits program fuel state = .ok output := by
      simpa [execute, hi] using accepted
    simpa [execute, hi] using run_add_fuel acceptedRun extra

theorem evaluates_deterministic {limits : Limits} {program : Program}
    {input : Array Value} {left right : Value} (hl : Evaluates limits program input left)
    (hr : Evaluates limits program input right) : left = right := by
  obtain ⟨lf, hl⟩ := hl
  obtain ⟨rf, hr⟩ := hr
  have hl' := execute_add_fuel hl rf
  have hr' := execute_add_fuel hr lf
  rw [Nat.add_comm rf lf] at hr'
  exact Except.ok.inj (hl'.symm.trans hr')

end Ix.Ixby
