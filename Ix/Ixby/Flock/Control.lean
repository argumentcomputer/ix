module
public import Ix.Ixby.Eval

/-!
# Ordered-bank control refinement for the generic Flock machine

This is the logical, decoded control boundary for the native fixed-capacity
component. Locals and saved continuations are in oldest-first array order,
not the reverse lists used by the Aiur backend. The rules check actual
instructions, operand reads, callee declarations and destination blocks.
Primitive evaluation is a separately visible premise, not a verifier oracle.

`Step.reference` proves these rules implement the existing reference step.
It does NOT prove that arbitrary native R1CS rows decode to these rules.
The Boolean-table/packing bridge, authenticated instruction/operand decoding,
primitive correspondence and physical-capacity admission remain obligations.
In particular the native component's free resolved actions alone do not imply
`Step`: the instruction/operand premises below must be discharged as well.
-/

public section
@[expose] section

namespace Ix.Ixby.FlockBackend.ControlModel

private theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

private theorem except_map_ok {ε α β : Type} (a : α) (f : α → β) :
    f <$> (Except.ok a : Except ε α) = .ok (f a) := rfl

attribute [local simp] except_bind_ok except_map_ok

inductive ActiveControl where
  | eval (frame : Frame)
  | ret (value : Value)
  deriving BEq, Repr, Inhabited

def ActiveControl.decode : ActiveControl → Control
  | .eval frame => .eval frame
  | .ret value => .ret value

structure Machine where
  control : ActiveControl
  /-- Live prefix in physical bank order; the last frame is resumed first. -/
  stack : Array Frame := #[]
  deriving BEq, Repr, Inhabited

def Machine.decode (machine : Machine) : State :=
  ⟨machine.control.decode, machine.stack.map Continuation.resume⟩

inductive Outcome where
  | next (machine : Machine)
  | halted (value : Value)
  deriving BEq, Repr, Inhabited

def Outcome.decode : Outcome → Transition
  | .next machine => .next machine.decode
  | .halted value => .halted value

def append (frame : Frame) (target : BlockId) (value : Value) : Frame :=
  { frame with block := target, locals := frame.locals.push value }

/-- Only the first-order value/call operation fragment. Each constructor
resolves the actual source operands; an arbitrary action is not admissible. -/
inductive Resolves (limits : Limits) (program : Program) (frame : Frame) :
    Op → Action → Prop where
  | copy {operand : Operand} {value : Value}
      (read : frame.read operand = .ok value) :
      Resolves limits program frame (.copy operand) (.value value)
  | primitive {primitive : Primitive} {operands : List Operand} {args : List Value}
      {value : Value}
      (read : frame.readOperands operands = .ok args)
      (evaluated : primitive.eval limits args = .ok value) :
      Resolves limits program frame (.primitive primitive operands) (.value value)
  | call {callee : FunctionId} {operands : List Operand} {args : List Value}
      (read : frame.readOperands operands = .ok args) :
      Resolves limits program frame (.call callee operands) (.call callee args.toArray)
  | callSelf {operands : List Operand} {args : List Value}
      (read : frame.readOperands operands = .ok args) :
      Resolves limits program frame (.callSelf operands) (.call frame.function args.toArray)

theorem Resolves.reference {limits : Limits} {program : Program} {frame : Frame}
    {op : Op} {action : Action} (resolved : Resolves limits program frame op action) :
    evalOp limits program frame op = .ok action := by
  cases resolved with
  | copy read => simp [evalOp, read]
  | primitive read evaluated => simp [evalOp, read, evaluated]
  | call read => simp [evalOp, read]
  | callSelf read => simp [evalOp, read]

/-- Explicit authenticated callee metadata and entry-frame contract. The
native action's claimed entry/arity cannot stand in for these checks. -/
structure Entry (limits : Limits) (program : Program) (callee : FunctionId)
    (args : Array Value) where
  function : Function
  found : program.getFunction callee = .ok function
  arity : args.size = function.arity
  block : Block
  checked : (Frame.mk callee function.entry args).check limits program = .ok block

def Entry.frame {limits : Limits} {program : Program} {callee : FunctionId}
    {args : Array Value} (entry : Entry limits program callee args) : Frame :=
  ⟨callee, entry.function.entry, args⟩

theorem Entry.reference {limits : Limits} {program : Program} {callee : FunctionId}
    {args : Array Value} (entry : Entry limits program callee args) :
    enter limits program callee args = .ok entry.frame := by
  simp [enter, entry.found, entry.arity, entry.checked, Entry.frame]

private theorem append_transfer {limits : Limits} {program : Program}
    {frame : Frame} {target : BlockId} {value : Value} {block : Block}
    (checked : (append frame target value).check limits program = .ok block) :
    frame.transfer limits program target #[value] = .ok (append frame target value) := by
  simp only [append] at checked
  simp [Frame.transfer, append, checked]

private theorem branch_transfer {limits : Limits} {program : Program}
    {frame : Frame} {target : BlockId} {block : Block}
    (checked : ({ frame with block := target } : Frame).check limits program = .ok block) :
    frame.transfer limits program target = .ok { frame with block := target } := by
  simp [Frame.transfer, checked]

/-- The native control update after canonical bank decoding AND constrained
instruction resolution. Whole-image admission is an additional initial-state
condition, so these rules cannot authenticate an unvisited malformed block. -/
inductive Step (limits : Limits) (program : Program) : Machine → Outcome → Prop where
  | bind {frame : Frame} {stack : Array Frame} {op : Op} {target : BlockId}
      {value : Value} {declared : Nat} {next : Block}
      (checked : frame.check limits program = .ok ⟨declared, .letOp op target⟩)
      (resolved : Resolves limits program frame op (.value value))
      (destination : (append frame target value).check limits program = .ok next) :
      Step limits program ⟨.eval frame, stack⟩
        (.next ⟨.eval (append frame target value), stack⟩)
  | call {frame : Frame} {stack : Array Frame} {op : Op} {target : BlockId}
      {callee : FunctionId} {args : Array Value} {declared : Nat}
      (checked : frame.check limits program = .ok ⟨declared, .letOp op target⟩)
      (resolved : Resolves limits program frame op (.call callee args))
      (entry : Entry limits program callee args)
      (capacity : stack.size < limits.continuations) :
      Step limits program ⟨.eval frame, stack⟩
        (.next ⟨.eval entry.frame, stack.push { frame with block := target }⟩)
  | ret {frame : Frame} {stack : Array Frame} {operand : Operand} {value : Value}
      {declared : Nat}
      (checked : frame.check limits program = .ok ⟨declared, .ret operand⟩)
      (read : frame.read operand = .ok value) :
      Step limits program ⟨.eval frame, stack⟩ (.next ⟨.ret value, stack⟩)
  | tailCall {frame : Frame} {stack : Array Frame} {callee : FunctionId}
      {operands : List Operand} {args : List Value} {declared : Nat}
      (checked : frame.check limits program = .ok ⟨declared, .tailCall callee operands⟩)
      (read : frame.readOperands operands = .ok args)
      (entry : Entry limits program callee args.toArray) :
      Step limits program ⟨.eval frame, stack⟩ (.next ⟨.eval entry.frame, stack⟩)
  | tailCallSelf {frame : Frame} {stack : Array Frame} {operands : List Operand}
      {args : List Value} {declared : Nat}
      (checked : frame.check limits program = .ok ⟨declared, .tailCallSelf operands⟩)
      (read : frame.readOperands operands = .ok args)
      (entry : Entry limits program frame.function args.toArray) :
      Step limits program ⟨.eval frame, stack⟩ (.next ⟨.eval entry.frame, stack⟩)
  | branch {frame : Frame} {stack : Array Frame} {operand : Operand} {condition : Bool}
      {yes no : BlockId} {declared : Nat} {next : Block}
      (checked : frame.check limits program = .ok ⟨declared, .branch operand yes no⟩)
      (read : frame.read operand = .ok (.scalar (.bool condition)))
      (destination : ({ frame with block := if condition then yes else no } : Frame).check
        limits program = .ok next) :
      Step limits program ⟨.eval frame, stack⟩
        (.next ⟨.eval { frame with block := if condition then yes else no }, stack⟩)
  | resume {value : Value} {saved : Frame} {rest : Array Frame} {next : Block}
      (destination : (append saved saved.block value).check limits program = .ok next) :
      Step limits program ⟨.ret value, rest.push saved⟩
        (.next ⟨.eval (append saved saved.block value), rest⟩)
  | halt (value : Value) :
      Step limits program ⟨.ret value, #[]⟩ (.halted value)

/-- No whole-step correctness assumption occurs here. The local instruction,
operand, primitive and callee premises above imply the reference transition. -/
theorem Step.reference {limits : Limits} {program : Program} {before : Machine}
    {after : Outcome} (transition : Step limits program before after) :
    Ix.Ixby.step limits program before.decode = .ok after.decode := by
  cases transition with
  | bind checked resolved destination =>
    simp [Ix.Ixby.step, stepEval, Machine.decode, ActiveControl.decode, Outcome.decode,
      checked, resolved.reference, append_transfer destination]
  | call checked resolved entry capacity =>
    simp [Ix.Ixby.step, stepEval, State.push, Machine.decode, ActiveControl.decode,
      Outcome.decode, checked, resolved.reference, entry.reference,
      Nat.not_le.mpr capacity]
  | ret checked read =>
    simp [Ix.Ixby.step, stepEval, Machine.decode, ActiveControl.decode, Outcome.decode,
      checked, read]
  | tailCall checked read entry =>
    simp [Ix.Ixby.step, stepEval, Machine.decode, ActiveControl.decode, Outcome.decode,
      checked, read, entry.reference]
  | tailCallSelf checked read entry =>
    simp [Ix.Ixby.step, stepEval, Machine.decode, ActiveControl.decode, Outcome.decode,
      checked, read, entry.reference]
  | branch checked read destination =>
    simp [Ix.Ixby.step, stepEval, Machine.decode, ActiveControl.decode, Outcome.decode,
      checked, read, branch_transfer destination]
  | resume destination =>
    simp [Ix.Ixby.step, Machine.decode, ActiveControl.decode, Outcome.decode,
      append_transfer destination]
  | halt value =>
    simp [Ix.Ixby.step, Machine.decode, ActiveControl.decode, Outcome.decode,
      Pure.pure, Except.pure]

end Ix.Ixby.FlockBackend.ControlModel
