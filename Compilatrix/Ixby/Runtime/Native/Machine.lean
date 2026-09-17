import Compilatrix.Ixby.Runtime.Native.Certificate
import Compilatrix.Ixby.Runtime.Execution

namespace Compilatrix.Ixby.Runtime.ScalarFunction

open Ix.Ixby Execution

theorem Checked.unary_returns {program : Program} {id : FunctionId} {operation : Primitive}
    (checked : Checked program id (direct 1 operation)) (limits : Limits)
    (room : 2 ≤ limits.locals) (arg result : Value)
    (primitive : operation.eval limits [arg] = .ok result) (continuation : Array Continuation) :
    Reaches limits program (frameState id 0 #[arg] continuation) (returned result continuation) := by
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, direct, frameState, returned,
      evalOp, Frame.readOperands, Frame.read, Frame.transfer, primitive, List.range_succ,
      Nat.not_lt.mpr room, show ¬limits.locals < 1 by omega,
      bind, Except.bind, pure, Except.pure]
  rfl

theorem Checked.binary_returns {program : Program} {id : FunctionId} {operation : Primitive}
    (checked : Checked program id (direct 2 operation)) (limits : Limits)
    (room : 3 ≤ limits.locals) (a b result : Value)
    (primitive : operation.eval limits [a, b] = .ok result) (continuation : Array Continuation) :
    Reaches limits program (frameState id 0 #[a, b] continuation) (returned result continuation) := by
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, direct, frameState, returned,
      evalOp, Frame.readOperands, Frame.read, Frame.transfer, primitive, List.range_succ,
      Nat.not_lt.mpr room, show ¬limits.locals < 2 by omega,
      bind, Except.bind, pure, Except.pure]
  rfl

def identity : Function := { arity := 1, blocks := #[⟨1, .ret (.local 0)⟩] }

theorem Checked.identity_returns {program : Program} {id : FunctionId}
    (checked : Checked program id identity) (limits : Limits)
    (room : 1 ≤ limits.locals) (value : Value) (continuation : Array Continuation) :
    Reaches limits program (frameState id 0 #[value] continuation) (returned value continuation) := by
  apply Reaches.of_step
  simp [step, stepEval, Frame.check, checked.code, identity, frameState, returned,
    Frame.read, Nat.not_lt.mpr room, bind, Except.bind, pure, Except.pure]

/-- A wrapper that tail-calls a checked helper neither pushes nor consumes
the caller's continuation. Its transfer still checks both concrete frames. -/
theorem tailCall_reaches {program : Program} {limits : Limits}
    {id callee : FunctionId} {expected target : Function}
    (checked : Checked program id expected) (_called : Checked program callee target)
    (args : Array Value) (operands : List Operand) (continuation : Array Continuation)
    (source : expected.blocks[0]? = some ⟨args.size, .tailCall callee operands⟩)
    (locals : args.size ≤ limits.locals)
    (values : Array Value)
    (read : ({ function := id, block := 0, locals := args } : Frame).readOperands operands = .ok values.toList)
    (entering : enter limits program callee values =
      .ok { function := callee, block := target.entry, locals := values }) :
    Reaches limits program (frameState id 0 args continuation)
      (frameState callee target.entry values continuation) := by
  apply Reaches.of_step
  simp [step, stepEval, Frame.check, checked.code, source, frameState, read, entering,
    Nat.not_lt.mpr locals, bind, Except.bind, pure, Except.pure]

end Compilatrix.Ixby.Runtime.ScalarFunction

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution

/-- Ordinary calls compose with a checked callee path and resume the exact
saved frame. The continuation bound is tested before entering the callee. -/
theorem call_returns (limits : Limits) (program : Program) (frame : Frame)
    (id : FunctionId) (operands : List Operand) (args : Array Value) (target : BlockId)
    (value : Value) (resumed : Frame) (continuation : Array Continuation)
    (stack : continuation.size < limits.continuations)
    (code : frame.check limits program =
      .ok ⟨frame.locals.size, .letOp (.call id operands) target⟩)
    (read : frame.readOperands operands = .ok args.toList)
    (entered : enter limits program id args =
      .ok { function := id, block := 0, locals := args })
    (transfer : frame.transfer limits program target #[value] = .ok resumed)
    (callee : Reaches limits program
      (frameState id 0 args (continuation.push (.resume { frame with block := target })))
      (returned value (continuation.push (.resume { frame with block := target })))) :
    Reaches limits program { control := .eval frame, continuation }
      { control := .eval resumed, continuation } := by
  have beforeCall : Reaches limits program { control := .eval frame, continuation }
      (frameState id 0 args (continuation.push (.resume { frame with block := target }))) := by
    apply Reaches.of_step
    simp [step, stepEval, code, evalOp, read, State.push, entered, frameState,
      show ¬continuation.size ≥ limits.continuations by omega,
      bind, Except.bind, pure, Except.pure]
  have afterCall := Execution.resume value continuation { frame with block := target } resumed
    (by simpa [Frame.transfer] using transfer)
  exact beforeCall.trans (callee.trans afterCall)

theorem apply_returns (limits : Limits) (program : Program) (frame : Frame)
    (operand : Operand) (operands : List Operand) (function : Value) (args : Array Value)
    (target : BlockId) (value : Value) (resumed : Frame) (continuation : Array Continuation)
    (stack : continuation.size < limits.continuations)
    (code : frame.check limits program =
      .ok ⟨frame.locals.size, .letOp (.apply operand operands) target⟩)
    (readFunction : frame.read operand = .ok function)
    (read : frame.readOperands operands = .ok args.toList)
    (transfer : frame.transfer limits program target #[value] = .ok resumed)
    (callee : Reaches limits program
      { control := .apply function args, continuation := continuation.push (.resume { frame with block := target }) }
      (returned value (continuation.push (.resume { frame with block := target })))) :
    Reaches limits program { control := .eval frame, continuation }
      { control := .eval resumed, continuation } := by
  have beforeApply : Reaches limits program { control := .eval frame, continuation }
      { control := .apply function args, continuation := continuation.push (.resume { frame with block := target }) } := by
    apply Reaches.of_step
    simp [step, stepEval, code, evalOp, readFunction, read, State.push,
      show ¬continuation.size ≥ limits.continuations by omega,
      bind, Except.bind, pure, Except.pure]
  have afterApply := Execution.resume value continuation { frame with block := target } resumed
    (by simpa [Frame.transfer] using transfer)
  exact beforeApply.trans (callee.trans afterApply)

end Compilatrix.Ixby.Runtime.Native
