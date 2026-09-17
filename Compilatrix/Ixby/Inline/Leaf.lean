import Compilatrix.Ixby.Inline.Operation
import Compilatrix.Ixby.Inline.Steps
import Compilatrix.Ixby.Runtime.Execution

namespace Compilatrix.Ixby.Inline

open Ix.Ixby Runtime.Execution

theorem Leaf.enter_eq {limits : Limits} {program : Program} {id : FunctionId} {leaf : Leaf}
    (body : program.getFunction id = .ok leaf.function) (args : Array Value)
    (arity : args.size = leaf.arity) (room : leaf.arity + 1 ≤ limits.locals) :
    enter limits program id args = .ok ⟨id, 0, args⟩ := by
  simp [enter, Frame.check, body, Leaf.function, arity,
    show ¬limits.locals < leaf.arity by omega, bind, Except.bind, pure, Except.pure]

theorem Leaf.entry_check {limits : Limits} {program : Program} {id : FunctionId} {leaf : Leaf}
    (body : program.getFunction id = .ok leaf.function) (args : Array Value)
    (arity : args.size = leaf.arity) (room : leaf.arity + 1 ≤ limits.locals) :
    (⟨id, 0, args⟩ : Frame).check limits program = .ok ⟨leaf.arity, .letOp leaf.operation.toOp 1⟩ := by
  simp [Frame.check, body, Leaf.function, arity,
    show ¬limits.locals < leaf.arity by omega, bind, Except.bind, pure, Except.pure]

theorem Leaf.step_operation {limits : Limits} {program : Program} {id : FunctionId} {leaf : Leaf}
    (body : program.getFunction id = .ok leaf.function) (args : Array Value)
    (arity : args.size = leaf.arity) (room : leaf.arity + 1 ≤ limits.locals)
    (value : Value) (evaluated : leaf.operation.eval limits program ⟨id, 0, args⟩ = .ok value)
    (continuation : Array Continuation) :
    step limits program (frameState id 0 args continuation) =
      .ok (.next (frameState id 1 (args.push value) continuation)) := by
  apply PureOp.step_value (Leaf.entry_check body args arity room) evaluated
  simp [Frame.transfer, Frame.check, body, Leaf.function, arity, Array.append_singleton,
    Nat.not_lt.mpr room, bind, Except.bind, pure, Except.pure]

theorem Leaf.step_operation_error {limits : Limits} {program : Program} {id : FunctionId} {leaf : Leaf}
    (body : program.getFunction id = .ok leaf.function) (args : Array Value)
    (arity : args.size = leaf.arity) (room : leaf.arity + 1 ≤ limits.locals)
    (error : Error) (evaluated : leaf.operation.eval limits program ⟨id, 0, args⟩ = .error error)
    (continuation : Array Continuation) :
    step limits program (frameState id 0 args continuation) = .error error := by
  simp [step, stepEval, frameState, Leaf.entry_check body args arity room,
    PureOp.eval_toOp, evaluated, Except.map, bind, Except.bind]

theorem Leaf.step_return {limits : Limits} {program : Program} {id : FunctionId} {leaf : Leaf}
    (body : program.getFunction id = .ok leaf.function) (args : Array Value)
    (arity : args.size = leaf.arity) (room : leaf.arity + 1 ≤ limits.locals)
    (value : Value) (continuation : Array Continuation) :
    step limits program (frameState id 1 (args.push value) continuation) =
      .ok (.next (returned value continuation)) := by
  simp [step, stepEval, Frame.check, body, Leaf.function, frameState, returned, arity,
    Nat.not_lt.mpr room, Frame.read, bind, Except.bind, pure, Except.pure]
  simp [← arity]

theorem call_step {limits : Limits} {program : Program} {frame : Frame} {locals : Nat}
    {callee : FunctionId} {args : List Operand} {values : Array Value} {next : BlockId} {leaf : Leaf}
    (code : frame.check limits program = .ok ⟨locals, .letOp (.call callee args) next⟩)
    (read : frame.readOperands args = .ok values.toList)
    (body : program.getFunction callee = .ok leaf.function)
    (arity : values.size = leaf.arity) (room : leaf.arity + 1 ≤ limits.locals)
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations) :
    step limits program ⟨.eval frame, continuation⟩ =
      .ok (.next (frameState callee 0 values (continuation.push (.resume { frame with block := next })))) := by
  simp [step, stepEval, code, evalOp, read, State.push,
    show ¬continuation.size ≥ limits.continuations by omega,
    Leaf.enter_eq body values arity room, frameState, bind, Except.bind, pure, Except.pure]

theorem resume_step {limits : Limits} {program : Program} {frame resumed : Frame}
    {value : Value} {next : BlockId} (continuation : Array Continuation)
    (transfer : frame.transfer limits program next #[value] = .ok resumed) :
    step limits program (returned value (continuation.push (.resume { frame with block := next }))) =
      .ok (.next ⟨.eval resumed, continuation⟩) := by
  have transferred : ({ frame with block := next } : Frame).transfer limits program next #[value] =
      .ok resumed := by simpa [Frame.transfer] using transfer
  simp [step, returned, transferred, bind, Except.bind, pure, Except.pure]

theorem call_path {limits : Limits} {program : Program} {frame : Frame} {locals : Nat}
    {callee : FunctionId} {args : List Operand} {values : Array Value} {next : BlockId} {leaf : Leaf}
    (code : frame.check limits program = .ok ⟨locals, .letOp (.call callee args) next⟩)
    (read : frame.readOperands args = .ok values.toList)
    (body : program.getFunction callee = .ok leaf.function)
    (arity : values.size = leaf.arity) (room : leaf.arity + 1 ≤ limits.locals)
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations)
    (value : Value) (evaluated : leaf.operation.eval limits program ⟨callee, 0, values⟩ = .ok value)
    (resumed : Frame) (transfer : frame.transfer limits program next #[value] = .ok resumed) :
    Steps limits program 4 ⟨.eval frame, continuation⟩ ⟨.eval resumed, continuation⟩ :=
  .cons (call_step code read body arity room continuation stack)
    (.cons (Leaf.step_operation body values arity room value evaluated _)
      (.cons (Leaf.step_return body values arity room value _)
        (.cons (resume_step continuation transfer) (.refl _))))

end Compilatrix.Ixby.Inline
