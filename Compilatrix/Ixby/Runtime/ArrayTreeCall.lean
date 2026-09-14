import Compilatrix.Ixby.Runtime.ArrayTreeCertificate
import Compilatrix.Ixby.Runtime.NatArithmetic

/-! Ordinary calls compose a callee path with the exact saved caller frame.
The callee's resource premises are checked at the extended continuation. -/

namespace Compilatrix.Ixby.Runtime.ArrayTrees

open Ix.Ixby Execution

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

end Compilatrix.Ixby.Runtime.ArrayTrees

namespace Compilatrix.Ixby.Runtime.ArrayTrees

open Ix.Ixby Execution ScalarFunction

/-- A local helper path becomes a whole-program execution only after the
reference evaluator admits the program and validates the complete input. -/
theorem evaluates_of_returns {limits : Limits} {program : Program} {id : FunctionId}
    {fn : Function} (checked : Checked program id fn) {input : Array Value} {value : Value}
    (arity : fn.arity = input.size) (entryBlock : fn.entry = 0) (instruction : Instr)
    (firstBlock : fn.blocks[0]? = some ⟨input.size, instruction⟩)
    (room : input.size ≤ limits.locals) (entry : program.entry = id)
    (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes input.toList = .ok ())
    (path : Reaches limits program (frameState id 0 input #[]) (returned value #[])) :
    Evaluates limits program input value := by
  apply path.evaluates
  simp [initialState, admitted, inputs, enter, entry, checked.code, arity, entryBlock,
    Frame.check, firstBlock, frameState, show ¬limits.locals < input.size by omega,
    bind, Except.bind, pure, Except.pure]

end Compilatrix.Ixby.Runtime.ArrayTrees
