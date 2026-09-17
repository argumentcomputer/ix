import Compilatrix.Ixby.Runtime.Chunked.FrameSimulation
import Compilatrix.Ixby.Runtime.Chunked.PrimitiveSimulation

namespace Compilatrix.Ixby.Runtime.Chunked

open Ix.Ixby (Limits Program Op)

set_option maxRecDepth 2048
set_option maxHeartbeats 400000

theorem evalOp_sim (limits : Limits) (program : Program) (frame : Frame) (op : Op) :
    (evalOp limits program frame op).map Action.toReference =
      Ix.Ixby.evalOp limits program frame.toReference op := by
  cases op with
  | copy operand =>
    simp only [evalOp, Ix.Ixby.evalOp, ← Frame.read_sim]
    cases frame.read operand <;> simp [Except.map, bind, Except.bind]
  | primitive primitive operands =>
    simp only [evalOp, Ix.Ixby.evalOp, ← Frame.readOperands_sim]
    cases frame.readOperands operands with
    | error error => rfl
    | ok args =>
      simp only [Except.map, bind, Except.bind, ← eval_sim]
      cases eval limits primitive args <;> simp [Except.map, bind, Except.bind]
  | construct ctor operands =>
    simp only [evalOp, Ix.Ixby.evalOp, ← Frame.readOperands_sim]
    cases program.getConstructor ctor <;> cases frame.readOperands operands <;>
      simp [Except.map, bind, Except.bind, Array.attach_map_val, apply_ite]
    split <;> simp_all [Array.attach_map_val]
  | project operand index =>
    simp only [evalOp, Ix.Ixby.evalOp, ← Frame.read_sim]
    cases frame.read operand with
    | error error => rfl
    | ok value =>
      cases value with
      | ctor id fields =>
        cases found : fields[index]? <;>
          simp [Except.map, bind, Except.bind, found, Array.attach_map_val]
      | _ => simp [Except.map, bind, Except.bind]
  | closure callee operands =>
    simp only [evalOp, Ix.Ixby.evalOp, ← Frame.readOperands_sim]
    cases program.getFunction callee <;> cases frame.readOperands operands <;>
      simp [Except.map, bind, Except.bind, Array.attach_map_val, apply_ite]
    split <;> simp_all [Array.attach_map_val]
  | call callee operands =>
    simp only [evalOp, Ix.Ixby.evalOp, ← Frame.readOperands_sim]
    cases frame.readOperands operands <;> simp [Except.map, bind, Except.bind]
  | callSelf operands =>
    simp only [evalOp, Ix.Ixby.evalOp, ← Frame.readOperands_sim]
    cases frame.readOperands operands <;> simp [Except.map, bind, Except.bind, Frame.toReference]
  | apply operand operands =>
    simp only [evalOp, Ix.Ixby.evalOp, ← Frame.read_sim, ← Frame.readOperands_sim]
    cases frame.read operand <;> cases frame.readOperands operands <;>
      simp [Except.map, bind, Except.bind]

end Compilatrix.Ixby.Runtime.Chunked
