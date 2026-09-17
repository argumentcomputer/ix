import Compilatrix.Ixby.Runtime.Chunked.Representation

namespace Compilatrix.Ixby.Runtime.Chunked

open Ix.Ixby (Limits Program Error Operand Block FunctionId BlockId)

@[simp] theorem Frame.read_sim (frame : Frame) (operand : Operand) :
    (frame.read operand).map Value.toReference = frame.toReference.read operand := by
  cases operand with
  | «local» slot =>
    cases found : frame.locals[slot]? <;>
      simp [Frame.read, Ix.Ixby.Frame.read, Frame.toReference, found, Except.map]
  | _ => simp [Frame.read, Ix.Ixby.Frame.read, Except.map]

@[simp] theorem Frame.readOperands_sim (frame : Frame) (operands : List Operand) :
    (frame.readOperands operands).map (List.map Value.toReference) =
      frame.toReference.readOperands operands := by
  induction operands with
  | nil => rfl
  | cons operand rest ih =>
    simp only [Frame.readOperands, Ix.Ixby.Frame.readOperands, ← Frame.read_sim, ← ih]
    cases read : frame.read operand <;> cases reads : frame.readOperands rest <;>
      simp [Except.map, bind, Except.bind, pure, Except.pure]

@[simp] theorem Frame.check_sim (frame : Frame) (limits : Limits) (program : Program) :
    frame.toReference.check limits program = frame.check limits program := by
  simp only [Frame.check, Ix.Ixby.Frame.check, Frame.toReference, Array.size_map]
  rfl

@[simp] theorem enter_sim (limits : Limits) (program : Program) (callee : FunctionId)
    (args : Array Value) :
    (enter limits program callee args).map Frame.toReference =
      Ix.Ixby.enter limits program callee (args.map Value.toReference) := by
  simp only [enter, Ix.Ixby.enter, Array.size_map]
  cases found : program.getFunction callee with
  | error error => rfl
  | ok function =>
    simp only [bind, Except.bind]
    split
    · rfl
    · change (do
        let _ ← Frame.check ⟨callee, function.entry, args⟩ limits program
        pure (Frame.mk callee function.entry args)).map Frame.toReference = (do
        let _ ← (Frame.mk callee function.entry args).toReference.check limits program
        pure (Frame.mk callee function.entry args).toReference)
      rw [Frame.check_sim]
      cases Frame.check ⟨callee, function.entry, args⟩ limits program <;> rfl

@[simp] theorem Frame.transfer_sim (frame : Frame) (limits : Limits) (program : Program)
    (target : BlockId) (extra : Array Value) :
    (frame.transfer limits program target extra).map Frame.toReference =
      frame.toReference.transfer limits program target (extra.map Value.toReference) := by
  let next : Frame := { frame with block := target, locals := frame.locals ++ extra }
  have same : Ix.Ixby.Frame.mk frame.function target
      (frame.locals.map Value.toReference ++ extra.map Value.toReference) = next.toReference := by
    simp [next, Frame.toReference]
  simp only [Frame.transfer, Ix.Ixby.Frame.transfer, Frame.toReference, same]
  change (do
      let _ ← next.check limits program
      pure next).map Frame.toReference = (do
      let _ ← next.toReference.check limits program
      pure next.toReference)
  rw [Frame.check_sim]
  cases next.check limits program <;> rfl

@[simp] theorem State.push_sim (state : State) (limits : Limits) (cont : Continuation) :
    (state.push limits cont).map State.toReference =
      state.toReference.push limits cont.toReference := by
  simp only [State.push, Ix.Ixby.State.push, State.toReference, Array.size_map]
  split <;> simp [Except.map, State.toReference]

end Compilatrix.Ixby.Runtime.Chunked
