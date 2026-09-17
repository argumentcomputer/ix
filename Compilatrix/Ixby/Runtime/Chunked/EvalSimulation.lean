import Compilatrix.Ixby.Runtime.Chunked.OpSimulation

namespace Compilatrix.Ixby.Runtime.Chunked

open Ix.Ixby (Limits Program Error)

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

theorem stepEval_sim (limits : Limits) (program : Program) (state : State) (frame : Frame) :
    (stepEval limits program state frame).map Transition.toReference =
      Ix.Ixby.stepEval limits program state.toReference frame.toReference := by
  simp only [stepEval, Ix.Ixby.stepEval, Frame.check_sim]
  cases checked : frame.check limits program with
  | error error => rfl
  | ok block =>
    simp only [bind, Except.bind]
    cases instruction : block.instruction with
    | letOp op target =>
      simp only [← evalOp_sim]
      cases result : evalOp limits program frame op with
      | error error => rfl
      | ok action =>
        cases action with
        | value value =>
          simp only [Except.map, Action.toReference, bind, Except.bind]
          have transfer := Frame.transfer_sim frame limits program target #[value]
          simp only [Array.map_singleton] at transfer
          rw [← transfer]
          cases frame.transfer limits program target #[value] <;>
            simp [Except.map, bind, Except.bind, State.toReference]
        | call callee args =>
          simp only [Except.map, Action.toReference, bind, Except.bind]
          have pushed := State.push_sim state limits (.resume { frame with block := target })
          simp only [Continuation.toReference, Frame.toReference] at pushed
          simp only [Frame.toReference]
          rw [← pushed, ← enter_sim]
          cases state.push limits (.resume { frame with block := target }) <;>
            cases enter limits program callee args <;>
            simp [Except.map, bind, Except.bind, State.toReference]
        | apply fn args =>
          simp only [Except.map, Action.toReference, bind, Except.bind]
          have pushed := State.push_sim state limits (.resume { frame with block := target })
          simp only [Continuation.toReference, Frame.toReference] at pushed
          simp only [Frame.toReference]
          rw [← pushed]
          cases state.push limits (.resume { frame with block := target }) <;>
            simp [Except.map, bind, Except.bind, State.toReference]
    | ret operand =>
      simp only [← Frame.read_sim]
      cases frame.read operand <;> simp [Except.map, bind, Except.bind, State.toReference]
    | tailCall callee operands =>
      simp only [← Frame.readOperands_sim]
      cases frame.readOperands operands with
      | error error => rfl
      | ok args =>
        simp only [Except.map, bind, Except.bind]
        have entered := enter_sim limits program callee args.toArray
        simp only [List.map_toArray] at entered
        rw [← entered]
        cases enter limits program callee args.toArray <;>
          simp [Except.map, bind, Except.bind, State.toReference]
    | tailCallSelf operands =>
      simp only [← Frame.readOperands_sim]
      cases frame.readOperands operands with
      | error error => rfl
      | ok args =>
        simp only [Except.map, bind, Except.bind]
        have entered := enter_sim limits program frame.function args.toArray
        simp only [List.map_toArray] at entered
        simp only [Frame.toReference] at *
        rw [← entered]
        cases enter limits program frame.function args.toArray <;>
          simp [Except.map, bind, Except.bind, State.toReference]
    | tailApply operand operands =>
      simp only [← Frame.read_sim, ← Frame.readOperands_sim]
      cases frame.read operand <;> cases frame.readOperands operands <;>
        simp [Except.map, bind, Except.bind, State.toReference]
    | caseCtor operand alternatives =>
      simp only [← Frame.read_sim]
      cases frame.read operand with
      | error error => rfl
      | ok value =>
        cases value with
        | ctor id fields =>
          simp only [Except.map, Value.toReference, Array.attach_map_val, bind, Except.bind]
          cases Ix.Ixby.selectCase program id alternatives with
          | error error => rfl
          | ok target =>
            simp only [bind, Except.bind, ← Frame.transfer_sim]
            cases frame.transfer limits program target fields <;>
              simp [Except.map, bind, Except.bind, State.toReference]
        | _ => simp [Except.map, bind, Except.bind]
    | caseNat operand ifZero ifSucc =>
      simp only [← Frame.read_sim]
      cases frame.read operand with
      | error error => rfl
      | ok value =>
        cases value with
        | scalar scalar =>
          cases scalar with
          | nat n =>
            cases n with
            | zero =>
              simp only [Except.map, Value.toReference, bind, Except.bind]
              have transfer := Frame.transfer_sim frame limits program ifZero #[]
              simp only [Array.map_empty] at transfer
              rw [← transfer]
              cases frame.transfer limits program ifZero #[] <;>
                simp [Except.map, bind, Except.bind, State.toReference]
            | succ n =>
              simp only [Except.map, Value.toReference, bind, Except.bind]
              have transfer := Frame.transfer_sim frame limits program ifSucc #[.scalar (.nat n)]
              simp only [Array.map_singleton, Value.toReference] at transfer
              rw [← transfer]
              cases frame.transfer limits program ifSucc #[.scalar (.nat n)] <;>
                simp [Except.map, bind, Except.bind, State.toReference]
          | _ => simp [Except.map, bind, Except.bind]
        | _ => simp [Except.map, bind, Except.bind]
    | branch operand ifTrue ifFalse =>
      simp only [← Frame.read_sim]
      cases frame.read operand with
      | error error => rfl
      | ok value =>
        cases value with
        | scalar scalar =>
          cases scalar with
          | bool condition =>
            simp only [Except.map, Value.toReference, bind, Except.bind]
            have transfer := Frame.transfer_sim frame limits program
              (if condition then ifTrue else ifFalse) #[]
            simp only [Array.map_empty] at transfer
            rw [← transfer]
            cases frame.transfer limits program (if condition then ifTrue else ifFalse) #[] <;>
              simp [Except.map, bind, Except.bind, State.toReference]
          | _ => simp [Except.map, bind, Except.bind]
        | _ => simp [Except.map, bind, Except.bind]

end Compilatrix.Ixby.Runtime.Chunked
