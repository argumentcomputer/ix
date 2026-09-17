import Compilatrix.Ixby.Runtime.Chunked.EvalSimulation
import Compilatrix.Ixby.Runtime.Chunked.ApplySimulation
import Compilatrix.Ixby.Runtime.Chunked.Execute
import Compilatrix.Ixby.Runtime.Execute

namespace Compilatrix.Ixby.Runtime.Chunked

open Ix.Ixby (Limits Program Error)

theorem step_sim (limits : Limits) (program : Program) (state : State) :
    (step limits program state).map Transition.toReference =
      Ix.Ixby.step limits program state.toReference := by
  cases state with
  | mk control continuation =>
    cases control with
    | eval frame => exact stepEval_sim limits program _ frame
    | apply fn args => exact stepApply_sim limits program _ fn args
    | ret value =>
      simp only [step, Ix.Ixby.step, State.toReference, Control.toReference, Array.back?_map]
      cases last : continuation.back? with
      | none => simp [Except.map, bind, Except.bind]
      | some cont =>
        cases cont with
        | apply args =>
          simp [Except.map, bind, Except.bind, State.toReference]
        | resume frame =>
          simp only [Option.map_some, Continuation.toReference]
          have transfer := Frame.transfer_sim frame limits program frame.block #[value]
          simp only [Array.map_singleton] at transfer
          have block : frame.toReference.block = frame.block := rfl
          rw [block, ← transfer]
          cases frame.transfer limits program frame.block #[value] <;>
            simp [Except.map, bind, Except.bind, State.toReference]

theorem run_sim (limits : Limits) (program : Program) (fuel : Nat) (state : State) :
    (run limits program fuel state).map Value.toReference =
      Ix.Ixby.run limits program fuel state.toReference := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [run, Ix.Ixby.run, ← step_sim]
    cases advanced : step limits program state with
    | error error => rfl
    | ok transition =>
      cases transition with
      | halted value => rfl
      | next nextState => simpa only [Except.map, Transition.toReference] using ih nextState

@[simp] theorem initialState_sim (limits : Limits) (program : Program)
    (input : Array Ix.Ixby.Value) :
    (initialState limits program input).map State.toReference =
      Ix.Ixby.initialState limits program input := by
  simp only [initialState]
  cases Ix.Ixby.initialState limits program input <;> simp [Except.map]

/-- Equality for every program, input, semantic limit and exact fuel budget;
failure ordering and out-of-fuel behavior are included. -/
theorem execute_sim (limits : Limits) (program : Program) (input : Array Ix.Ixby.Value)
    (fuel : Nat) :
    execute limits program input fuel = Ix.Ixby.execute limits program input fuel := by
  simp only [execute, Ix.Ixby.execute, initialState]
  cases initialized : Ix.Ixby.initialState limits program input with
  | error error => rfl
  | ok state =>
    simpa only [Except.map, bind, Except.bind, State.toReference_ofReference] using
      run_sim limits program fuel (State.ofReference state)

/-- The resumable runner reports exactly the reference logical-transition
counter. No chunk copy or flatten operation creates a guest transition. -/
theorem runChunk_sim (limits : Limits) (program : Program) (fuel : Nat)
    (state : State) (count : Nat) :
    (runChunk limits program fuel state count).map chunkToReference =
      Runtime.runChunk limits program fuel state.toReference count := by
  induction fuel generalizing state count with
  | zero => rfl
  | succ fuel ih =>
    simp only [runChunk, Runtime.runChunk, ← step_sim]
    cases advanced : step limits program state with
    | error error => rfl
    | ok transition =>
      cases transition with
      | halted value => rfl
      | next nextState =>
        simpa only [Except.map, Transition.toReference, bind, Except.bind] using
          ih nextState (count + 1)

end Compilatrix.Ixby.Runtime.Chunked
