import Compilatrix.Ixby.Runtime.Chunked.FrameSimulation
import Compilatrix.Ixby.Runtime.Chunked.PrimitiveSimulation

namespace Compilatrix.Ixby.Runtime.Chunked

open Ix.Ixby (Limits Program Error)

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

theorem stepApply_sim (limits : Limits) (program : Program) (state : State)
    (value : Value) (args : Array Value) :
    (stepApply limits program state value args).map Transition.toReference =
      Ix.Ixby.stepApply limits program state.toReference value.toReference
        (args.map Value.toReference) := by
  simp only [stepApply, Ix.Ixby.stepApply, array_isEmpty_map]
  split
  · simp [Except.map, State.toReference]
  · cases value with
    | pap callee captured =>
      simp only [Value.toReference, Array.attach_map_val]
      cases found : program.getFunction callee with
      | error error => rfl
      | ok function =>
        simp only [bind, Except.bind, Array.size_map]
        split
        · rfl
        · simp only [← Array.map_append, Array.size_map]
          split
          · simp [Except.map, State.toReference, Array.attach_map_val]
          · simp only [← Array.map_extract, array_isEmpty_map]
            have pushed := State.push_sim state limits
              (.apply ((captured ++ args).extract function.arity (captured ++ args).size))
            simp only [Continuation.toReference] at pushed
            rw [← pushed, ← enter_sim]
            split
            · cases enter limits program callee ((captured ++ args).extract 0 function.arity) <;>
                simp [Except.map, bind, Except.bind, State.toReference]
            · cases state.push limits
                (.apply ((captured ++ args).extract function.arity (captured ++ args).size)) <;>
                cases enter limits program callee ((captured ++ args).extract 0 function.arity) <;>
                simp [Except.map, bind, Except.bind, State.toReference]
    | _ => simp [Except.map, bind, Except.bind, State.toReference]

end Compilatrix.Ixby.Runtime.Chunked
