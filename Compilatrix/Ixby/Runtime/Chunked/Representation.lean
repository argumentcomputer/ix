import Compilatrix.Ixby.Runtime.Chunked.Machine

namespace Compilatrix.Ixby.Runtime.Chunked

@[simp] theorem array_isEmpty_map (values : Array α) (f : α → β) :
    (values.map f).isEmpty = values.isEmpty := by
  simp [Array.isEmpty]

def Frame.toReference (frame : Frame) : Ix.Ixby.Frame :=
  ⟨frame.function, frame.block, frame.locals.map Value.toReference⟩

def Frame.ofReference (frame : Ix.Ixby.Frame) : Frame :=
  ⟨frame.function, frame.block, frame.locals.map Value.ofReference⟩

@[simp] def Control.toReference : Control → Ix.Ixby.Control
  | .eval frame => .eval frame.toReference
  | .apply value args => .apply value.toReference (args.map Value.toReference)
  | .ret value => .ret value.toReference

def Control.ofReference : Ix.Ixby.Control → Control
  | .eval frame => .eval (Frame.ofReference frame)
  | .apply value args => .apply (Value.ofReference value) (args.map Value.ofReference)
  | .ret value => .ret (Value.ofReference value)

@[simp] def Continuation.toReference : Continuation → Ix.Ixby.Continuation
  | .resume frame => .resume frame.toReference
  | .apply args => .apply (args.map Value.toReference)

def Continuation.ofReference : Ix.Ixby.Continuation → Continuation
  | .resume frame => .resume (Frame.ofReference frame)
  | .apply args => .apply (args.map Value.ofReference)

def State.toReference (state : State) : Ix.Ixby.State :=
  ⟨state.control.toReference, state.continuation.map Continuation.toReference⟩

def State.ofReference (state : Ix.Ixby.State) : State :=
  ⟨Control.ofReference state.control, state.continuation.map Continuation.ofReference⟩

@[simp] def Transition.toReference : Transition → Ix.Ixby.Transition
  | .next state => .next state.toReference
  | .halted value => .halted value.toReference

@[simp] def Action.toReference : Action → Ix.Ixby.Action
  | .value result => .value result.toReference
  | .call callee args => .call callee (args.map Value.toReference)
  | .apply fn args => .apply fn.toReference (args.map Value.toReference)

@[simp] theorem Frame.toReference_ofReference (frame : Ix.Ixby.Frame) :
    (Frame.ofReference frame).toReference = frame := by
  simp [Frame.ofReference, Frame.toReference, Array.map_map, Function.comp_def]

@[simp] theorem Control.toReference_ofReference (control : Ix.Ixby.Control) :
    (Control.ofReference control).toReference = control := by
  cases control <;> simp [Control.ofReference, Array.map_map, Function.comp_def]

@[simp] theorem Continuation.toReference_ofReference (cont : Ix.Ixby.Continuation) :
    (Continuation.ofReference cont).toReference = cont := by
  cases cont <;> simp [Continuation.ofReference, Array.map_map, Function.comp_def]

@[simp] theorem State.toReference_ofReference (state : Ix.Ixby.State) :
    (State.ofReference state).toReference = state := by
  simp only [State.ofReference, State.toReference, Array.map_map, Function.comp_def,
    Control.toReference_ofReference, Continuation.toReference_ofReference]
  simp

@[simp] theorem except_map_bind (x : Except ε α) (f : α → Except ε β) (g : β → γ) :
    (x.bind f).map g = x.bind (fun value => (f value).map g) := by
  cases x <;> rfl

@[simp] theorem except_bind_map (x : Except ε α) (f : α → β) (g : β → Except ε γ) :
    (x.map f).bind g = x.bind (fun value => g (f value)) := by
  cases x <;> rfl

end Compilatrix.Ixby.Runtime.Chunked
