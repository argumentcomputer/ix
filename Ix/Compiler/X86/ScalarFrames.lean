import Ix.Compiler.X86.ScalarStack

namespace Ix.Compiler.X86.Scalar
open WordRegion

theorem Frame.push_address {layout : Layout} (frame : Frame layout) :
    layout.address frame.top - 8 = layout.address frame.baseIndex := by
  simpa [Frame.baseIndex] using layout.subtract (slot := frame.top) (count := 1) (by have := frame.enough; omega)

theorem Frame.allocate_address {layout : Layout} (frame : Frame layout) :
    layout.address frame.baseIndex - frameSize.bytes = layout.address frame.stackIndex := by
  have enough := frame.enough
  have result := layout.subtract (slot := frame.baseIndex) (count := 32) (by simp only [Frame.baseIndex]; omega)
  change layout.address frame.baseIndex - 256 = layout.address (frame.baseIndex - 32) at result
  change layout.address frame.baseIndex - 256 = layout.address frame.stackIndex
  simpa [Frame.baseIndex, Frame.stackIndex, Nat.sub_sub] using result

theorem Frame.free_address {layout : Layout} (frame : Frame layout) :
    layout.address frame.stackIndex + frameSize.bytes = layout.address frame.baseIndex := by
  rw [← frame.allocate_address, UInt64.sub_add_cancel]

theorem Frame.pop_address {layout : Layout} (frame : Frame layout) :
    layout.address frame.baseIndex + 8 = layout.address frame.top := by
  rw [← frame.push_address, UInt64.sub_add_cancel]

def pushState {layout : Layout} (frame : Frame layout) (state : State) : State :=
  (state.setReg .rsp (layout.address frame.baseIndex)).setWord frame.baseIndex (state.registers .rbp)

def frameState {layout : Layout} (frame : Frame layout) (state : State) : State :=
  ((pushState frame state).setReg .rbp (layout.address frame.baseIndex)).setReg .rsp (layout.address frame.stackIndex)

def enterState {layout : Layout} (frame : Frame layout) (parameters : Nat) (state : State) : State :=
  let ready := frameState frame state
  let first := if 0 < parameters then ready.setWord (frame.localIndex 0) (state.registers .rdi) else ready
  if 1 < parameters then first.setWord (frame.localIndex 1) (state.registers .rsi) else first

theorem frame_trace {layout : Layout} (frame : Frame layout) (state : State)
    (stack : state.registers .rsp = layout.address frame.top) :
    Trace layout [.push .rbp, .mov .w64 .rbp (.reg .rsp), .allocFrame frameSize] state (frameState frame state) := by
  have pushed : Trace layout [.push .rbp] state (pushState frame state) :=
    .cons (.push _ _ _ frame.base_bound (by rw [stack, frame.push_address])) (.nil _)
  have setBase : Trace layout [.mov .w64 .rbp (.reg .rsp)] (pushState frame state)
      ((pushState frame state).setReg .rbp (layout.address frame.baseIndex)) := by
    simpa [pushState] using Trace.cons (Effect.mov (pushState frame state) .rbp (.reg .rsp)) (Trace.nil _)
  have allocate : Trace layout [.allocFrame frameSize]
      ((pushState frame state).setReg .rbp (layout.address frame.baseIndex)) (frameState frame state) := by
    simpa [frameState, pushState, frame.allocate_address] using
      Trace.cons (Effect.allocFrame ((pushState frame state).setReg .rbp (layout.address frame.baseIndex)) frameSize)
        (Trace.nil _)
  exact pushed.append (setBase.append allocate)

theorem enter_framed {layout : Layout} (frame : Frame layout) (parameters : Nat) (state : State) :
    Framed frame (enterState frame parameters state) := by
  simp only [enterState]
  split <;> (try split) <;>
    simp [Framed, frameState, pushState, State.setReg_registers]

theorem enter_trace {layout : Layout} (frame : Frame layout) (parameters : Nat) (state : State)
    (stack : state.registers .rsp = layout.address frame.top) :
    Trace layout (prologue parameters) state (enterState frame parameters state) := by
  have first : Trace layout [.spill (slot 0) .rdi] (frameState frame state)
      ((frameState frame state).setWord (frame.localIndex 0) (state.registers .rdi)) := by
    have store := Effect.spill (frameState frame state) (slot 0) .rdi (frame.localIndex 0)
      (frame.local_bound 0) (by simpa [frameState, pushState] using frame.local_address (index := 0) (by decide))
    simpa [frameState, pushState] using Trace.cons store (Trace.nil _)
  have second (ready : State) (base : ready.registers .rbp = layout.address frame.baseIndex)
      (argument : ready.registers .rsi = state.registers .rsi) :
      Trace layout [.spill (slot 1) .rsi] ready (ready.setWord (frame.localIndex 1) (state.registers .rsi)) := by
    have store := Effect.spill ready (slot 1) .rsi (frame.localIndex 1) (frame.local_bound 1)
      (by rw [base]; exact frame.local_address (by decide))
    simpa [argument] using Trace.cons store (Trace.nil _)
  unfold prologue enterState
  by_cases one : 0 < parameters
  · by_cases two : 1 < parameters
    · simpa only [if_pos one, if_pos two] using
        ((frame_trace frame state stack).append first).append
          (second _ (by simp [frameState, pushState]) (by simp [frameState, pushState]))
    · simpa only [if_pos one, if_neg two, List.append_nil] using (frame_trace frame state stack).append first
  · have two : ¬1 < parameters := by omega
    simpa only [if_neg one, if_neg two, List.append_nil] using frame_trace frame state stack

def ArgumentsAt (values : Array Word) (state : State) : Prop :=
  values.size ≤ 2 ∧ ∀ index (bound : index < values.size),
    values[index] = if index = 0 then state.registers .rdi else state.registers .rsi

theorem enter_values {layout : Layout} (frame : Frame layout) (state : State) (values : Array Word)
    (arguments : ArgumentsAt values state) : ValuesAt frame values (enterState frame values.size state) := by
  refine ⟨by have := arguments.1; simp only [maxLocals]; omega, ?_⟩
  intro index bound
  have arity := arguments.1
  have enough := frame.enough
  have indexCases : index = 0 ∨ index = 1 := by omega
  rcases indexCases with rfl | rfl
  · have one : 0 < values.size := bound
    have different : frame.localIndex 0 ≠ frame.localIndex 1 := by
      simp only [Frame.localIndex]
      omega
    rw [arguments.2 0 bound]
    simp only [enterState, if_pos one]
    split <;> simp [Words.set, different]
  · have one : 0 < values.size := by omega
    have two : 1 < values.size := bound
    rw [arguments.2 1 bound]
    simp [enterState, if_pos one, if_pos two]

theorem enter_words_above {layout : Layout} (frame : Frame layout) (parameters : Nat) (state : State)
    (index : Nat) (above : frame.top ≤ index) :
    (enterState frame parameters state).words index = state.words index := by
  have enough := frame.enough
  simp only [enterState]
  split <;> (try split) <;>
    simp (discharger := omega) [frameState, pushState, Words.set, Frame.baseIndex, Frame.localIndex, if_neg] <;> omega

theorem enter_savedBase {layout : Layout} (frame : Frame layout) (parameters : Nat) (state : State) :
    (enterState frame parameters state).words frame.baseIndex = state.registers .rbp := by
  have enough := frame.enough
  simp only [enterState]
  split <;> (try split) <;>
    simp (discharger := omega) [frameState, pushState, Words.set, Frame.baseIndex, Frame.localIndex, if_neg] <;> omega

def leaveState {layout : Layout} (frame : Frame layout) (state : State) : State :=
  (state.setReg .rsp (layout.address frame.top)).setReg .rbp (state.words frame.baseIndex)

theorem leave_trace {layout : Layout} (frame : Frame layout) (state : State) (framed : Framed frame state) :
    Trace layout epilogue state (leaveState frame state) := by
  have freed : Trace layout [.freeFrame frameSize] state (state.setReg .rsp (layout.address frame.baseIndex)) := by
    simpa [framed.2, frame.free_address] using Trace.cons (Effect.freeFrame state frameSize) (Trace.nil _)
  have popped : Trace layout [.pop .rbp] (state.setReg .rsp (layout.address frame.baseIndex))
      (leaveState frame state) := by
    simpa [leaveState, frame.pop_address] using Trace.cons
      (Effect.pop (state.setReg .rsp (layout.address frame.baseIndex)) .rbp frame.baseIndex frame.base_bound (by simp))
      (Trace.nil _)
  exact freed.append popped

end Ix.Compiler.X86.Scalar
