import Ix.Compiler.X86.ScalarSafety
import Ix.Compiler.X86.WordRegionSafeMacros

namespace Ix.Compiler.X86.Scalar
open WordRegion

def pushHoles {layout : Layout} (frame : Frame layout) (holes : Stream.Holes) : Stream.Holes :=
  Stream.clearRange holes (layout.address frame.baseIndex) 8

def enterHoles {layout : Layout} (frame : Frame layout) (parameters : Nat) (holes : Stream.Holes) : Stream.Holes :=
  let pushed := pushHoles frame holes
  let first := if 0 < parameters then Stream.clearRange pushed (layout.address (frame.localIndex 0)) 8 else pushed
  if 1 < parameters then Stream.clearRange first (layout.address (frame.localIndex 1)) 8 else first

theorem HolesIn.enter {layout : Layout} {rootTop : Nat} {holes : Stream.Holes}
    (valid : HolesIn layout rootTop holes) (frame : Frame layout) (parameters : Nat) :
    HolesIn layout rootTop (enterHoles frame parameters holes) := by
  have pushed := valid.clear (layout.address frame.baseIndex) 8
  unfold enterHoles pushHoles
  split <;> (try split)
  · exact (pushed.clear _ _).clear _ _
  · exact pushed.clear _ _
  · exact pushed.clear _ _
  · exact pushed

theorem frame_safeTrace {layout : Layout} {returns : List ReturnFrame}
    (frame : Frame layout) (state : State) (holes : Stream.Holes)
    (stack : state.registers .rsp = layout.address frame.top)
    (frames : FramesAbove layout frame.top returns) :
    SafeTrace layout returns [.push .rbp, .mov .w64 .rbp (.reg .rsp), .allocFrame frameSize]
      state holes (frameState frame state) (pushHoles frame holes) := by
  have pushed : SafeTrace layout returns [.push .rbp] state holes (pushState frame state) (pushHoles frame holes) :=
    SafeTrace.push _ _ _ _ _ _ frame.base_bound (by rw [stack, frame.push_address]) (frame.base_disjoint frames)
  have setBase : SafeTrace layout returns [.mov .w64 .rbp (.reg .rsp)]
      (pushState frame state) (pushHoles frame holes)
      ((pushState frame state).setReg .rbp (layout.address frame.baseIndex)) (pushHoles frame holes) := by
    simpa [pushState] using SafeTrace.mov layout returns (pushState frame state) (pushHoles frame holes) .rbp (.reg .rsp)
  have allocate : SafeTrace layout returns [.allocFrame frameSize]
      ((pushState frame state).setReg .rbp (layout.address frame.baseIndex)) (pushHoles frame holes)
      (frameState frame state) (pushHoles frame holes) := by
    simpa [frameState, pushState, frame.allocate_address] using
      SafeTrace.allocFrame layout returns ((pushState frame state).setReg .rbp (layout.address frame.baseIndex))
        (pushHoles frame holes) frameSize
  exact pushed.append (setBase.append allocate)

theorem enter_safeTrace {layout : Layout} {returns : List ReturnFrame}
    (frame : Frame layout) (parameters : Nat) (state : State) (holes : Stream.Holes)
    (stack : state.registers .rsp = layout.address frame.top)
    (frames : FramesAbove layout frame.top returns) :
    SafeTrace layout returns (prologue parameters) state holes
      (enterState frame parameters state) (enterHoles frame parameters holes) := by
  have first : SafeTrace layout returns [.spill (slot 0) .rdi] (frameState frame state) (pushHoles frame holes)
      ((frameState frame state).setWord (frame.localIndex 0) (state.registers .rdi))
      (Stream.clearRange (pushHoles frame holes) (layout.address (frame.localIndex 0)) 8) := by
    simpa [frameState, pushState] using SafeTrace.spill layout returns (frameState frame state) (pushHoles frame holes)
      (slot 0) .rdi (frame.localIndex 0) (frame.local_bound 0)
      (by simpa [frameState, pushState] using frame.local_address (index := 0) (by decide)) (frame.local_disjoint frames 0)
  have second (ready : State) (currentHoles : Stream.Holes)
      (base : ready.registers .rbp = layout.address frame.baseIndex)
      (argument : ready.registers .rsi = state.registers .rsi) :
      SafeTrace layout returns [.spill (slot 1) .rsi] ready currentHoles
        (ready.setWord (frame.localIndex 1) (state.registers .rsi))
        (Stream.clearRange currentHoles (layout.address (frame.localIndex 1)) 8) := by
    simpa [argument] using SafeTrace.spill layout returns ready currentHoles (slot 1) .rsi (frame.localIndex 1)
      (frame.local_bound 1) (by rw [base]; exact frame.local_address (by decide)) (frame.local_disjoint frames 1)
  unfold prologue enterState enterHoles
  by_cases one : 0 < parameters
  · by_cases two : 1 < parameters
    · simpa only [if_pos one, if_pos two] using
        ((frame_safeTrace frame state holes stack frames).append first).append
          (second _ _ (by simp [frameState, pushState]) (by simp [frameState, pushState]))
    · simpa only [if_pos one, if_neg two, List.append_nil] using
        (frame_safeTrace frame state holes stack frames).append first
  · have two : ¬1 < parameters := by omega
    simpa only [if_neg one, if_neg two, List.append_nil] using frame_safeTrace frame state holes stack frames

theorem leave_safeTrace {layout : Layout} {returns : List ReturnFrame} {rootTop : Nat}
    (frame : Frame layout) (state : State) (holes : Stream.Holes) (framed : Framed frame state)
    (valid : HolesIn layout rootTop holes) :
    SafeTrace layout returns epilogue state holes (leaveState frame state) holes := by
  have freed : SafeTrace layout returns [.freeFrame frameSize] state holes
      (state.setReg .rsp (layout.address frame.baseIndex)) holes := by
    simpa [framed.2, frame.free_address] using SafeTrace.freeFrame layout returns state holes frameSize
  have popped : SafeTrace layout returns [.pop .rbp] (state.setReg .rsp (layout.address frame.baseIndex)) holes
      (leaveState frame state) holes := by
    simpa [leaveState, frame.pop_address] using SafeTrace.pop layout returns
      (state.setReg .rsp (layout.address frame.baseIndex)) holes .rbp frame.baseIndex frame.base_bound (by simp)
      (valid.readable frame.base_bound (.inl frame.base_ordinary))
  exact freed.append popped

end Ix.Compiler.X86.Scalar
