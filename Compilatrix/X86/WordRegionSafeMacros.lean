import Compilatrix.X86.WordRegionSafeTrace

namespace Compilatrix.X86.WordRegion

@[simp] theorem State.address_normalized (state : State) (address : MemAddr) :
    state.address (Encode.normalizedAddress address) = state.address address :=
  Encode.normalizedAddress_eval address (state.core Memory.unmapped)

theorem SafeTrace.load (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (destination : GPR) (source : MemAddr) (index : Nat)
    (bound : index < layout.slots) (address : state.address source = layout.address index)
    (readable : Stream.ReadableData holes (layout.address index) 8) :
    SafeTrace layout returns [.load .w64 destination source] state holes
      (state.setReg destination (state.words index)) holes := by
  refine .cons (.load _ _ _ _ bound address) ?_ (.nil _ _)
  simpa [Stream.OperationSafe,
    State.address_core, address, Width.bytes] using readable

theorem SafeTrace.store (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (destination : MemAddr) (source : GPR) (index : Nat)
    (bound : index < layout.slots) (address : state.address destination = layout.address index)
    (disjoint : Stream.FramesDisjoint returns (layout.address index) 8) :
    SafeTrace layout returns [.store .w64 destination source] state holes
      (state.setWord index (state.registers source)) (Stream.clearRange holes (layout.address index) 8) := by
  refine .cons (.store _ _ _ _ bound address) ?_ ?_
  · simpa [Stream.OperationSafe,
      State.address_core, address, Width.bytes] using disjoint
  · simpa [Stream.nextHoles, Stream.clearAccesses,
      State.address_core, address, Width.bytes] using
      SafeTrace.nil (layout := layout) (returns := returns) (state.setWord index (state.registers source))
        (Stream.clearRange holes (layout.address index) 8)

/-- An instruction that touches no memory is safe and keeps the mask. -/
theorem quietStep {layout : Layout} {returns : List ReturnFrame} {instruction : Instr} {state after : State}
    {holes : Stream.Holes} (effect : Effect layout instruction state after)
    (reads : Stream.operationReads (Encode.instructionOperation instruction) (state.core Memory.unmapped) = [])
    (writes : Stream.operationWrites (Encode.instructionOperation instruction) (state.core Memory.unmapped) = []) :
    SafeTrace layout returns [instruction] state holes after holes := by
  have next : Stream.nextHoles holes (Encode.instructionOperation instruction) (state.core Memory.unmapped) = holes := by
    simp [Stream.nextHoles, writes, Stream.clearAccesses]
  refine .cons effect ⟨by simp [reads], by simp [writes]⟩ ?_
  rw [next]
  exact .nil _ _

theorem SafeTrace.mov (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (destination : GPR) (source : MoveSource) :
    SafeTrace layout returns [.mov .w64 destination source] state holes
      (state.setReg destination (state.move source)) holes :=
  quietStep (.mov _ _ _) (Stream.footprint_mov .w64 destination source _).1 (Stream.footprint_mov .w64 destination source _).2

theorem SafeTrace.alu (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (operation : AluOp) (destination : GPR) (source : AluSource) :
    SafeTrace layout returns [.alu operation .w64 destination source] state holes
      (state.setReg destination (operation.eval (state.registers destination) (state.alu source))) holes :=
  quietStep (.alu _ _ _ _) (Stream.footprint_alu operation .w64 destination source _).1
    (Stream.footprint_alu operation .w64 destination source _).2

theorem SafeTrace.allocFrame (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (size : FrameSize) :
    SafeTrace layout returns [.allocFrame size] state holes
      (state.setReg .rsp (state.registers .rsp - size.bytes)) holes :=
  quietStep (.allocFrame _ _) (Stream.footprint_frame size _).1 (Stream.footprint_frame size _).2.1

theorem SafeTrace.freeFrame (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (size : FrameSize) :
    SafeTrace layout returns [.freeFrame size] state holes
      (state.setReg .rsp (state.registers .rsp + size.bytes)) holes :=
  quietStep (.freeFrame _ _) (Stream.footprint_frame size _).2.2.1 (Stream.footprint_frame size _).2.2.2

theorem SafeTrace.reload (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (destination : GPR) (source : StackSlot) (index : Nat)
    (bound : index < layout.slots)
    (address : state.registers .rbp - source.displacement = layout.address index)
    (readable : Stream.ReadableData holes (layout.address index) 8) :
    SafeTrace layout returns [.reload destination source] state holes
      (state.setReg destination (state.words index)) holes := by
  refine .cons (.reload _ _ _ _ bound address) ?_ (.nil _ _)
  simpa [Stream.OperationSafe,
    Encode.spillAddress_eval, State.core, Core.readReg, address, Width.bytes] using readable

theorem SafeTrace.spill (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (destination : StackSlot) (source : GPR) (index : Nat)
    (bound : index < layout.slots)
    (address : state.registers .rbp - destination.displacement = layout.address index)
    (disjoint : Stream.FramesDisjoint returns (layout.address index) 8) :
    SafeTrace layout returns [.spill destination source] state holes
      (state.setWord index (state.registers source)) (Stream.clearRange holes (layout.address index) 8) := by
  refine .cons (.spill _ _ _ _ bound address) ?_ ?_
  · simpa [Stream.OperationSafe,
      Encode.spillAddress_eval, State.core, Core.readReg, address, Width.bytes] using disjoint
  · simpa [Stream.nextHoles, Stream.clearAccesses,
      Encode.spillAddress_eval, State.core, Core.readReg, address, Width.bytes] using
      SafeTrace.nil (layout := layout) (returns := returns) (state.setWord index (state.registers source))
        (Stream.clearRange holes (layout.address index) 8)

theorem SafeTrace.push (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (source : GPR) (index : Nat) (bound : index < layout.slots)
    (address : state.registers .rsp - 8 = layout.address index)
    (disjoint : Stream.FramesDisjoint returns (layout.address index) 8) :
    SafeTrace layout returns [.push source] state holes
      ((state.setReg .rsp (layout.address index)).setWord index (state.registers source))
      (Stream.clearRange holes (layout.address index) 8) := by
  refine .cons (.push _ _ _ bound address) ?_ ?_
  · simpa [Stream.OperationSafe,
      State.core, Core.readReg, address] using disjoint
  · simpa [Stream.nextHoles, Stream.clearAccesses,
      State.core, Core.readReg, address] using SafeTrace.nil (layout := layout) (returns := returns)
      ((state.setReg .rsp (layout.address index)).setWord index (state.registers source))
      (Stream.clearRange holes (layout.address index) 8)

theorem SafeTrace.pop (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (destination : GPR) (index : Nat) (bound : index < layout.slots)
    (address : state.registers .rsp = layout.address index)
    (readable : Stream.ReadableData holes (layout.address index) 8) :
    SafeTrace layout returns [.pop destination] state holes
      ((state.setReg .rsp (layout.address index + 8)).setReg destination (state.words index)) holes := by
  refine .cons (.pop _ _ _ bound address) ?_ (.nil _ _)
  simpa [Stream.OperationSafe,
    State.core, Core.readReg, address] using readable

end Compilatrix.X86.WordRegion
