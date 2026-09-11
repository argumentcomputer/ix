import Ix.Compiler.X86.WordRegionSafeTrace

namespace Ix.Compiler.X86.WordRegion

theorem SafeTrace.mov (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (destination : GPR) (source : MoveSource) :
    SafeTrace layout returns [.mov .w64 destination source] state holes
      (state.setReg destination (state.move source)) holes :=
  .cons (.mov _ _ _) ⟨trivial, trivial⟩ (.nil _ _)

theorem SafeTrace.alu (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (operation : AluOp) (destination : GPR) (source : AluSource) :
    SafeTrace layout returns [.alu operation .w64 destination source] state holes
      (state.setReg destination (operation.eval (state.registers destination) (state.alu source))) holes :=
  .cons (.alu _ _ _ _) ⟨trivial, trivial⟩ (.nil _ _)

theorem SafeTrace.allocFrame (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (size : FrameSize) :
    SafeTrace layout returns [.allocFrame size] state holes
      (state.setReg .rsp (state.registers .rsp - size.bytes)) holes :=
  .cons (.allocFrame _ _) ⟨trivial, trivial⟩ (.nil _ _)

theorem SafeTrace.freeFrame (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (size : FrameSize) :
    SafeTrace layout returns [.freeFrame size] state holes
      (state.setReg .rsp (state.registers .rsp + size.bytes)) holes :=
  .cons (.freeFrame _ _) ⟨trivial, trivial⟩ (.nil _ _)

theorem SafeTrace.reload (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (destination : GPR) (source : StackSlot) (index : Nat)
    (bound : index < layout.slots)
    (address : state.registers .rbp - source.displacement = layout.address index)
    (readable : Stream.ReadableData holes (layout.address index) 8) :
    SafeTrace layout returns [.reload destination source] state holes
      (state.setReg destination (state.words index)) holes := by
  refine .cons (.reload _ _ _ _ bound address) ?_ (.nil _ _)
  simpa [Stream.OperationSafe, Stream.operationReads, Stream.operationWrites, Encode.instructionOperation,
    Encode.spillAddress_eval, State.core, Core.readReg, address, Width.bytes] using readable

theorem SafeTrace.spill (layout : Layout) (returns : List ReturnFrame) (state : State)
    (holes : Stream.Holes) (destination : StackSlot) (source : GPR) (index : Nat)
    (bound : index < layout.slots)
    (address : state.registers .rbp - destination.displacement = layout.address index)
    (disjoint : Stream.FramesDisjoint returns (layout.address index) 8) :
    SafeTrace layout returns [.spill destination source] state holes
      (state.setWord index (state.registers source)) (Stream.clearRange holes (layout.address index) 8) := by
  refine .cons (.spill _ _ _ _ bound address) ?_ ?_
  · simpa [Stream.OperationSafe, Stream.operationReads, Stream.operationWrites, Encode.instructionOperation,
      Encode.spillAddress_eval, State.core, Core.readReg, address, Width.bytes] using disjoint
  · simpa [Stream.nextHoles, Stream.operationWrites, Encode.instructionOperation,
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
  · simpa [Stream.OperationSafe, Stream.operationReads, Stream.operationWrites, Encode.instructionOperation,
      State.core, Core.readReg, address] using disjoint
  · simpa [Stream.nextHoles, Stream.operationWrites, Encode.instructionOperation,
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
  simpa [Stream.OperationSafe, Stream.operationReads, Stream.operationWrites, Encode.instructionOperation,
    State.core, Core.readReg, address] using readable

end Ix.Compiler.X86.WordRegion
