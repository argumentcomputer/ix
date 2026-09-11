import Compilatrix.X86.AllocatingMemory

namespace Compilatrix.X86.Allocating
open UniqueABI UniqueTarget UniqueExecution

structure CallSite (checked : Checked) (block : BlockId) (offset : Nat) : Prop where
  prepare : Straight.Segment checked block offset [.alu .sub .w64 .rsp (.imm 8)]
  call : Straight.Segment checked block (offset + 1) [.call 28]
  restore : Straight.Segment checked block (offset + 2) [.alu .add .w64 .rsp (.imm 8)]
  fits : offset + 3 < UInt32.size

def token (block : BlockId) (offset : Nat) : Word :=
  (PC.mk block (UInt32.ofNat (offset + 2))).encode

theorem allocate_rsp (state : State) (layout : Layout) (index : Nat) (pointer : Word) :
    allocateState (state.setReg .rsp pointer) layout index nilTag 0 (.imm 0) .rsi =
      (allocateState state layout index nilTag 0 (.imm 0) .rsi).setReg .rsp pointer := by
  apply State.ext
  · funext register
    cases register <;> simp [allocateState, prepareAllocation, writeSourceState, counterState, State.setReg,
      State.setWord, Registers.set, State.move, MoveSource.eval]
  · change (allocateState (state.setReg .rsp pointer) layout index nilTag 0 (.imm 0) .rsi).words =
      (allocateState state layout index nilTag 0 (.imm 0) .rsi).words
    rw [allocateState_words _ _ _ _ _ _ _ rfl, allocateState_words _ _ _ _ _ _ _ rfl]
    rfl

/-- One actual native call performs exactly the established allocation
effect. The caller's other registers, heap reservations, and exposed fields
survive the call; the only additional memory effect is its concrete return
slot. The theorem admits arbitrary heap word views, including reservations. -/
theorem allocatorSteps (layout : Layout) (state : State) (index : Nat)
    (bound : index < layout.capacity) (context : state.registers .rdi = layout.base)
    (cursor : state.words Field.cursor.index = UInt64.ofNat (cellBytes * index))
    (stack : Stack layout) (pointer : state.registers .rsp = stack.top)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory)
    (available : stack.Available memory) (checked : Checked) (block : BlockId) (offset : Nat)
    (site : CallSite checked block offset)
    (calleeCode : BlockCode checked 28 (allocate nilTag 0 (.imm 0) .rsi) .ret) :
    ∃ nextMemory, Realizes layout (outside.write64 stack.slot (token block offset))
        (allocateState state layout index nilTag 0 (.imm 0) .rsi).words nextMemory ∧
      Stream.SafeSteps Runtime.rejecting checked 24 (fun _ => False) (leaf (state.core memory) block offset)
        stack.holes (leaf ((allocateState state layout index nilTag 0 (.imm 0) .rsi).core nextMemory) block (offset + 3)) := by
  let padded := state.setReg .rsp (stack.top - 8)
  let called := state.setReg .rsp stack.slot
  let callMemory := memory.write64 stack.slot (token block offset)
  let callOutside := outside.write64 stack.slot (token block offset)
  let frame := callFrame (padded.core memory) block (offset + 1)
  let allocated := allocateState called layout index nilTag 0 (.imm 0) .rsi
  let after := allocateState state layout index nilTag 0 (.imm 0) .rsi
  have subTrace : Trace layout [.alu .sub .w64 .rsp (.imm 8)] state padded := by
    simpa [padded, AluOp.eval, signExtend32, pointer] using
      Trace.cons (Effect.alu (layout := layout) state .sub .rsp (.imm 8)) (Trace.nil _)
  have subSteps := subTrace.safeSteps_readOnly rfl (HeapAccess.empty layout) outside memory represented
    Runtime.rejecting checked block offset site.prepare (by have := site.fits; simpa using (show offset + 1 < UInt32.size by omega))
  have paddedPointer : padded.registers .rsp - 8 = stack.slot := by simp [padded, stack.subtract.2]
  have calledView : Realizes layout callOutside called.words callMemory :=
    represented.writeOutside stack.slot (token block offset) (fun i bound => stack.outside (by decide : 0 < 3) bound)
  have callEffect := call_inFrame site.call (by have := site.fits; omega) calleeCode.hasBlock Runtime.rejecting
    (padded.core memory) [] (by simpa [padded, State.core, Core.readReg] using stack.callAligned)
    (by simpa only [State.core, Core.readReg, paddedPointer, Stack.slot] using available.2 0 (by decide))
  have callCoreEq : callCore (padded.core memory) block (offset + 1) = called.core callMemory := by
    simp [callCore, callFrame, padded, called, callMemory, token, State.core, State.setReg, Registers.set,
      Core.readReg, Core.setReg, stack.subtract.2, UInt32.add_assoc]
  rw [callCoreEq] at callEffect
  obtain ⟨callBlock, callFound, callReads⟩ := site.call
  have callAt := callReads 0 (by simp)
  simp only [Nat.add_zero, List.getElem?_cons_zero] at callAt
  have safe : Stream.SafeAt checked.program (fun _ => False) (leaf (padded.core memory) block (offset + 1)) := by
    simp only [Stream.SafeAt, leaf, UInt32.toNat_ofNat_of_lt' (by have := site.fits; omega : offset + 1 < UInt32.size),
      callFound, callAt]
    simpa [State.core, Core.readReg, paddedPointer, Stream.FramesDisjoint, padded, stack.subtract.2, Stack.slot] using
      And.intro stack.callAligned (available.2 0 (by decide))
  have holeStep : Stream.holeStep checked.program (leaf (padded.core memory) block (offset + 1)) (fun _ => False) = stack.holes := by
    simp only [Stream.holeStep, leaf, UInt32.toNat_ofNat_of_lt' (by have := site.fits; omega : offset + 1 < UInt32.size),
      callFound, callAt, State.core, Core.readReg, paddedPointer, Stack.holes]
  have callSteps : Stream.SafeSteps Runtime.rejecting checked 1 (fun _ => False)
      (leaf (padded.core memory) block (offset + 1)) stack.holes (inFrame (called.core callMemory) 28 0 [frame]) := by
    simpa only [holeStep] using Stream.SafeSteps.single safe callEffect
  have frameSlot : frame.returnSlot = stack.slot := by simp [frame, callFrame, State.core, Core.readReg, paddedPointer]
  have access : HeapAccess layout stack.holes [frame] := stack.heapAccess [frame] (by simpa using frameSlot)
  have allocation := allocateTrace layout called index nilTag 0 (.imm 0) .rsi bound
    (by simpa [called] using context) cursor
  obtain ⟨allocatedMemory, allocatedView, allocationSteps⟩ := allocation.safeSteps access callOutside callMemory calledView
    Runtime.rejecting checked 28 0 calleeCode.segment (by simpa using calleeCode.fits)
  simp only [Nat.zero_add] at allocationSteps
  change Realizes layout callOutside allocated.words allocatedMemory at allocatedView
  have allocationPermissions := allocationSteps.steps.rejecting_permissions
  have slotValue : allocatedMemory.read64 stack.slot = frame.continuation.encode := by
    rw [calledView.readOutside allocatedView stack.slot (fun i bound => stack.outside (by decide : 0 < 3) bound)]
    simp [callMemory, Memory.read64_write64, frame, callFrame, token, UInt32.add_assoc]
  have slotReadable : allocatedMemory.read64? stack.slot = .ok frame.continuation.encode := by
    have permissions : allocatedMemory.readable = memory.readable := by simpa [callMemory, inFrame, State.core] using allocationPermissions.1
    have readable : Memory.rangeAllowed memory.readable stack.slot 8 = true := available.1 0 (by decide)
    simp only [Memory.read64?, Memory.read?, Width.bytes, permissions, readable, ↓reduceIte]
    exact congrArg Except.ok slotValue
  have allocatedEq : allocated = after.setReg .rsp stack.slot := allocate_rsp state layout index stack.slot
  have afterView : Realizes layout callOutside after.words allocatedMemory := by
    rw [allocatedEq] at allocatedView
    exact allocatedView
  have saved : (allocated.core allocatedMemory).calleeSavedMatch frame.calleeSaved = true := by
    have kept := allocateState_saved called layout index nilTag 0 (.imm 0) .rsi rfl
    have same := (kept.core callMemory allocatedMemory).2
    simp only [Core.calleeSavedMatch]
    rw [show (allocated.core allocatedMemory).calleeSavedSnapshot = (called.core callMemory).calleeSavedSnapshot from same]
    simp [frame, callFrame, called, padded, State.core, Core.calleeSavedSnapshot, SysV.calleeSaved, Core.readReg]
  have retSteps := calleeCode.safe_ret Runtime.rejecting (allocated.core allocatedMemory) frame [] stack.holes
    (by simp [allocatedEq, frameSlot, State.core, Core.readReg])
    (by simpa [frameSlot, State.core] using slotReadable) saved
  let restored := after.setReg .rsp (stack.slot + 8)
  have framePC : frame.continuation = ⟨block, UInt32.ofNat (offset + 2)⟩ := rfl
  have retShape : Machine.mk ((allocated.core allocatedMemory).setReg .rsp (frame.returnSlot + 8))
      frame.continuation [] .running =
      leaf (restored.core allocatedMemory) block (offset + 2) := by
    rw [allocatedEq, frameSlot, framePC]
    simp [restored, leaf, State.core, State.setReg, Core.setReg]
  rw [retShape] at retSteps
  have addTrace : Trace layout [.alu .add .w64 .rsp (.imm 8)] restored after := by
    have afterRsp : after.registers .rsp = stack.top :=
      ((allocateState_saved state layout index nilTag 0 (.imm 0) .rsi rfl) .rsp rfl).trans pointer
    have stackRestored : (restored.setReg .rsp (restored.registers .rsp + 8)) = after := by
      apply State.ext
      · funext register
        cases register <;> simp [restored, stack.add.2, afterRsp]
      · rfl
    simpa [AluOp.eval, signExtend32, stackRestored] using
      Trace.cons (Effect.alu (layout := layout) restored .add .rsp (.imm 8)) (Trace.nil _)
  have restoredView : Realizes layout callOutside restored.words allocatedMemory := by
    exact afterView
  have addSteps := addTrace.safeSteps_readOnly rfl (stack.heapAccess [] (by simp)) callOutside allocatedMemory restoredView
    Runtime.rejecting checked block (offset + 2) site.restore (by simpa using site.fits)
  refine ⟨allocatedMemory, ?_, ?_⟩
  · exact afterView
  · have all := subSteps.append (callSteps.append (allocationSteps.append (retSteps.append addSteps)))
    simpa only [allocate_length, List.length_cons, List.length_nil, Nat.add_zero, Nat.add_assoc,
      Nat.reduceAdd, inFrame, leaf, after] using all

end Compilatrix.X86.Allocating
