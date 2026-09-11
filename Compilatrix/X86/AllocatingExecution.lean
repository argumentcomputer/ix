import Compilatrix.X86.AllocatingTarget
import Compilatrix.X86.AllocatingFirst
import Compilatrix.X86.UniqueSafeLoop
import Compilatrix.X86.RuntimeInput

namespace Compilatrix.X86.Allocating
open UniqueABI UniqueTarget UniqueExecution

theorem emptySteps (layout : Layout) (state : State)
    (capacity : 2 ≤ layout.capacity) (context : state.registers .rdi = layout.base)
    (root : state.registers .rdx = layout.cell 0) (length : state.registers .rsi = 0)
    (chain : DownChain layout state.words []) (counts : CountsAt layout (readyCounts 1) state.words)
    (stack : Stack layout) (pointer : state.registers .rsp = stack.top)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory)
    (available : stack.Available memory) (foldCounters : Bool) :
    ∃ after nextMemory, LoopResult layout [] (mainCounts 0) state after ∧
      Realizes layout (afterOutside layout stack [] outside) after.words nextMemory ∧
      Stream.SafeSteps Runtime.rejecting (checked foldCounters) 42 (fun _ => False) (leaf (state.core memory) 2 0)
        stack.holes (haltedLeaf (after.core nextMemory) 4 13) := by
  have dispatch := (Trace.nil (layout := layout) state).safeBranch_readOnly rfl (HeapAccess.empty layout)
    outside memory represented Runtime.rejecting (checked foldCounters) 2 26 27 (RuntimeTarget.wordCompare .rsi (.imm 0)) .eq
    (dispatchCode foldCounters) true
    (by simp [RuntimeTarget.wordCompare, Compare.holds, Condition.holds, State.core, Core.readReg, AluSource.eval, signExtend32, length])
    (hasBlock foldCounters 26 (by decide))
  let initialized := allocateState state layout 1 nilTag 0 (.imm 0) .rsi
  have initialization := RuntimeExecution.initializeInput_result layout [] state capacity context root chain counts
  obtain ⟨allocatedMemory, allocatedView, called⟩ := allocatorSteps layout state 1 (by omega) context counts.cursor
    stack pointer outside memory represented available (checked foldCounters) 26 0 (callSite foldCounters false) (calleeCode foldCounters)
  have jump := (emptyCode foldCounters).safe_jump (hasBlock foldCounters 3 (by decide)) Runtime.rejecting
    (initialized.core allocatedMemory) [] stack.holes
  have invariant : LoopInvariant layout [] [] (readyCounts 2) initialized :=
    ⟨initialization.input, initialization.accumulator, initialization.counts,
      initialization.inputRoot, initialization.accRoot, initialization.context⟩
  obtain ⟨after, nextMemory, result, view, loop⟩ := loopSafeStepsFor layout [] [] (readyCounts 2) initialized invariant
    capacity (by decide) stack.holes (stack.heapAccess [] (by simp))
    (by
      have same : initialized.registers .rsp = stack.top := (initialization.saved .rsp rfl).trans pointer
      rw [same]
      exact stack.returnClean)
    (afterOutside layout stack [] outside) allocatedMemory allocatedView Runtime.rejecting (checked foldCounters)
    (RuntimeTarget.loopInstructions foldCounters) (RuntimeTarget.loopCode foldCounters true) (RuntimeTarget.loopTrace foldCounters layout)
  refine ⟨after, nextMemory, ?_, view, ?_⟩
  · have saved := initialization.saved.trans result.saved
    simpa [mainCounts, Counts.finish, readyCounts, Counts.release] using ({ result with saved } : LoopResult layout [] (readyCounts 2).release state after)
  · exact dispatch.append (called.append (jump.append loop))

theorem nonemptySteps (layout : Layout) (head : Word) (tail : List Word) (state : State)
    (capacity : tail.length + 3 ≤ layout.capacity) (context : state.registers .rdi = layout.base)
    (root : state.registers .rdx = layout.cell (tail.length + 1)) (length : state.registers .rsi = UInt64.ofNat (tail.length + 1))
    (chain : DownChain layout state.words (head :: tail)) (counts : CountsAt layout (readyCounts (tail.length + 2)) state.words)
    (stack : Stack layout) (pointer : state.registers .rsp = stack.top)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory)
    (available : stack.Available memory) (foldCounters : Bool) :
    ∃ after nextMemory, LoopResult layout (head :: tail).reverse (mainCounts (tail.length + 1)) state after ∧
      Realizes layout (afterOutside layout stack (head :: tail) outside) after.words nextMemory ∧
      Stream.SafeSteps Runtime.rejecting (checked foldCounters)
        (((RuntimeTarget.loopInstructions foldCounters).length + 3) * tail.length + 72)
        (fun _ => False) (leaf (state.core memory) 2 0) stack.holes (haltedLeaf (after.core nextMemory) 4 13) := by
  have nonzero : UInt64.ofNat (tail.length + 1) ≠ 0 := by
    intro equal
    have same := congrArg UInt64.toNat equal
    have small : tail.length + 1 < UInt64.size := by
      have := layout.capacityBound
      change layout.capacity ≤ 66 at this
      change tail.length + 1 < 18446744073709551616
      omega
    rw [UInt64.toNat_ofNat_of_lt' small] at same
    change tail.length + 1 = 0 at same
    omega
  have dispatch := (Trace.nil (layout := layout) state).safeBranch_readOnly rfl (HeapAccess.empty layout)
    outside memory represented Runtime.rejecting (checked foldCounters) 2 26 27 (RuntimeTarget.wordCompare .rsi (.imm 0)) .eq
    (dispatchCode foldCounters) false
    (by simpa [RuntimeTarget.wordCompare, Compare.holds, Condition.holds, State.core, Core.readReg, AluSource.eval, signExtend32, length] using nonzero)
    (hasBlock foldCounters 27 (by decide))
  let index := tail.length + 1
  let reserved := reserveState state index
  have reservation := reserveTrace layout state index (by omega) context root
  obtain ⟨reservedMemory, reservedView, reserveSteps⟩ := reservation.safeSteps (HeapAccess.empty layout) outside memory represented
    Runtime.rejecting (checked foldCounters) 27 0 (reserveSegment foldCounters) (by decide)
  simp only [Nat.zero_add] at reserveSteps
  have reservePermissions := reserveSteps.steps.rejecting_permissions
  have reservedAvailable : stack.Available reservedMemory := available.of_permissions reservePermissions.1 reservePermissions.2
  have reservedContext : reserved.registers .rdi = layout.base := by simpa [reserved, reserveState] using context
  have reservedPointer : reserved.registers .rsp = stack.top := by simpa [reserved, reserveState] using pointer
  have reservedCursor : reserved.words Field.cursor.index = UInt64.ofNat (cellBytes * (index + 1)) := by
    rw [reserve_words]
    simpa [reservedWords, Field.index, Words.set, cellSlot, headerWords, cellWords, index,
      readyCounts, UInt64.add_assoc] using counts.cursor
  obtain ⟨allocatedMemory, allocatedView, called⟩ := allocatorSteps layout reserved (index + 1) (by omega) reservedContext reservedCursor
    stack reservedPointer outside reservedMemory reservedView reservedAvailable (checked foldCounters) 27 10
    (callSite foldCounters true) (calleeCode foldCounters)
  let allocated := allocateState reserved layout (index + 1) nilTag 0 (.imm 0) .rsi
  let next := firstState state layout index
  have finish := finishFirstTrace layout allocated index (by omega)
    (by simpa [allocated, allocateState] using reservedContext)
    (by simpa [allocated, allocateState, reserved, reserveState] using root)
  obtain ⟨finishedMemory, finishedView, finishSteps⟩ := finish.safeSteps (stack.heapAccess [] (by simp))
    (afterOutside layout stack (head :: tail) outside) allocatedMemory allocatedView Runtime.rejecting (checked foldCounters)
    27 13 (finishSegment foldCounters) (by decide)
  have jump := (firstCode foldCounters).safe_jump (hasBlock foldCounters 3 (by decide)) Runtime.rejecting
    (next.core finishedMemory) [] stack.holes
  have invariant := firstState_invariant layout head tail state capacity context root chain counts
  obtain ⟨after, nextMemory, result, view, loop⟩ := loopSafeStepsFor layout tail [head] (readyCounts (tail.length + 3)).consume next invariant
    (by simpa [Nat.add_assoc] using capacity) (by simp [readyCounts, Counts.consume]) stack.holes (stack.heapAccess [] (by simp))
    (by rw [firstState_saved state layout index .rsp rfl, pointer]; exact stack.returnClean)
    (afterOutside layout stack (head :: tail) outside) finishedMemory finishedView Runtime.rejecting (checked foldCounters)
    (RuntimeTarget.loopInstructions foldCounters) (RuntimeTarget.loopCode foldCounters true) (RuntimeTarget.loopTrace foldCounters layout)
  refine ⟨after, nextMemory, ?_, view, ?_⟩
  · have saved := (firstState_saved state layout index).trans result.saved
    have result' : LoopResult layout (tail.reverse ++ [head])
        ((readyCounts (tail.length + 3)).consume.finish tail.length) state after := { result with saved }
    simpa [List.reverse_cons, Counts.finish_consume, readyCounts_finish, Nat.add_assoc] using result'
  · have all := dispatch.append (reserveSteps.append (called.append (finishSteps.append (jump.append loop))))
    have cost : 1 + (reserveCons.length + (24 + (RuntimeTarget.finishFirstInstructions.length +
        (1 + (((RuntimeTarget.loopInstructions foldCounters).length + 3) * tail.length + 16))))) =
        ((RuntimeTarget.loopInstructions foldCounters).length + 3) * tail.length + 72 := by
      simp [RuntimeTarget.finishFirstInstructions, reserveCons, reuseCons, changeCounter]
      omega
    change Stream.SafeSteps _ _ (1 + (reserveCons.length + (24 + (RuntimeTarget.finishFirstInstructions.length +
        (1 + (((RuntimeTarget.loopInstructions foldCounters).length + 3) * tail.length + 16)))))) _ _ _ _ at all
    rw [cost] at all
    exact all

/-- The single emitted function handles every admitted runtime Word list.
Capacity includes the reserved caller cell and the callee's fresh cell;
stack sufficiency and all E2 call-safety premises are derived here. -/
theorem mainSteps (layout : Layout) (values : List Word) (state : State)
    (input : RuntimeExecution.Input layout values state) (capacity : values.length + 2 ≤ layout.capacity)
    (stack : Stack layout) (pointer : state.registers .rsp = stack.top)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory)
    (available : stack.Available memory) (foldCounters : Bool := false) :
    ∃ after nextMemory, LoopResult layout values.reverse (mainCounts values.length) state after ∧
      Realizes layout (afterOutside layout stack values outside) after.words nextMemory ∧
      Stream.SafeSteps Runtime.rejecting (checked foldCounters) (controlCost values.length foldCounters)
        (fun _ => False) (leaf (state.core memory) 0 0) stack.holes (haltedLeaf (after.core nextMemory) 4 13) := by
  obtain ⟨prepared, result, validation⟩ := RuntimeExecution.validationSteps (foldCounters := foldCounters) (callAllocator := true)
    layout values state input capacity outside memory represented Runtime.rejecting
  have preparedView : Realizes layout outside prepared.words memory := result.words.symm ▸ represented
  have preparedPointer : prepared.registers .rsp = stack.top := (result.saved .rsp rfl).trans pointer
  cases values with
  | nil =>
      obtain ⟨after, nextMemory, returned, view, rest⟩ := emptySteps layout prepared capacity result.context result.root result.length
        (result.words.symm ▸ input.chain) (result.words.symm ▸ input.counts)
        stack preparedPointer outside memory preparedView available foldCounters
      refine ⟨after, nextMemory, { returned with saved := result.saved.trans returned.saved }, view, ?_⟩
      have all := validation.append rest
      cases foldCounters <;> simpa [checked, controlCost, RuntimeTarget.controlCost, RuntimeTarget.validationCost] using all
  | cons head tail =>
      obtain ⟨after, nextMemory, returned, view, rest⟩ := nonemptySteps layout head tail prepared
        (by simpa [Nat.add_assoc] using capacity) result.context result.root result.length
        (result.words.symm ▸ input.chain) (result.words.symm ▸ input.counts)
        stack preparedPointer outside memory preparedView available foldCounters
      refine ⟨after, nextMemory, { returned with saved := result.saved.trans returned.saved }, view, ?_⟩
      have all := validation.append rest
      have cost : RuntimeTarget.validationCost (head :: tail).length +
          (((RuntimeTarget.loopInstructions foldCounters).length + 3) * tail.length + 72) =
          controlCost (head :: tail).length foldCounters := by
        cases foldCounters <;>
          simp [controlCost, RuntimeTarget.controlCost, RuntimeTarget.validationCost, RuntimeTarget.loopInstructions,
            UniqueCounterFold.instructions, consInstructions, reserveCons, reuseCons, changeCounter] <;> omega
      rw [cost] at all
      exact all

end Compilatrix.X86.Allocating
