import Ix.Compiler.X86.RuntimeGuards

namespace Ix.Compiler.X86.RuntimeExecution

open UniqueABI UniqueTarget UniqueExecution RuntimeTarget

variable {foldCounters : Bool}

def headersState (state : State) : State :=
  let state := headerState state .allocs
  let state := headerState state .frees
  let state := headerState state .reuses
  let state := headerState state .live
  let state := headerState state .peak
  let state := headerState state .rcops
  let state := headerState state .payload
  headerState state .reservations

theorem headerSequence (layout : Layout) (count : Nat) (state : State)
    (counts : CountsAt layout (readyCounts count) state.words)
    (context : state.registers .rdi = layout.base) (expected : state.registers .r10 = UInt64.ofNat count)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    Steps runtime (RuntimeTarget.checked foldCounters) 16 (leaf (state.core memory) 12 0)
      (leaf ((headersState state).core memory) 20 0) := by
  let s1 := headerState state .allocs
  let s2 := headerState s1 .frees
  let s3 := headerState s2 .reuses
  let s4 := headerState s3 .live
  let s5 := headerState s4 .peak
  let s6 := headerState s5 .rcops
  let s7 := headerState s6 .payload
  have one := headerSteps (foldCounters := foldCounters) layout state .allocs context outside memory represented runtime 12 13 (.reg .r10)
    ⟨rfl, by decide⟩ (by simp [headerState, wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core,
      AluSource.eval, Field.index, counts.allocs, readyCounts, expected]) (by decide)
  have two := headerSteps (foldCounters := foldCounters) layout s1 .frees (by simpa [s1, headerState] using context) outside memory represented
    runtime 13 14 (.imm 0) ⟨rfl, by decide⟩ (by simp [s1, headerState, wordCompare, Compare.holds, Condition.holds,
      Core.readReg, State.core, AluSource.eval, Field.index, counts.frees, readyCounts, signExtend32]) (by decide)
  have three := headerSteps (foldCounters := foldCounters) layout s2 .reuses (by simpa [s2, s1, headerState] using context) outside memory represented
    runtime 14 15 (.imm 0) ⟨rfl, by decide⟩ (by simp [s2, s1, headerState, wordCompare, Compare.holds, Condition.holds,
      Core.readReg, State.core, AluSource.eval, Field.index, counts.reuses, readyCounts, signExtend32]) (by decide)
  have four := headerSteps (foldCounters := foldCounters) layout s3 .live (by simpa [s3, s2, s1, headerState] using context) outside memory represented
    runtime 15 16 (.reg .r10) ⟨rfl, by decide⟩ (by simp [s3, s2, s1, headerState, wordCompare, Compare.holds, Condition.holds,
      Core.readReg, State.core, AluSource.eval, Field.index, counts.live, readyCounts, expected]) (by decide)
  have five := headerSteps (foldCounters := foldCounters) layout s4 .peak (by simpa [s4, s3, s2, s1, headerState] using context) outside memory represented
    runtime 16 17 (.reg .r10) ⟨rfl, by decide⟩ (by simp [s4, s3, s2, s1, headerState, wordCompare, Compare.holds, Condition.holds,
      Core.readReg, State.core, AluSource.eval, Field.index, counts.peak, readyCounts, expected]) (by decide)
  have six := headerSteps (foldCounters := foldCounters) layout s5 .rcops (by simpa [s5, s4, s3, s2, s1, headerState] using context) outside memory represented
    runtime 17 18 (.imm 0) ⟨rfl, by decide⟩ (by simp [s5, s4, s3, s2, s1, headerState, wordCompare, Compare.holds, Condition.holds,
      Core.readReg, State.core, AluSource.eval, Field.index, counts.rcops, signExtend32]) (by decide)
  have seven := headerSteps (foldCounters := foldCounters) layout s6 .payload (by simpa [s6, s5, s4, s3, s2, s1, headerState] using context) outside memory represented
    runtime 18 19 (.imm 0) ⟨rfl, by decide⟩ (by simp [s6, s5, s4, s3, s2, s1, headerState, wordCompare, Compare.holds, Condition.holds,
      Core.readReg, State.core, AluSource.eval, Field.index, counts.payload, readyCounts, signExtend32]) (by decide)
  have eight := headerSteps (foldCounters := foldCounters) layout s7 .reservations (by simpa [s7, s6, s5, s4, s3, s2, s1, headerState] using context)
    outside memory represented runtime 19 20 (.imm 0) ⟨rfl, by decide⟩
    (by simp [s7, s6, s5, s4, s3, s2, s1, headerState, wordCompare, Compare.holds, Condition.holds, Core.readReg,
      State.core, AluSource.eval, Field.index, counts.reservations, signExtend32]) (by decide)
  exact one.append (two.append (three.append (four.append (five.append (six.append (seven.append eight))))))

def descriptorState (state : State) : State :=
  headersState (capacityAlignmentState (capacityState (cursorState (alignmentState state))))

theorem descriptorSteps (layout : Layout) (length : Nat) (state : State)
    (capacity : length + 2 ≤ layout.capacity)
    (counts : CountsAt layout (readyCounts (length + 1)) state.words)
    (context : state.registers .rdi = layout.base) (argument : state.registers .rsi = UInt64.ofNat length)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    Steps runtime (RuntimeTarget.checked foldCounters) 33 (leaf (state.core memory) 0 0)
      (leaf ((descriptorState state).core memory) 20 0) := by
  have lengthBound : length ≤ 64 := by have := layout.capacityBound; change layout.capacity ≤ 66 at this; omega
  have lengthSmall : length < UInt64.size := by change length < 18446744073709551616; omega
  have bytesSmall : cellBytes * layout.capacity < UInt64.size := by
    have := layout.capacityBound
    change layout.capacity ≤ 66 at this
    change 32 * layout.capacity < 18446744073709551616
    omega
  have requiredSmall : cellBytes * (length + 2) < UInt64.size := by
    change 32 * (length + 2) < 18446744073709551616
    omega
  have space : UInt64.ofNat (cellBytes * (length + 2)) ≤ UInt64.ofNat (cellBytes * layout.capacity) := by
    rw [UInt64.ofNat_le_iff_le requiredSmall bytesSmall]
    exact Nat.mul_le_mul_left _ capacity
  have capped : UInt64.ofNat (cellBytes * layout.capacity) ≤ 2112 := by
    change UInt64.ofNat (cellBytes * layout.capacity) ≤ UInt64.ofNat 2112
    rw [UInt64.ofNat_le_iff_le bytesSmall (by decide)]
    have := layout.capacityBound
    change layout.capacity ≤ 66 at this
    change 32 * layout.capacity ≤ 2112
    omega
  have multiple : UInt64.ofNat (cellBytes * layout.capacity) &&& 31 = 0 := by
    rw [and_thirtyOne]
    apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_mod, UInt64.toNat_ofNat_of_lt' bytesSmall, cellBytes]
  have required : UInt64.ofNat (cellBytes * (length + 1)) + 32 = UInt64.ofNat (cellBytes * (length + 2)) := by
    simp [cellBytes, Nat.mul_add, UInt64.ofNat_add, UInt64.add_assoc]
  have available : byteCount (UInt64.ofNat length) + 32 ≤ UInt64.ofNat (cellBytes * layout.capacity) := by
    rw [byteCount_nat, required]
    exact space
  let aligned := alignmentState state
  let cursor := cursorState aligned
  let sized := capacityState cursor
  let prepared := capacityAlignmentState sized
  have zero := guardSteps (foldCounters := foldCounters) (Trace.nil (layout := layout) state) rfl outside memory represented runtime 0 1
    .rsi (.imm 64) .unsignedLe ⟨rfl, by decide⟩
    (by simpa [wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core, AluSource.eval,
      signExtend32, argument, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' lengthSmall] using lengthBound) (by decide)
  have one := guardSteps (foldCounters := foldCounters) (alignmentTrace layout state) rfl outside memory represented runtime 1 7
    .rax (.imm 0) .eq ⟨rfl, by decide⟩
    (by simp [alignmentState, wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core,
      AluSource.eval, signExtend32, context, and_seven, layout.aligned]) (by decide)
  have seven := guardSteps (foldCounters := foldCounters) (Trace.nil (layout := layout) aligned) rfl outside memory represented runtime 7 8
    .rdi (.imm 0) .ne ⟨rfl, by decide⟩
    (by simp [aligned, alignmentState, wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core,
      AluSource.eval, signExtend32, context, layout.nonzero]) (by decide)
  have eight := guardSteps (foldCounters := foldCounters) (cursorTrace layout aligned (by simpa [aligned, alignmentState] using context)) rfl
    outside memory represented runtime 8 9 .r11 (.reg .rax) .eq ⟨rfl, by decide⟩
    (by simp [cursorState, aligned, alignmentState, wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core,
      AluSource.eval, argument, byteCount_nat, Field.index, counts.cursor, readyCounts]) (by decide)
  have nine := guardSteps (foldCounters := foldCounters) (capacityTrace layout cursor (by simpa [cursor, cursorState, aligned, alignmentState] using context))
    rfl outside memory represented runtime 9 10 .rcx (.reg .r11) .unsignedGe ⟨rfl, by decide⟩
    (by simpa [capacityState, cursor, cursorState, aligned, alignmentState, wordCompare, Compare.holds, Condition.holds,
      Core.readReg, State.core, AluSource.eval, argument, Field.index, counts.capacity] using available) (by decide)
  have ten := guardSteps (foldCounters := foldCounters) (Trace.nil (layout := layout) sized) rfl outside memory represented runtime 10 11
    .rcx (.imm 2112) .unsignedLe ⟨rfl, by decide⟩
    (by simpa [sized, capacityState, cursor, cursorState, aligned, alignmentState, wordCompare, Compare.holds, Condition.holds,
      Core.readReg, State.core, AluSource.eval, Field.index, counts.capacity, signExtend32] using capped) (by decide)
  have eleven := guardSteps (foldCounters := foldCounters) (capacityAlignmentTrace layout sized) rfl outside memory represented runtime 11 12
    .r11 (.imm 0) .eq ⟨rfl, by decide⟩
    (by simpa [capacityAlignmentState, sized, capacityState, cursor, cursorState, aligned, alignmentState, wordCompare,
      Compare.holds, Condition.holds, Core.readReg, State.core, AluSource.eval, Field.index, counts.capacity,
      signExtend32] using multiple) (by decide)
  have rest := headerSequence (foldCounters := foldCounters) layout (length + 1) prepared counts
    (by simpa [prepared, capacityAlignmentState, sized, capacityState, cursor, cursorState, aligned, alignmentState] using context)
    (by simp [prepared, capacityAlignmentState, sized, capacityState, cursor, cursorState, aligned, alignmentState,
      argument, UInt64.ofNat_add]) outside memory represented runtime
  exact zero.append (one.append (seven.append (eight.append (nine.append (ten.append (eleven.append rest))))))

theorem descriptorState_words (state : State) : (descriptorState state).words = state.words := rfl

theorem descriptorState_register (state : State) (register : GPR)
    (kept : register ∉ [.rax, .rcx, .r10, .r11]) :
    (descriptorState state).registers register = state.registers register := by
  cases register <;>
    simp_all [descriptorState, headersState, headerState, capacityAlignmentState, capacityState, cursorState, alignmentState]

theorem descriptorState_saved (state : State) : PreservesSaved state (descriptorState state) := by
  intro register saved
  apply descriptorState_register
  cases register <;> simp_all [Saved]

end Ix.Compiler.X86.RuntimeExecution
