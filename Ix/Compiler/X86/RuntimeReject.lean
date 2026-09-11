import Ix.Compiler.X86.RuntimeInput

/-! Explicit rejection results for the runtime ABI. The generic guard lemma
preserves the exact memory, and the length/capacity corollaries start at the
actual exported entry rather than assuming a program counter after checks. -/

namespace Ix.Compiler.X86.RuntimeExecution

open UniqueABI UniqueTarget UniqueExecution RuntimeTarget

variable {foldCounters : Bool}

def rejectedState (state : State) : State := state.setReg .rax 0

theorem failureSteps (state : State) (memory : Memory) (runtime : Runtime) :
    Steps runtime (RuntimeTarget.checked foldCounters) 2 (leaf (state.core memory) 6 0)
      (haltedLeaf ((rejectedState state).core memory) 6 1) := by
  have sequence : Straight.Sequence [Instr.mov .w64 .rax (.imm 0)]
      (state.core memory) ((rejectedState state).core memory) :=
    .cons (Straight.Effect.mov (state.core memory) .rax (.imm 0)) (.nil _)
  have code : BlockCode (RuntimeTarget.checked foldCounters) 6 [Instr.mov .w64 .rax (.imm 0)] .ret := ⟨rfl, by decide⟩
  have first := sequence.steps runtime (RuntimeTarget.checked foldCounters) 6 0 code.segment (by decide)
  exact first.append (Steps.single (code.ret runtime _))

theorem guardRejectedSteps {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (readonly : instructions.all readsOnly = true)
    (outside memory : Memory) (represented : Realizes layout outside before.words memory)
    (runtime : Runtime) (block next : BlockId) (left : GPR) (right : AluSource) (condition : Condition)
    (code : BlockCode (RuntimeTarget.checked foldCounters) block instructions (.branch (wordCompare left right) condition next 6))
    (fails : (wordCompare left right).holds condition (after.core Memory.unmapped) = false) :
    Steps runtime (RuntimeTarget.checked foldCounters) (instructions.length + 3) (leaf (before.core memory) block 0)
      (haltedLeaf ((rejectedState after).core memory) 6 1) := by
  have guard := trace.branch_readOnly readonly outside memory represented runtime (RuntimeTarget.checked foldCounters) block next 6
    (wordCompare left right) condition code false fails (hasBlock 6 (by decide))
  have all := guard.append (failureSteps after memory runtime)
  simpa [Nat.add_assoc] using all

theorem lengthRejects (state : State) (memory : Memory) (runtime : Runtime)
    (tooLong : ¬state.registers .rsi ≤ 64) :
    runFrom runtime (RuntimeTarget.checked foldCounters) 3 (state.core memory) =
        haltedLeaf ((rejectedState state).core memory) 6 1 ∧
      PreservesSaved state (rejectedState state) := by
  have code : BlockCode (RuntimeTarget.checked foldCounters) 0 [] (.branch (wordCompare .rsi (.imm 64)) .unsignedLe 1 6) := ⟨rfl, by decide⟩
  have branch := code.branch runtime (state.core memory) false
    (by simp [wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core, AluSource.eval, signExtend32, tooLong])
    (hasBlock 6 (by decide))
  have steps := (Steps.single branch).append (failureSteps state memory runtime)
  exact ⟨steps.run_eq, PreservesSaved.setReg state .rax 0 rfl⟩

theorem cursorPrefix (layout : Layout) (length : Nat) (state : State) (bounded : length ≤ 64)
    (counts : CountsAt layout (readyCounts (length + 1)) state.words)
    (context : state.registers .rdi = layout.base) (argument : state.registers .rsi = UInt64.ofNat length)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    Steps runtime (RuntimeTarget.checked foldCounters) 10 (leaf (state.core memory) 0 0)
      (leaf ((cursorState (alignmentState state)).core memory) 9 0) := by
  have small : length < UInt64.size := by change length < 18446744073709551616; omega
  let aligned := alignmentState state
  have zero := guardSteps (foldCounters := foldCounters) (Trace.nil (layout := layout) state) rfl outside memory represented runtime 0 1
    .rsi (.imm 64) .unsignedLe ⟨rfl, by decide⟩
    (by simpa [wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core, AluSource.eval,
      signExtend32, argument, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' small] using bounded) (by decide)
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
  exact zero.append (one.append (seven.append eight))

def capacityRejectedState (state : State) : State := rejectedState (capacityState (cursorState (alignmentState state)))

theorem capacityRejects (layout : Layout) (length : Nat) (state : State) (bounded : length ≤ 64)
    (insufficient : layout.capacity < length + 2)
    (counts : CountsAt layout (readyCounts (length + 1)) state.words)
    (context : state.registers .rdi = layout.base) (argument : state.registers .rsi = UInt64.ofNat length)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    runFrom runtime (RuntimeTarget.checked foldCounters) 15 (state.core memory) =
        haltedLeaf ((capacityRejectedState state).core memory) 6 1 ∧
      PreservesSaved state (capacityRejectedState state) := by
  have capBound := layout.capacityBound
  change layout.capacity ≤ 66 at capBound
  have requiredSmall : cellBytes * (length + 2) < UInt64.size := by
    change 32 * (length + 2) < 18446744073709551616
    omega
  have bytesSmall : cellBytes * layout.capacity < UInt64.size := by
    change 32 * layout.capacity < 18446744073709551616
    omega
  have short : ¬UInt64.ofNat (cellBytes * (length + 2)) ≤ UInt64.ofNat (cellBytes * layout.capacity) := by
    rw [UInt64.ofNat_le_iff_le requiredSmall bytesSmall]
    change ¬32 * (length + 2) ≤ 32 * layout.capacity
    omega
  have required : UInt64.ofNat (cellBytes * (length + 1)) + 32 = UInt64.ofNat (cellBytes * (length + 2)) := by
    simp [cellBytes, Nat.mul_add, UInt64.ofNat_add, UInt64.add_assoc]
  have unavailable : ¬byteCount (UInt64.ofNat length) + 32 ≤ UInt64.ofNat (cellBytes * layout.capacity) := by
    rw [byteCount_nat, required]
    exact short
  let prepared := cursorState (alignmentState state)
  have validationPrefix := cursorPrefix (foldCounters := foldCounters) layout length state bounded counts context argument outside memory represented runtime
  have failure := guardRejectedSteps (foldCounters := foldCounters) (capacityTrace layout prepared (by simpa [prepared, cursorState, alignmentState] using context))
    rfl outside memory represented runtime 9 10 .rcx (.reg .r11) .unsignedGe ⟨rfl, by decide⟩
    (by simpa [capacityState, prepared, cursorState, alignmentState, wordCompare, Compare.holds, Condition.holds,
      Core.readReg, State.core, AluSource.eval, argument, Field.index, counts.capacity] using unavailable)
  refine ⟨(validationPrefix.append failure).run_eq, ?_⟩
  intro register saved
  cases register <;> simp_all [Saved, capacityRejectedState, rejectedState, capacityState, cursorState, alignmentState]

end Ix.Compiler.X86.RuntimeExecution
