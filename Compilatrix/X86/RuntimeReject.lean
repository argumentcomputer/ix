import Compilatrix.X86.RuntimeInput

/-! Explicit rejection results for the runtime ABI. The generic guard lemma
preserves the exact memory, and the length/capacity corollaries start at the
actual exported entry rather than assuming a program counter after checks. -/

namespace Compilatrix.X86.RuntimeExecution

open UniqueABI UniqueTarget UniqueExecution RuntimeTarget

variable {foldCounters callAllocator : Bool}

def rejectedState (state : State) : State := state.setReg .rax 0

theorem failureSteps (state : State) (memory : Memory) (runtime : Runtime) :
    Stream.SafeSteps runtime (RuntimeTarget.checked foldCounters callAllocator) 2 (fun _ => False) (leaf (state.core memory) 6 0)
      (fun _ => False) (haltedLeaf ((rejectedState state).core memory) 6 1) := by
  have sequence : Straight.Sequence [Instr.mov .w64 .rax (.imm 0)]
      (state.core memory) ((rejectedState state).core memory) :=
    .cons (Straight.Effect.mov (state.core memory) .rax (.imm 0)) (.nil _)
  have code : BlockCode (RuntimeTarget.checked foldCounters callAllocator) 6 [Instr.mov .w64 .rax (.imm 0)] .ret := ⟨by cases callAllocator <;> rfl, by decide⟩
  have found : (RuntimeTarget.checked foldCounters callAllocator).program.blocks[6]? =
      some { instructions := #[Instr.mov .w64 .rax (.imm 0)], terminator := .ret } := code.found
  have ordinary := sequence.steps runtime (RuntimeTarget.checked foldCounters callAllocator) 6 0 code.segment (by decide)
  have safe : Stream.SafeAt (RuntimeTarget.checked foldCounters callAllocator).program (fun _ => False)
      (leaf (state.core memory) 6 0) := by
    simp [Stream.SafeAt, leaf, found, Stream.OperationSafe, Stream.operationReads, Stream.operationWrites, Encode.instructionOperation]
  have one : step runtime (RuntimeTarget.checked foldCounters callAllocator) (leaf (state.core memory) 6 0) =
      leaf ((rejectedState state).core memory) 6 1 := by
    cases ordinary with
    | cons one rest => cases rest; exact one
  have first := Stream.SafeSteps.single safe one
  simp only [Stream.holeStep, leaf, show (6 : BlockId).toNat = 6 from rfl, found] at first
  exact first.append (code.safe_halt runtime _ (fun _ => False) (fun _ _ => id))

theorem guardRejectedSteps {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (readonly : instructions.all readsOnly = true)
    (outside memory : Memory) (represented : Realizes layout outside before.words memory)
    (runtime : Runtime) (block next : BlockId) (left : GPR) (right : AluSource) (condition : Condition)
    (code : BlockCode (RuntimeTarget.checked foldCounters callAllocator) block instructions (.branch (wordCompare left right) condition next 6))
    (fails : (wordCompare left right).holds condition (after.core Memory.unmapped) = false) :
    Stream.SafeSteps runtime (RuntimeTarget.checked foldCounters callAllocator) (instructions.length + 3)
      (fun _ => False) (leaf (before.core memory) block 0) (fun _ => False)
      (haltedLeaf ((rejectedState after).core memory) 6 1) := by
  have guard := trace.safeBranch_readOnly readonly (HeapAccess.empty layout) outside memory represented runtime (RuntimeTarget.checked foldCounters callAllocator) block next 6
    (wordCompare left right) condition code false fails (hasBlock 6 (by decide))
  have all := guard.append (failureSteps after memory runtime)
  simpa [Nat.add_assoc, leaf, inFrame] using all

theorem lengthRejects (state : State) (memory : Memory) (runtime : Runtime)
    (tooLong : ¬state.registers .rsi ≤ 64) :
    runFrom runtime (RuntimeTarget.checked foldCounters callAllocator) 3 (state.core memory) =
        haltedLeaf ((rejectedState state).core memory) 6 1 ∧
      PreservesSaved state (rejectedState state) := by
  have code : BlockCode (RuntimeTarget.checked foldCounters callAllocator) 0 [] (.branch (wordCompare .rsi (.imm 64)) .unsignedLe 1 6) := ⟨by cases callAllocator <;> rfl, by decide⟩
  have branch := code.branch runtime (state.core memory) false
    (by simp [wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core, AluSource.eval, signExtend32, tooLong])
    (hasBlock 6 (by decide))
  have steps := (Steps.single branch).append (failureSteps state memory runtime).steps
  exact ⟨steps.run_eq, PreservesSaved.setReg state .rax 0 rfl⟩

theorem cursorPrefix (layout : Layout) (length : Nat) (state : State) (bounded : length ≤ 64)
    (counts : CountsAt layout (readyCounts (length + 1)) state.words)
    (context : state.registers .rdi = layout.base) (argument : state.registers .rsi = UInt64.ofNat length)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    Stream.SafeSteps runtime (RuntimeTarget.checked foldCounters callAllocator) 10 (fun _ => False) (leaf (state.core memory) 0 0)
      (fun _ => False) (leaf ((cursorState (alignmentState state)).core memory) 9 0) := by
  have small : length < UInt64.size := by change length < 18446744073709551616; omega
  let aligned := alignmentState state
  have zero := guardSteps (foldCounters := foldCounters) (callAllocator := callAllocator) (Trace.nil (layout := layout) state) rfl outside memory represented runtime 0 1
    .rsi (.imm 64) .unsignedLe ⟨by cases callAllocator <;> rfl, by decide⟩
    (by simpa [wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core, AluSource.eval,
      signExtend32, argument, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' small] using bounded) (by decide)
  have one := guardSteps (foldCounters := foldCounters) (callAllocator := callAllocator) (alignmentTrace layout state) rfl outside memory represented runtime 1 7
    .rax (.imm 0) .eq ⟨by cases callAllocator <;> rfl, by decide⟩
    (by simp [alignmentState, wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core,
      AluSource.eval, signExtend32, context, and_seven, layout.aligned]) (by decide)
  have seven := guardSteps (foldCounters := foldCounters) (callAllocator := callAllocator) (Trace.nil (layout := layout) aligned) rfl outside memory represented runtime 7 8
    .rdi (.imm 0) .ne ⟨by cases callAllocator <;> rfl, by decide⟩
    (by simp [aligned, alignmentState, wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core,
      AluSource.eval, signExtend32, context, layout.nonzero]) (by decide)
  have eight := guardSteps (foldCounters := foldCounters) (callAllocator := callAllocator) (cursorTrace layout aligned (by simpa [aligned, alignmentState] using context)) rfl
    outside memory represented runtime 8 9 .r11 (.reg .rax) .eq ⟨by cases callAllocator <;> rfl, by decide⟩
    (by simp [cursorState, aligned, alignmentState, wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core,
      AluSource.eval, argument, byteCount_nat, Field.index, counts.cursor, readyCounts]) (by decide)
  exact zero.append (one.append (seven.append eight))

def capacityRejectedState (state : State) : State := rejectedState (capacityState (cursorState (alignmentState state)))

theorem capacityRejectedSteps (layout : Layout) (length : Nat) (state : State) (bounded : length ≤ 64)
    (insufficient : layout.capacity < length + 2)
    (counts : CountsAt layout (readyCounts (length + 1)) state.words)
    (context : state.registers .rdi = layout.base) (argument : state.registers .rsi = UInt64.ofNat length)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    Stream.SafeSteps runtime (RuntimeTarget.checked foldCounters callAllocator) 15 (fun _ => False)
      (leaf (state.core memory) 0 0) (fun _ => False) (haltedLeaf ((capacityRejectedState state).core memory) 6 1) ∧
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
  have validationPrefix := cursorPrefix (foldCounters := foldCounters) (callAllocator := callAllocator) layout length state bounded counts context argument outside memory represented runtime
  have failure := guardRejectedSteps (foldCounters := foldCounters) (callAllocator := callAllocator) (capacityTrace layout prepared (by simpa [prepared, cursorState, alignmentState] using context))
    rfl outside memory represented runtime 9 10 .rcx (.reg .r11) .unsignedGe ⟨by cases callAllocator <;> rfl, by decide⟩
    (by simpa [capacityState, prepared, cursorState, alignmentState, wordCompare, Compare.holds, Condition.holds,
      Core.readReg, State.core, AluSource.eval, argument, Field.index, counts.capacity] using unavailable)
  refine ⟨validationPrefix.append failure, ?_⟩
  intro register saved
  cases register <;> simp_all [Saved, capacityRejectedState, rejectedState, capacityState, cursorState, alignmentState]

theorem capacityRejects (layout : Layout) (length : Nat) (state : State) (bounded : length ≤ 64)
    (insufficient : layout.capacity < length + 2)
    (counts : CountsAt layout (readyCounts (length + 1)) state.words)
    (context : state.registers .rdi = layout.base) (argument : state.registers .rsi = UInt64.ofNat length)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    runFrom runtime (RuntimeTarget.checked foldCounters callAllocator) 15 (state.core memory) =
        haltedLeaf ((capacityRejectedState state).core memory) 6 1 ∧
      PreservesSaved state (capacityRejectedState state) := by
  have rejected := capacityRejectedSteps (foldCounters := foldCounters) (callAllocator := callAllocator)
    layout length state bounded insufficient counts context argument outside memory represented runtime
  exact ⟨rejected.1.steps.run_eq, rejected.2⟩

end Compilatrix.X86.RuntimeExecution
