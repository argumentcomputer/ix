import Ix.Compiler.X86.UniqueHeap

/-! A bounded reserve/reuse rewrite. The adjacent reservation and live-cell
counter updates cancel before any observer or call. Retain every cell operation,
the cumulative reuse/payload counters, and the exact final register state. -/

namespace Ix.Compiler.X86.UniqueCounterFold

open UniqueABI UniqueTarget UniqueExecution

def policyTag : String := "unique-reserve-reuse-counter-fold/1"

def instructions : List Instr :=
  [.load .w64 .r8 (memoryOperand .rdx 8), .load .w64 .r9 (memoryOperand .rdx 16),
   .mov .w64 .rcx (.imm reservedTag), .store .w64 (memoryOperand .rdx 0) .rcx,
   .store .w64 (memoryOperand .rdx 8) .r8, .store .w64 (memoryOperand .rdx 16) .rsi,
   .mov .w64 .rcx (.imm consTag), .store .w64 (memoryOperand .rdx 0) .rcx] ++
  changeCounter .reuses .add 1 ++ changeCounter .payload .add 2 ++
  [.mov .w64 .rsi (.reg .rdx), .mov .w64 .rdx (.reg .r9)]

def foldedState (state : State) (index : Nat) : State :=
  let loaded := (state.setReg .r8 (state.words (cellSlot index 1))).setReg .r9
    (state.words (cellSlot index 2))
  let reserved := writeSourceState loaded (cellSlot index 0) (.imm reservedTag)
  let payload := (reserved.setWord (cellSlot index 1) (reserved.registers .r8)).setWord
    (cellSlot index 2) (reserved.registers .rsi)
  let reused := writeSourceState payload (cellSlot index 0) (.imm consTag)
  let counted := counterState (counterState reused .reuses .add 1) .payload .add 2
  (counted.setReg .rsi (counted.registers .rdx)).setReg .rdx (counted.registers .r9)

/-- Equality includes scratch registers and every arena word. No assumption
about the initial counter values is needed for the cancelling Word updates. -/
theorem state_eq (state : State) (index : Nat) : foldedState state index = consState state index := by
  apply State.ext
  · funext register
    cases register <;>
      simp (discharger := omega) [foldedState, consState, reserveState, reuseState,
        writeSourceState, counterState, State.setReg, State.setWord, State.move,
        MoveSource.eval, Registers.set, Words.set, Field.index, AluOp.eval,
        signExtend32, cellSlot, headerWords, cellWords, beq_iff_eq]
  · rw [consState_words]
    funext slot
    have cases : slot = 4 ∨ slot = 8 ∨ slot = cellSlot index 0 ∨ slot = cellSlot index 1 ∨
        slot = cellSlot index 2 ∨
        (slot ≠ 4 ∧ slot ≠ 8 ∧ slot ≠ cellSlot index 0 ∧ slot ≠ cellSlot index 1 ∧ slot ≠ cellSlot index 2) := by
      omega
    rcases cases with h | h | h | h | h | h <;>
      (try simp only [cellSlot, headerWords, cellWords, Nat.add_zero] at h) <;>
      simp (discharger := omega) [foldedState, consumedWords, writeSourceState, counterState,
        State.setReg, State.setWord, State.move, MoveSource.eval,
        Registers.set, Words.set, Field.index, AluOp.eval, signExtend32, cellSlot,
        headerWords, cellWords, beq_iff_eq, if_neg, *] <;> rfl

theorem trace (layout : Layout) (state : State) (index : Nat) (indexBound : index < layout.capacity)
    (context : state.registers .rdi = layout.base) (pointer : state.registers .rdx = layout.cell index) :
    Trace layout instructions state (consState state index) := by
  let first := state.setReg .r8 (state.words (cellSlot index 1))
  let loaded := first.setReg .r9 (state.words (cellSlot index 2))
  let reserved := writeSourceState loaded (cellSlot index 0) (.imm reservedTag)
  let head := reserved.setWord (cellSlot index 1) (reserved.registers .r8)
  let payload := head.setWord (cellSlot index 2) (reserved.registers .rsi)
  let reused := writeSourceState payload (cellSlot index 0) (.imm consTag)
  let counted := counterState reused .reuses .add 1
  let final := counterState counted .payload .add 2
  have loads : Trace layout [.load .w64 .r8 (memoryOperand .rdx 8), .load .w64 .r9 (memoryOperand .rdx 16)]
      state loaded := by
    refine .cons (loadField layout state .rdx .r8 index 1 indexBound (by decide) pointer)
      (.cons (loadField layout first .rdx .r9 index 2 indexBound (by decide) ?_) (.nil _))
    simpa [first] using pointer
  have reserve := writeSourceTrace layout loaded .rdx index 0 (.imm reservedTag) indexBound (by decide)
    (by simpa [loaded, first] using pointer) (by decide)
  have stores : Trace layout [.store .w64 (memoryOperand .rdx 8) .r8, .store .w64 (memoryOperand .rdx 16) .rsi]
      reserved payload := by
    refine .cons (storeField layout reserved .rdx .r8 index 1 indexBound (by decide) ?_)
      (.cons (storeField layout head .rdx .rsi index 2 indexBound (by decide) ?_) (.nil _)) <;>
      simpa [head, reserved, loaded, first] using pointer
  have reuse := writeSourceTrace layout payload .rdx index 0 (.imm consTag) indexBound (by decide)
    (by simpa [payload, head, reserved, loaded, first] using pointer) (by decide)
  have countReuse := counterTrace layout reused .reuses .add 1
    (by simpa [reused, payload, head, reserved, loaded, first] using context)
  have countPayload := counterTrace layout counted .payload .add 2
    (by simpa [counted, reused, payload, head, reserved, loaded, first] using context)
  have finish : Trace layout [.mov .w64 .rsi (.reg .rdx), .mov .w64 .rdx (.reg .r9)] final (foldedState state index) := by
    refine .cons (.mov _ _ _) (.cons (.mov _ _ _) ?_)
    exact .nil _
  have all := loads.append (reserve.append (stores.append (reuse.append (countReuse.append (countPayload.append finish)))))
  simpa [instructions, List.append_assoc, state_eq] using all

theorem instruction_saving : instructions.length + 12 = consInstructions.length := rfl

end Ix.Compiler.X86.UniqueCounterFold
