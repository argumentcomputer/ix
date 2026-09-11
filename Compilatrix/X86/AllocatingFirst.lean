import Compilatrix.X86.RuntimeExecution

/-! Moving the nil allocation under the first reservation preserves the
reversal's heap and resource observations. Reuse raises the live count back
to its true peak; this write is necessary because allocation ran while one
cell was reserved. -/
namespace Compilatrix.X86.Allocating
open UniqueABI UniqueTarget UniqueExecution

def finishFirstState (state : State) (index : Nat) : State :=
  let reused := reuseState state index
  let counted := reused.setReg .r11 (reused.words Field.live.index)
  let peaked := counted.setWord Field.peak.index (reused.words Field.live.index)
  (peaked.setReg .rsi (peaked.registers .rdx)).setReg .rdx (peaked.registers .r9)

def firstState (state : State) (layout : Layout) (index : Nat) : State :=
  finishFirstState (allocateState (reserveState state index) layout (index + 1) nilTag 0 (.imm 0) .rsi) index

theorem finishFirstTrace (layout : Layout) (state : State) (index : Nat)
    (bound : index < layout.capacity) (context : state.registers .rdi = layout.base)
    (root : state.registers .rdx = layout.cell index) :
    Trace layout RuntimeTarget.finishFirstInstructions state (finishFirstState state index) := by
  let reused := reuseState state index
  let counted := reused.setReg .r11 (reused.words Field.live.index)
  let peaked := counted.setWord Field.peak.index (reused.words Field.live.index)
  have first := reuseTrace layout state index bound context root
  have last : Trace layout [Instr.load .w64 .r11 (header .live), .store .w64 (header .peak) .r11,
      .mov .w64 .rsi (.reg .rdx), .mov .w64 .rdx (.reg .r9)] reused (finishFirstState state index) := by
    refine .cons (.load _ _ _ Field.live.index (layout.field_bound .live)
      (header_address reused layout .live (by simpa [reused, reuseState] using context))) ?_
    refine .cons (.store _ _ _ Field.peak.index (layout.field_bound .peak)
      (header_address counted layout .peak (by simpa [counted, reused, reuseState] using context))) ?_
    refine .cons (.mov _ _ _) (.cons (.mov _ _ _) ?_)
    simpa [finishFirstState, reused, counted, peaked] using Trace.nil (layout := layout) (finishFirstState state index)
  exact first.append last

def reservedWords (words : Words) (index : Nat) : Words :=
  ((words.set (cellSlot index 0) reservedTag).set Field.reservations.index
    (words Field.reservations.index + 1)).set Field.live.index (words Field.live.index - 1)

def reusedWords (words : Words) (index : Nat) (head tail : Word) : Words :=
  let cell := ((words.set (cellSlot index 1) head).set (cellSlot index 2) tail).set (cellSlot index 0) consTag
  let reserved := cell.set Field.reservations.index (words Field.reservations.index - 1)
  let live := reserved.set Field.live.index (words Field.live.index + 1)
  (live.set Field.reuses.index (words Field.reuses.index + 1)).set Field.payload.index (words Field.payload.index + 2)

theorem reserve_words (state : State) (index : Nat) :
    (reserveState state index).words = reservedWords state.words index := by
  funext slot
  simp (discharger := omega) [reserveState, reservedWords, counterState, writeSourceState, State.setReg,
    State.setWord, State.move, MoveSource.eval, Words.set, Field.index, AluOp.eval, signExtend32,
    beq_iff_eq, if_neg, cellSlot, headerWords, cellWords] <;> rfl

theorem reuse_words (state : State) (index : Nat) :
    (reuseState state index).words = reusedWords state.words index (state.registers .r8) (state.registers .rsi) := by
  funext slot
  simp (discharger := omega) [reuseState, reusedWords, counterState, writeSourceState, State.setReg,
    State.setWord, State.move, MoveSource.eval, Words.set, Field.index, AluOp.eval, signExtend32,
    beq_iff_eq, if_neg, cellSlot, headerWords, cellWords] <;> rfl

theorem firstState_words_model (state : State) (layout : Layout) (index : Nat) :
    (firstState state layout index).words =
      let words := reusedWords (allocatedWords (reservedWords state.words index) (index + 1) nilTag 0 0)
        index (state.words (cellSlot index 1)) (layout.cell (index + 1))
      words.set Field.peak.index (words Field.live.index) := by
  have head := allocateState_other (reserveState state index) layout (index + 1) nilTag 0 (.imm 0) .rsi .r8
    (by decide) (by decide) (by decide) (by decide)
  simp only [firstState, finishFirstState, State.setReg_words, State.setWord_words, reuse_words,
    allocateState_words _ _ _ _ _ (.imm 0) _ rfl, reserve_words, allocateState_destination, head, State.move_imm]
  simp [reserveState]

theorem firstState_words (state : State) (layout : Layout) (index : Nat) :
    (firstState state layout index).words =
      consumedWords (allocatedWords state.words (index + 1) nilTag 0 0) index (layout.cell (index + 1)) := by
  rw [firstState_words_model]
  simp (discharger := omega) only [reservedWords, reusedWords, allocatedWords, consumedWords, putCell,
    Field.index, cellSlot, headerWords, cellWords, Words.set_same, Words.set_other,
    UInt64.add_sub_cancel, UInt64.sub_add_cancel, Nat.add_zero]
  funext slot
  have cases : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 4 ∨ slot = 5 ∨ slot = 6 ∨ slot = 7 ∨
      slot = 8 ∨ slot = 9 ∨ slot = cellSlot index 0 ∨ slot = cellSlot index 1 ∨
      slot = cellSlot index 2 ∨ slot = cellSlot index 3 ∨ slot = cellSlot (index + 1) 0 ∨
      slot = cellSlot (index + 1) 1 ∨ slot = cellSlot (index + 1) 2 ∨ slot = cellSlot (index + 1) 3 ∨
      (slot ≠ 0 ∧ slot ≠ 1 ∧ slot ≠ 2 ∧ slot ≠ 3 ∧ slot ≠ 4 ∧ slot ≠ 5 ∧ slot ≠ 6 ∧ slot ≠ 7 ∧
       slot ≠ 8 ∧ slot ≠ 9 ∧ slot ≠ cellSlot index 0 ∧ slot ≠ cellSlot index 1 ∧
       slot ≠ cellSlot index 2 ∧ slot ≠ cellSlot index 3 ∧ slot ≠ cellSlot (index + 1) 0 ∧
       slot ≠ cellSlot (index + 1) 1 ∧ slot ≠ cellSlot (index + 1) 2 ∧ slot ≠ cellSlot (index + 1) 3) := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (try simp only [cellSlot, headerWords, cellWords, Nat.add_zero] at h) <;>
    (try simp only [h]) <;>
    simp (discharger := omega) only [Words.set_same, Words.set_other]

theorem firstState_saved (state : State) (layout : Layout) (index : Nat) :
    PreservesSaved state (firstState state layout index) := by
  intro register saved
  cases register <;> simp_all [Saved, firstState, finishFirstState, reserveState, reuseState, allocateState]

theorem firstState_invariant (layout : Layout) (head : Word) (tail : List Word) (state : State)
    (capacity : tail.length + 3 ≤ layout.capacity) (context : state.registers .rdi = layout.base)
    (root : state.registers .rdx = layout.cell (tail.length + 1))
    (chain : DownChain layout state.words (head :: tail))
    (counts : CountsAt layout (readyCounts (tail.length + 2)) state.words) :
    LoopInvariant layout tail [head] (readyCounts (tail.length + 3)).consume
      (firstState state layout (tail.length + 1)) := by
  have initialized := RuntimeExecution.initializeInput_result layout (head :: tail) state
    (by simpa [Nat.add_assoc] using capacity) context root chain (by simpa [Nat.add_assoc] using counts)
  have words : (firstState state layout (tail.length + 1)).words =
      consumedWords (allocateState state layout (tail.length + 2) nilTag 0 (.imm 0) .rsi).words
        (tail.length + 1) (layout.cell (tail.length + 2)) := by
    rw [firstState_words, allocateState_words _ _ _ _ _ _ _ rfl]
    rfl
  have chains := chains_cons initialized.input initialized.accumulator
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [words]
    exact chains.1
  · rw [words]
    exact chains.2
  · rw [words]
    simpa [List.length_cons, Nat.add_assoc] using initialized.counts.consume (tail.length + 1) (layout.cell (tail.length + 2))
  · simpa [firstState, finishFirstState, reserveState, reuseState, allocateState] using chain.1.tailAt
  · simpa [firstState, finishFirstState, reserveState, reuseState, allocateState] using root
  · simpa [firstState, finishFirstState, reserveState, reuseState, allocateState] using context

end Compilatrix.X86.Allocating
