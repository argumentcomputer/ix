import Ix.Compiler.X86.UniqueMacros

/-! Physical cell and resource effects of the selected instruction traces.
The scalar heads and native tail pointers stay in the byte-memory word view. -/

namespace Ix.Compiler.X86.UniqueExecution

open UniqueABI UniqueTarget

def putCell (words : Words) (index : Nat) (tag head tail : Word) : Words :=
  (((words.set (cellSlot index 0) tag).set (cellSlot index 1) head).set (cellSlot index 2) tail).set
    (cellSlot index 3) 0

def allocatedWords (words : Words) (index : Nat) (tag head tail : Word) : Words :=
  let cells := putCell (words.set Field.cursor.index (words Field.cursor.index + 32)) index tag head tail
  ((cells.set Field.allocs.index (words Field.allocs.index + 1)).set Field.live.index
    (words Field.live.index + 1)).set Field.peak.index (words Field.live.index + 1)

def consumedWords (words : Words) (index : Nat) (accumulator : Word) : Words :=
  (((words.set (cellSlot index 0) consTag).set (cellSlot index 2) accumulator).set Field.reuses.index
    (words Field.reuses.index + 1)).set Field.payload.index (words Field.payload.index + 2)

def releasedWords (words : Words) (index : Nat) : Words :=
  ((putCell words index freedTag 0 0).set Field.frees.index (words Field.frees.index + 1)).set
    Field.live.index (words Field.live.index - 1)

private theorem slot_cases (slot index : Nat) :
    slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 4 ∨ slot = 5 ∨ slot = 6 ∨ slot = 7 ∨
    slot = 8 ∨ slot = 9 ∨ slot = cellSlot index 0 ∨ slot = cellSlot index 1 ∨
    slot = cellSlot index 2 ∨ slot = cellSlot index 3 ∨
    (slot ≠ 0 ∧ slot ≠ 1 ∧ slot ≠ 2 ∧ slot ≠ 3 ∧ slot ≠ 4 ∧ slot ≠ 5 ∧ slot ≠ 6 ∧ slot ≠ 7 ∧
     slot ≠ 8 ∧ slot ≠ 9 ∧ slot ≠ cellSlot index 0 ∧ slot ≠ cellSlot index 1 ∧
     slot ≠ cellSlot index 2 ∧ slot ≠ cellSlot index 3) := by omega

/-- The emitter uses an immediate tail for nil and the previous input root for
cons. The latter register survives the allocation's scratch work. -/
def allocationTailSafe : MoveSource → Bool
  | .imm _ => true
  | .reg register => register == .rdx

theorem allocateState_words (state : State) (layout : Layout) (index : Nat)
    (tag head : Word) (tail : MoveSource) (destination : GPR) (safe : allocationTailSafe tail = true) :
    (allocateState state layout index tag head tail destination).words =
      allocatedWords state.words index tag head (state.move tail) := by
  cases tail with
  | reg register =>
      simp only [allocationTailSafe, beq_iff_eq] at safe
      subst register
      funext slot
      rcases slot_cases slot index with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        (try simp only [cellSlot, headerWords, cellWords, Nat.add_zero] at h) <;>
        simp (discharger := omega) [allocateState, allocatedWords, putCell, prepareAllocation,
          writeSourceState, counterState, State.setWord, State.setReg, State.move, State.core,
          MoveSource.eval, Core.readReg, Registers.set, Words.set, Field.index,
          AluOp.eval, signExtend32, beq_iff_eq, if_neg, cellSlot, headerWords, cellWords, *] <;> rfl
  | imm value =>
      funext slot
      rcases slot_cases slot index with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        (try simp only [cellSlot, headerWords, cellWords, Nat.add_zero] at h) <;>
        simp (discharger := omega) [allocateState, allocatedWords, putCell, prepareAllocation,
          writeSourceState, counterState, State.setWord, State.setReg, State.move,
          MoveSource.eval, Registers.set, Words.set, Field.index,
          AluOp.eval, signExtend32, beq_iff_eq, if_neg, cellSlot, headerWords, cellWords, *] <;> rfl

theorem consState_words (state : State) (index : Nat) :
    (consState state index).words = consumedWords state.words index (state.registers .rsi) := by
  funext slot
  rcases slot_cases slot index with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (try simp only [cellSlot, headerWords, cellWords, Nat.add_zero] at h) <;>
    simp (discharger := omega) [consState, consumedWords, reserveState, reuseState,
      writeSourceState, counterState, State.setWord, State.setReg, State.move,
      MoveSource.eval, Registers.set, Words.set, Field.index,
      AluOp.eval, signExtend32, beq_iff_eq, if_neg, cellSlot, headerWords, cellWords,
      UInt64.add_sub_cancel, UInt64.sub_add_cancel, *] <;> rfl

theorem releaseState_words (state : State) (index : Nat) :
    (releaseState state index).words = releasedWords state.words index := by
  funext slot
  rcases slot_cases slot index with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (try simp only [cellSlot, headerWords, cellWords, Nat.add_zero] at h) <;>
    simp (discharger := omega) [releaseState, releasedWords, putCell,
      writeSourceState, counterState, State.setWord, State.setReg, State.move,
      MoveSource.eval, Words.set, Field.index,
      AluOp.eval, signExtend32, beq_iff_eq, if_neg, cellSlot, headerWords, cellWords, *] <;> rfl

structure CellAt (words : Words) (index : Nat) (tag head tail : Word) : Prop where
  tagAt : words (cellSlot index 0) = tag
  headAt : words (cellSlot index 1) = head
  tailAt : words (cellSlot index 2) = tail
  padding : words (cellSlot index 3) = 0

theorem CellAt.mono {before after : Words} {index : Nat} {tag head tail : Word}
    (cell : CellAt before index tag head tail)
    (same : ∀ field < 4, after (cellSlot index field) = before (cellSlot index field)) :
    CellAt after index tag head tail := by
  exact ⟨(same 0 (by decide)).trans cell.tagAt, (same 1 (by decide)).trans cell.headAt,
    (same 2 (by decide)).trans cell.tailAt, (same 3 (by decide)).trans cell.padding⟩

theorem CellAt.setHeader {words : Words} {index slot : Nat} {tag head tail : Word}
    (cell : CellAt words index tag head tail) (bound : slot < headerWords) (value : Word) :
    CellAt (words.set slot value) index tag head tail := by
  apply cell.mono
  intro field fieldBound
  apply Words.set_other
  simp only [cellSlot, headerWords, cellWords] at *
  omega

theorem putCell_at (words : Words) (index : Nat) (tag head tail : Word) :
    CellAt (putCell words index tag head tail) index tag head tail := by
  constructor <;> simp [putCell, Words.set, cellSlot]

theorem putCell_other (words : Words) {index other field : Nat} (different : other ≠ index)
    (fieldBound : field < 4) (tag head tail : Word) :
    putCell words index tag head tail (cellSlot other field) = words (cellSlot other field) := by
  simp (discharger := omega) [putCell, Words.set, cellSlot, headerWords, cellWords, if_neg]

theorem allocatedWords_cell (words : Words) (index : Nat) (tag head tail : Word) :
    CellAt (allocatedWords words index tag head tail) index tag head tail :=
  (((putCell_at _ _ _ _ _).setHeader (by decide : Field.allocs.index < headerWords) _).setHeader
    (by decide : Field.live.index < headerWords) _).setHeader (by decide : Field.peak.index < headerWords) _

theorem allocatedWords_other (words : Words) {index other field : Nat} (different : other ≠ index)
    (fieldBound : field < 4) (tag head tail : Word) :
    allocatedWords words index tag head tail (cellSlot other field) = words (cellSlot other field) := by
  simp (discharger := omega) [allocatedWords, putCell, Words.set, cellSlot, headerWords,
    cellWords, Field.index, if_neg]

theorem consumedWords_cell {words : Words} {index : Nat} {head tail : Word}
    (cell : CellAt words index consTag head tail) (accumulator : Word) :
    CellAt (consumedWords words index accumulator) index consTag head accumulator := by
  obtain ⟨tagAt, headAt, tailAt, padding⟩ := cell
  simp only [cellSlot, headerWords, cellWords] at headAt padding
  constructor <;> simp (discharger := omega) [consumedWords, Words.set, cellSlot, headerWords,
    cellWords, Field.index, if_neg, *]

theorem consumedWords_other (words : Words) {index other field : Nat} (different : other ≠ index)
    (fieldBound : field < 4) (accumulator : Word) :
    consumedWords words index accumulator (cellSlot other field) = words (cellSlot other field) := by
  simp (discharger := omega) [consumedWords, Words.set, cellSlot, headerWords, cellWords, Field.index, if_neg]

theorem releasedWords_cell (words : Words) (index : Nat) :
    CellAt (releasedWords words index) index freedTag 0 0 :=
  ((putCell_at _ _ _ _ _).setHeader (by decide : Field.frees.index < headerWords) _).setHeader
    (by decide : Field.live.index < headerWords) _

theorem releasedWords_other (words : Words) {index other field : Nat} (different : other ≠ index)
    (fieldBound : field < 4) :
    releasedWords words index (cellSlot other field) = words (cellSlot other field) := by
  simp (discharger := omega) [releasedWords, putCell, Words.set, cellSlot, headerWords, cellWords, Field.index, if_neg]

structure Counts where
  allocs : Nat := 0
  frees : Nat := 0
  reuses : Nat := 0
  live : Nat := 0
  peak : Nat := 0
  payload : Nat := 0
  deriving Repr, BEq, DecidableEq

def Counts.allocate (counts : Counts) : Counts :=
  { counts with allocs := counts.allocs + 1, live := counts.live + 1, peak := counts.live + 1 }
def Counts.consume (counts : Counts) : Counts :=
  { counts with reuses := counts.reuses + 1, payload := counts.payload + 2 }
def Counts.release (counts : Counts) : Counts :=
  { counts with frees := counts.frees + 1, live := counts.live - 1 }

structure CountsAt (layout : Layout) (counts : Counts) (words : Words) : Prop where
  cursor : words 0 = UInt64.ofNat (cellBytes * counts.allocs)
  capacity : words 1 = UInt64.ofNat (cellBytes * layout.capacity)
  allocs : words 2 = UInt64.ofNat counts.allocs
  frees : words 3 = UInt64.ofNat counts.frees
  reuses : words 4 = UInt64.ofNat counts.reuses
  live : words 5 = UInt64.ofNat counts.live
  peak : words 6 = UInt64.ofNat counts.peak
  rcops : words 7 = 0
  payload : words 8 = UInt64.ofNat counts.payload
  reservations : words 9 = 0

theorem CountsAt.initial (layout : Layout) : CountsAt layout {} (initialWords layout) := by
  constructor <;> rfl

theorem CountsAt.allocate {layout : Layout} {counts : Counts} {words : Words}
    (before : CountsAt layout counts words) (index : Nat) (tag head tail : Word) :
    CountsAt layout counts.allocate (allocatedWords words index tag head tail) := by
  obtain ⟨cursor, capacity, allocs, frees, reuses, live, peak, rcops, payload, reservations⟩ := before
  constructor <;>
    simp (discharger := omega) [allocatedWords, putCell, Words.set, cellSlot, headerWords, cellWords,
      Field.index, Counts.allocate, if_neg, cellBytes, UInt64.ofNat_add, Nat.mul_add, *] <;> rfl

theorem CountsAt.consume {layout : Layout} {counts : Counts} {words : Words}
    (before : CountsAt layout counts words) (index : Nat) (accumulator : Word) :
    CountsAt layout counts.consume (consumedWords words index accumulator) := by
  obtain ⟨cursor, capacity, allocs, frees, reuses, live, peak, rcops, payload, reservations⟩ := before
  constructor <;>
    simp (discharger := omega) [consumedWords, Words.set, cellSlot, headerWords, cellWords,
      Field.index, Counts.consume, if_neg, UInt64.ofNat_add, *] <;> rfl

theorem CountsAt.release {layout : Layout} {counts : Counts} {words : Words}
    (before : CountsAt layout counts words) (index : Nat) (positive : 0 < counts.live) :
    CountsAt layout counts.release (releasedWords words index) := by
  obtain ⟨cursor, capacity, allocs, frees, reuses, live, peak, rcops, payload, reservations⟩ := before
  constructor <;>
    simp (discharger := omega) [releasedWords, putCell, Words.set, cellSlot, headerWords, cellWords,
      Field.index, Counts.release, if_neg, UInt64.ofNat_add, UInt64.ofNat_sub, *] <;> rfl

@[simp] theorem consState_rdi (state : State) (index : Nat) :
    (consState state index).registers .rdi = state.registers .rdi := by
  simp [consState, reserveState, reuseState]
@[simp] theorem consState_rsi (state : State) (index : Nat) :
    (consState state index).registers .rsi = state.registers .rdx := by
  simp [consState, reserveState, reuseState]
@[simp] theorem consState_rdx (state : State) (index : Nat) :
    (consState state index).registers .rdx = state.words (cellSlot index 2) := by
  simp [consState, reserveState, reuseState]

@[simp] theorem releaseState_rdi (state : State) (index : Nat) :
    (releaseState state index).registers .rdi = state.registers .rdi := by
  simp [releaseState]
@[simp] theorem releaseState_rsi (state : State) (index : Nat) :
    (releaseState state index).registers .rsi = state.registers .rsi := by
  simp [releaseState]
@[simp] theorem releaseState_rdx (state : State) (index : Nat) :
    (releaseState state index).registers .rdx = state.registers .rdx := by
  simp [releaseState]

theorem allocateState_destination (state : State) (layout : Layout) (index : Nat)
    (tag head : Word) (tail : MoveSource) (destination : GPR) :
    (allocateState state layout index tag head tail destination).registers destination = layout.cell index := by
  simp [allocateState]

theorem allocateState_other (state : State) (layout : Layout) (index : Nat)
    (tag head : Word) (tail : MoveSource) (destination register : GPR)
    (other : register ≠ destination) (notRax : register ≠ .rax) (notRcx : register ≠ .rcx)
    (notR11 : register ≠ .r11) :
    (allocateState state layout index tag head tail destination).registers register = state.registers register := by
  simp [allocateState, other, notRax, notRcx, notR11]

end Ix.Compiler.X86.UniqueExecution
