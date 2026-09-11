import Ix.Compiler.X86.RuntimeExecution

/-! The caller's canonical input construction and its byte-memory relation.
This constructor is test/ABI support; it is absent from the emitted function. -/

namespace Ix.Compiler.X86.RuntimeExecution

open UniqueABI UniqueTarget UniqueExecution

/-- Inspect the requested slot before reading counters from the recursive
input. This avoids eager recomputation of every counter at every cell. -/
def inputWordsStep (words : Words) (index : Nat) (tag head tail : Word) (slot : Nat) : Word :=
  if slot == Field.peak.index then words Field.live.index + 1
  else if slot == Field.live.index then words Field.live.index + 1
  else if slot == Field.allocs.index then words Field.allocs.index + 1
  else if slot == cellSlot index 3 then 0
  else if slot == cellSlot index 2 then tail
  else if slot == cellSlot index 1 then head
  else if slot == cellSlot index 0 then tag
  else if slot == Field.cursor.index then words Field.cursor.index + 32
  else words slot

theorem inputWordsStep_eq (words : Words) (index : Nat) (tag head tail : Word) :
    inputWordsStep words index tag head tail = allocatedWords words index tag head tail := rfl

def inputWords (layout : Layout) : List Word → Words
  | [] => inputWordsStep (initialWords layout) 0 nilTag 0 0
  | head :: tail => inputWordsStep (inputWords layout tail) (tail.length + 1) consTag head (layout.cell tail.length)

theorem inputWords_valid (layout : Layout) (values : List Word) :
    DownChain layout (inputWords layout values) values ∧
      CountsAt layout (readyCounts (values.length + 1)) (inputWords layout values) := by
  induction values with
  | nil => exact ⟨allocatedWords_cell _ _ _ _ _, (CountsAt.initial layout).allocate 0 nilTag 0 0⟩
  | cons head tail ih =>
      refine ⟨⟨allocatedWords_cell _ _ _ _ _, ih.1.mono ?_⟩, ?_⟩
      · intro index bound field fieldBound
        exact allocatedWords_other (inputWords layout tail) (by omega) fieldBound _ _ _
      · simpa [inputWords, inputWordsStep_eq, List.length_cons, Nat.add_assoc] using ih.2.allocate (tail.length + 1) consTag head (layout.cell tail.length)

def inputMemory (layout : Layout) (values : List Word) (outside : Memory) : Memory :=
  fillWords layout (inputWords layout values)
    { outside with
      readable := fun address => layout.allowed address || outside.readable address
      writable := fun address => layout.allowed address || outside.writable address }
    layout.slots

theorem inputMemory_realizes (layout : Layout) (values : List Word) (outside : Memory) :
    Realizes layout outside (inputWords layout values) (inputMemory layout values outside) := by
  refine ⟨fun slot bound => fillWords_read _ _ _ (by omega) bound, ?_, ?_, ?_⟩
  · intro slot bound
    simp only [inputMemory, fillWords_readable]
    apply Memory.rangeAllowed_of_forall
    intro offset offsetBound
    simp [layout.byteAllowed bound offsetBound]
  · intro slot bound
    simp only [inputMemory, fillWords_writable]
    apply Memory.rangeAllowed_of_forall
    intro offset offsetBound
    simp [layout.byteAllowed bound offsetBound]
  · intro address notAllowed
    exact fillWords_frame _ _ _ (by omega) address notAllowed

def inputState (layout : Layout) (values : List Word) (registers : Registers) : State :=
  { registers := (registers.set .rdi layout.base).set .rsi (UInt64.ofNat values.length)
    words := inputWords layout values }

theorem inputState_valid (layout : Layout) (values : List Word) (registers : Registers) :
    Input layout values (inputState layout values registers) :=
  ⟨(inputWords_valid layout values).1, (inputWords_valid layout values).2, by simp [inputState], by simp [inputState]⟩

def canonicalLayout (values : List Word) (bound : values.length ≤ maxLength) : Layout :=
  { base := 0x1000
    capacity := values.length + 2
    capacityBound := Nat.add_le_add_right bound 2
    aligned := by decide
    nonzero := by decide
    fits := by
      change values.length ≤ 64 at bound
      change 4096 + 80 + 32 * (values.length + 2) ≤ 18446744073709551616
      omega }

def downNodes (layout : Layout) : Nat → List Word
  | 0 => [layout.cell 0]
  | length + 1 => layout.cell (length + 1) :: downNodes layout length

theorem downNodes_mem {layout : Layout} {length : Nat} {pointer : Word}
    (member : pointer ∈ downNodes layout length) : ∃ index, index ≤ length ∧ pointer = layout.cell index := by
  induction length with
  | zero => exact ⟨0, by omega, by simpa [downNodes] using member⟩
  | succ length ih =>
      simp only [downNodes, List.mem_cons] at member
      rcases member with same | member
      · exact ⟨length + 1, by omega, same⟩
      · obtain ⟨index, bound, same⟩ := ih member
        exact ⟨index, by omega, same⟩

theorem down_native {layout : Layout} {outside memory : Memory} {words : Words} {values : List Word}
    (chain : DownChain layout words values) (represented : Realizes layout outside words memory)
    (bound : values.length < layout.capacity) :
    NativeList memory (values.map UInt64.toNat) (layout.cell values.length) (downNodes layout values.length) := by
  induction values with
  | nil =>
      have atCell : 0 < layout.capacity := by simpa using bound
      refine .nil ?_ ?_ ?_ ?_
      · simpa using (represented.readCell atCell (by decide : 0 < cellWords)).trans chain.tagAt
      · exact (represented.readCell atCell (by decide : 1 < cellWords)).trans chain.headAt
      · exact (represented.readCell atCell (by decide : 2 < cellWords)).trans chain.tailAt
      · exact (represented.readCell atCell (by decide : 3 < cellWords)).trans chain.padding
  | cons head tail ih =>
      have atCell : tail.length + 1 < layout.capacity := by simpa using bound
      refine .cons ?_ ?_ ?_ ?_ (ih chain.2 (by omega)) ?_
      · simpa using (represented.readCell atCell (by decide : 0 < cellWords)).trans chain.1.tagAt
      · exact congrArg UInt64.toNat ((represented.readCell atCell (by decide : 1 < cellWords)).trans chain.1.headAt)
      · exact (represented.readCell atCell (by decide : 2 < cellWords)).trans chain.1.tailAt
      · exact (represented.readCell atCell (by decide : 3 < cellWords)).trans chain.1.padding
      · intro member
        obtain ⟨index, lower, equal⟩ := downNodes_mem member
        have := cell_injective layout atCell (by omega) equal
        omega

/-- Every bounded runtime list has an admitted caller state, and the same
emitted code executes and fully reclaims it. -/
theorem canonical_executes (values : List Word) (bound : values.length ≤ maxLength) (registers : Registers)
    (outside : Memory) (runtime : Runtime) :
    ∃ returned returnedMemory reclaimed reclaimedMemory,
      Execution (canonicalLayout values bound) values (inputState (canonicalLayout values bound) values registers)
        (inputMemory (canonicalLayout values bound) values outside) outside runtime
        returned returnedMemory reclaimed reclaimedMemory :=
  executes _ values _ (inputState_valid _ values registers) (Nat.le_refl _) outside _ (inputMemory_realizes _ values outside) runtime

end Ix.Compiler.X86.RuntimeExecution
