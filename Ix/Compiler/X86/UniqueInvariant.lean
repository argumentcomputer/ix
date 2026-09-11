import Ix.Compiler.X86.UniqueHeap

/-! The two owned native chains occupy disjoint index intervals. The input
chain runs down to cell zero; the accumulator runs up to its allocated nil.
No external root or caller-supplied heap shape is assumed at source entry. -/

namespace Ix.Compiler.X86.UniqueExecution

open UniqueABI UniqueTarget

def DownChain (layout : Layout) (words : Words) : List Word → Prop
  | [] => CellAt words 0 nilTag 0 0
  | head :: tail => CellAt words (tail.length + 1) consTag head (layout.cell tail.length) ∧
      DownChain layout words tail

def UpChain (layout : Layout) (words : Words) (start : Nat) : List Word → Prop
  | [] => CellAt words start nilTag 0 0
  | head :: tail => CellAt words start consTag head (layout.cell (start + 1)) ∧
      UpChain layout words (start + 1) tail

theorem DownChain.mono {layout : Layout} {before after : Words} {values : List Word}
    (chain : DownChain layout before values)
    (same : ∀ index ≤ values.length, ∀ field < 4,
      after (cellSlot index field) = before (cellSlot index field)) : DownChain layout after values := by
  induction values with
  | nil => exact CellAt.mono chain (same 0 (by simp))
  | cons head tail ih =>
      exact ⟨chain.1.mono (same (tail.length + 1) (by simp)),
        ih chain.2 (fun index bound field fieldBound => same index (by simp; omega) field fieldBound)⟩

theorem UpChain.mono {layout : Layout} {before after : Words} {values : List Word} {start : Nat}
    (chain : UpChain layout before start values)
    (same : ∀ index, start ≤ index → index ≤ start + values.length → ∀ field < 4,
      after (cellSlot index field) = before (cellSlot index field)) : UpChain layout after start values := by
  induction values generalizing start with
  | nil => exact CellAt.mono chain (same start (by omega) (by simp))
  | cons head tail ih =>
      exact ⟨chain.1.mono (same start (by omega) (by simp)),
        ih chain.2 (fun index lower upper field fieldBound =>
          same index (by omega) (by simp only [List.length_cons]; omega) field fieldBound)⟩

/-- One destructive transfer preserves the two disjoint finite chains. -/
theorem chains_cons {layout : Layout} {words : Words} {head : Word} {tail acc : List Word}
    (input : DownChain layout words (head :: tail))
    (accumulator : UpChain layout words (tail.length + 2) acc) :
    let after := consumedWords words (tail.length + 1) (layout.cell (tail.length + 2))
    DownChain layout after tail ∧ UpChain layout after (tail.length + 1) (head :: acc) := by
  refine ⟨input.2.mono ?_, consumedWords_cell input.1 _, ?_⟩
  · intro index bound field fieldBound
    exact consumedWords_other words (by omega) fieldBound _
  · apply accumulator.mono
    intro index lower upper field fieldBound
    exact consumedWords_other words (by omega) fieldBound _

def Saved : GPR → Bool
  | .rbx | .rbp | .rsp | .r12 | .r13 | .r14 | .r15 => true
  | _ => false

def PreservesSaved (before after : State) : Prop :=
  ∀ register, Saved register = true → after.registers register = before.registers register

theorem PreservesSaved.refl (state : State) : PreservesSaved state state := fun _ _ => rfl

theorem PreservesSaved.trans {before middle after : State}
    (first : PreservesSaved before middle) (second : PreservesSaved middle after) : PreservesSaved before after :=
  fun register saved => (second register saved).trans (first register saved)

theorem PreservesSaved.setReg (state : State) (register : GPR) (value : Word) (allowed : Saved register = false) :
    PreservesSaved state (state.setReg register value) := by
  intro candidate saved
  have different : candidate ≠ register := by
    intro same
    rw [same, allowed] at saved
    contradiction
  simp [different]

theorem PreservesSaved.core {before after : State} (preserved : PreservesSaved before after)
    (beforeMemory afterMemory : Memory) :
    (after.core afterMemory).readReg .rsp = (before.core beforeMemory).readReg .rsp ∧
    (after.core afterMemory).calleeSavedSnapshot = (before.core beforeMemory).calleeSavedSnapshot := by
  constructor
  · exact preserved .rsp rfl
  · simp [Core.calleeSavedSnapshot, SysV.calleeSaved, Core.readReg, State.core,
      preserved .rbx rfl, preserved .rbp rfl, preserved .r12 rfl, preserved .r13 rfl,
      preserved .r14 rfl, preserved .r15 rfl]

theorem allocateState_saved (state : State) (layout : Layout) (index : Nat)
    (tag head : Word) (tail : MoveSource) (destination : GPR) (allowed : Saved destination = false) :
    PreservesSaved state (allocateState state layout index tag head tail destination) := by
  intro register saved
  apply allocateState_other
  · intro same; rw [same, allowed] at saved; contradiction
  · intro same; subst register; contradiction
  · intro same; subst register; contradiction
  · intro same; subst register; contradiction

theorem consState_saved (state : State) (index : Nat) : PreservesSaved state (consState state index) := by
  intro register saved
  cases register <;> simp [Saved] at saved <;> simp [consState, reuseState, reserveState]

theorem releaseState_saved (state : State) (index : Nat) : PreservesSaved state (releaseState state index) := by
  intro register saved
  cases register <;> simp [Saved] at saved <;> simp [releaseState]

def readyCounts (count : Nat) : Counts := { allocs := count, live := count, peak := count }

@[simp] theorem readyCounts_allocate (count : Nat) : (readyCounts count).allocate = readyCounts (count + 1) := rfl

def inputPrefix (values : List Word) : List Instr :=
  allocate nilTag 0 (.imm 0) .rdx ++ inputCons values.reverse

theorem inputCons_append (left right : List Word) : inputCons (left ++ right) = inputCons left ++ inputCons right := by
  induction left with
  | nil => rfl
  | cons head tail ih => simp [inputCons, ih, List.append_assoc]

theorem inputPrefix_cons (head : Word) (tail : List Word) :
    inputPrefix (head :: tail) = inputPrefix tail ++ allocate consTag head (.reg .rdx) .rdx := by
  simp [inputPrefix, List.reverse_cons, inputCons_append, inputCons, List.append_assoc]

structure InputResult (layout : Layout) (values : List Word) (before after : State) : Prop where
  chain : DownChain layout after.words values
  counts : CountsAt layout (readyCounts (values.length + 1)) after.words
  root : after.registers .rdx = layout.cell values.length
  context : after.registers .rdi = layout.base
  saved : PreservesSaved before after

theorem inputTrace (layout : Layout) (values : List Word) (state : State)
    (capacity : values.length + 1 ≤ layout.capacity) (context : state.registers .rdi = layout.base)
    (initial : state.words = initialWords layout) :
    ∃ after, Trace layout (inputPrefix values) state after ∧ InputResult layout values state after := by
  induction values with
  | nil =>
      let after := allocateState state layout 0 nilTag 0 (.imm 0) .rdx
      have first := allocateTrace layout state 0 nilTag 0 (.imm 0) .rdx (by simp at capacity; omega) context
        (by simp [initial, initialWords, Field.index, Words.set])
      have words : after.words = allocatedWords state.words 0 nilTag 0 0 := by
        simpa [after] using allocateState_words state layout 0 nilTag 0 (.imm 0) .rdx rfl
      have counts : CountsAt layout {} state.words := initial ▸ CountsAt.initial layout
      refine ⟨after, by simpa [inputPrefix, inputCons, after] using first, ?_⟩
      refine ⟨?_, ?_, allocateState_destination state layout 0 nilTag 0 (.imm 0) .rdx, ?_,
        allocateState_saved state layout 0 nilTag 0 (.imm 0) .rdx rfl⟩
      · change CellAt after.words 0 nilTag 0 0
        rw [words]
        exact allocatedWords_cell _ _ _ _ _
      · rw [words]
        exact counts.allocate 0 nilTag 0 0
      · exact (allocateState_other state layout 0 nilTag 0 (.imm 0) .rdx .rdi
          (by decide) (by decide) (by decide) (by decide)).trans context
  | cons head tail ih =>
      obtain ⟨middle, first, result⟩ := ih (by simp only [List.length_cons] at capacity; omega)
      let after := allocateState middle layout (tail.length + 1) consTag head (.reg .rdx) .rdx
      have cursor : middle.words Field.cursor.index = UInt64.ofNat (cellBytes * (tail.length + 1)) :=
        result.counts.cursor
      have last := allocateTrace layout middle (tail.length + 1) consTag head (.reg .rdx) .rdx
        (by simp only [List.length_cons] at capacity; omega) result.context cursor
      have words : after.words = allocatedWords middle.words (tail.length + 1) consTag head (layout.cell tail.length) := by
        simpa [after, result.root] using allocateState_words middle layout (tail.length + 1) consTag head (.reg .rdx) .rdx rfl
      refine ⟨after, by rw [inputPrefix_cons]; exact first.append last, ?_⟩
      refine ⟨?_, ?_, allocateState_destination middle layout (tail.length + 1) consTag head (.reg .rdx) .rdx, ?_,
        result.saved.trans (allocateState_saved middle layout (tail.length + 1) consTag head (.reg .rdx) .rdx rfl)⟩
      · rw [words]
        refine ⟨allocatedWords_cell _ _ _ _ _, result.chain.mono ?_⟩
        intro index bound field fieldBound
        exact allocatedWords_other middle.words (by omega) fieldBound _ _ _
      · rw [words]
        simpa using result.counts.allocate (tail.length + 1) consTag head (layout.cell tail.length)
      · exact (allocateState_other middle layout (tail.length + 1) consTag head (.reg .rdx) .rdx .rdi
          (by decide) (by decide) (by decide) (by decide)).trans result.context

structure Initialized (layout : Layout) (values : List Word) (before after : State) : Prop where
  input : DownChain layout after.words values
  accumulator : UpChain layout after.words (values.length + 1) []
  counts : CountsAt layout (readyCounts (values.length + 2)) after.words
  inputRoot : after.registers .rdx = layout.cell values.length
  accRoot : after.registers .rsi = layout.cell (values.length + 1)
  context : after.registers .rdi = layout.base
  saved : PreservesSaved before after

theorem initializeTrace (layout : Layout) (values : List Word) (state : State)
    (capacity : values.length + 2 ≤ layout.capacity) (context : state.registers .rdi = layout.base)
    (initial : state.words = initialWords layout) :
    ∃ after, Trace layout (inputInstructions values) state after ∧ Initialized layout values state after := by
  obtain ⟨middle, first, result⟩ := inputTrace layout values state (by omega) context initial
  let after := allocateState middle layout (values.length + 1) nilTag 0 (.imm 0) .rsi
  have last := allocateTrace layout middle (values.length + 1) nilTag 0 (.imm 0) .rsi
    (by omega) result.context result.counts.cursor
  have words : after.words = allocatedWords middle.words (values.length + 1) nilTag 0 0 := by
    simpa [after] using allocateState_words middle layout (values.length + 1) nilTag 0 (.imm 0) .rsi rfl
  refine ⟨after, first.append last, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, allocateState_destination middle layout (values.length + 1) nilTag 0 (.imm 0) .rsi, ?_,
    result.saved.trans (allocateState_saved middle layout (values.length + 1) nilTag 0 (.imm 0) .rsi rfl)⟩
  · rw [words]
    apply result.chain.mono
    intro index bound field fieldBound
    exact allocatedWords_other middle.words (by omega) fieldBound _ _ _
  · change CellAt after.words (values.length + 1) nilTag 0 0
    rw [words]
    exact allocatedWords_cell _ _ _ _ _
  · rw [words]
    simpa [Nat.add_assoc] using result.counts.allocate (values.length + 1) nilTag 0 0
  · exact (allocateState_other middle layout (values.length + 1) nilTag 0 (.imm 0) .rsi .rdx
      (by decide) (by decide) (by decide) (by decide)).trans result.root
  · exact (allocateState_other middle layout (values.length + 1) nilTag 0 (.imm 0) .rsi .rdi
      (by decide) (by decide) (by decide) (by decide)).trans result.context

end Ix.Compiler.X86.UniqueExecution
