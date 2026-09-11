import Ix.Compiler.X86.RuntimeHeader

namespace Ix.Compiler.X86.RuntimeExecution

open UniqueABI UniqueTarget UniqueExecution RuntimeTarget

variable {foldCounters : Bool}

theorem cell_successor (layout : Layout) (index : Nat) :
    layout.cell index + 32 = layout.cell (index + 1) := by
  simp [Layout.cell, Layout.address, cellSlot, headerWords, cellWords, Nat.mul_add,
    UInt64.ofNat_add, UInt64.add_assoc]

theorem down_nil {layout : Layout} {words : Words} {values : List Word} (chain : DownChain layout words values) :
    CellAt words 0 nilTag 0 0 := by
  induction values with
  | nil => exact chain
  | cons _ _ ih => exact ih chain.2

structure LinkAt (layout : Layout) (words : Words) (index : Nat) : Prop where
  tag : words (cellSlot index 0) = consTag
  tail : words (cellSlot index 2) = layout.cell (index - 1)
  padding : words (cellSlot index 3) = 0

theorem down_link {layout : Layout} {words : Words} {values : List Word}
    (chain : DownChain layout words values) (index : Nat) (positive : 0 < index) (bound : index ≤ values.length) :
    LinkAt layout words index := by
  induction values with
  | nil => simp at bound; omega
  | cons head tail ih =>
      by_cases last : index = tail.length + 1
      · subst index
        exact ⟨chain.1.tagAt, by simpa using chain.1.tailAt, chain.1.padding⟩
      · exact ih chain.2 (by simp only [List.length_cons] at bound; omega)

def nilSetupState (layout : Layout) (state : State) : State :=
  ((state.setReg .rdx (layout.cell 0)).setReg .r8 (layout.cell 1)).setReg .r9 (state.registers .rsi)

def nilFieldsState (state : State) : State :=
  let state := state.setReg .rcx 0
  let state := state.setReg .r11 0
  let state := state.setReg .rcx 0
  let state := state.setReg .r11 0
  let state := state.setReg .rcx 0
  let state := state.setReg .r11 0
  state.setReg .rcx 0

def nilState (layout : Layout) (state : State) : State := nilFieldsState (nilSetupState layout state)

theorem nilTrace (layout : Layout) (state : State) (context : state.registers .rdi = layout.base)
    (bound : 1 < layout.capacity) (atNil : CellAt state.words 0 nilTag 0 0) :
    Trace layout nilInstructions state (nilState layout state) := by
  have setup : Trace layout
      [Instr.lea .rdx (memoryOperand .rdi headerBytes), .lea .r8 (memoryOperand .rdx cellBytes),
        .mov .w64 .r9 (.reg .rsi)] state (nilSetupState layout state) := by
    refine .cons (.lea _ _ _) (.cons (.lea _ _ _) (.cons (.mov _ _ _) ?_))
    have root : state.address (memoryOperand .rdi headerBytes) = layout.cell 0 := by
      rw [operand_address _ _ _ (by decide), context]
      simpa [headerBytes] using layout.allocate_address 0
    simpa [nilSetupState, root, cellBytes, operand_address _ .rdx 32 (by decide), cell_successor] using
      Trace.nil (layout := layout) (nilSetupState layout state)
  let start := nilSetupState layout state
  have fields : Trace layout
      [Instr.load .w64 .rcx (memoryOperand .rdx 0), .load .w64 .r11 (memoryOperand .rdx 8),
        .alu .or .w64 .rcx (.reg .r11), .load .w64 .r11 (memoryOperand .rdx 16),
        .alu .or .w64 .rcx (.reg .r11), .load .w64 .r11 (memoryOperand .rdx 24),
        .alu .or .w64 .rcx (.reg .r11)] start (nilFieldsState start) := by
    refine .cons (loadField layout start .rdx .rcx 0 0 (by omega) (by decide) (by simp [start, nilSetupState])) ?_
    refine .cons (loadField layout _ .rdx .r11 0 1 (by omega) (by decide) (by simp [start, nilSetupState])) ?_
    refine .cons (.alu _ _ _ _) ?_
    refine .cons (loadField layout _ .rdx .r11 0 2 (by omega) (by decide) (by simp [start, nilSetupState])) ?_
    refine .cons (.alu _ _ _ _) ?_
    refine .cons (loadField layout _ .rdx .r11 0 3 (by omega) (by decide) (by simp [start, nilSetupState])) ?_
    refine .cons (.alu _ _ _ _) ?_
    simpa [nilFieldsState, start, nilSetupState, AluOp.eval, atNil.tagAt, atNil.headAt, atNil.tailAt, atNil.padding,
      nilTag] using Trace.nil (layout := layout) (nilFieldsState start)
  exact setup.append fields

theorem nilSteps (layout : Layout) (state : State) (context : state.registers .rdi = layout.base)
    (bound : 1 < layout.capacity) (atNil : CellAt state.words 0 nilTag 0 0)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    Steps runtime (RuntimeTarget.checked foldCounters) 11 (leaf (state.core memory) 20 0)
      (leaf ((nilState layout state).core memory) 21 0) :=
  guardSteps (foldCounters := foldCounters) (nilTrace layout state context bound atNil) rfl outside memory represented runtime 20 21
    .rcx (.imm 0) .eq ⟨rfl, by decide⟩
    (by simp [nilState, nilFieldsState, wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core,
      AluSource.eval, signExtend32]) (by decide)

def fieldState (state : State) (index field : Nat) : State := state.setReg .rcx (state.words (cellSlot index field))

theorem fieldTrace (layout : Layout) (state : State) (index field : Nat)
    (bound : index < layout.capacity) (fieldBound : field < cellWords) (pointer : state.registers .r8 = layout.cell index) :
    Trace layout (fieldInstructions (8 * field)) state (fieldState state index field) :=
  .cons (loadField layout state .r8 .rcx index field bound fieldBound pointer) (.nil _)

def advanceState (state : State) : State :=
  ((state.setReg .rdx (state.registers .r8)).setReg .r8 (state.registers .r8 + 32)).setReg .r9 (state.registers .r9 - 1)

theorem advanceTrace (layout : Layout) (state : State) :
    Trace layout advanceInstructions state (advanceState state) := by
  refine .cons (.mov _ _ _) (.cons (.lea _ _ _) (.cons (.alu _ _ _ _) ?_))
  simpa [advanceState, cellBytes, operand_address _ .r8 32 (by decide), AluOp.eval, signExtend32] using
    Trace.nil (layout := layout) (advanceState state)

def inspectedState (state : State) (index : Nat) : State :=
  advanceState (fieldState (fieldState (fieldState state index 0) index 2) index 3)

theorem inspectSteps (layout : Layout) (state : State) (index : Nat)
    (bound : index + 1 < layout.capacity) (pointer : state.registers .r8 = layout.cell (index + 1))
    (previous : state.registers .rdx = layout.cell index) (link : LinkAt layout state.words (index + 1))
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    Steps runtime (RuntimeTarget.checked foldCounters) 10 (leaf (state.core memory) 22 0)
      (leaf ((inspectedState state (index + 1)).core memory) 21 0) := by
  let tagged := fieldState state (index + 1) 0
  let linked := fieldState tagged (index + 1) 2
  let padded := fieldState linked (index + 1) 3
  have tag := guardSteps (foldCounters := foldCounters) (fieldTrace layout state (index + 1) 0 bound (by decide) pointer) rfl outside memory represented
    runtime 22 23 .rcx (.imm 1) .eq ⟨rfl, by decide⟩
    (by simp [fieldState, wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core, AluSource.eval,
      signExtend32, link.tag, consTag]) (by decide)
  have tail := guardSteps (foldCounters := foldCounters) (fieldTrace layout tagged (index + 1) 2 bound (by decide) (by simpa [tagged, fieldState] using pointer))
    rfl outside memory represented runtime 23 24 .rcx (.reg .rdx) .eq ⟨rfl, by decide⟩
    (by simp [fieldState, tagged, wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core, AluSource.eval,
      link.tail, previous]) (by decide)
  have padding := guardSteps (foldCounters := foldCounters) (fieldTrace layout linked (index + 1) 3 bound (by decide)
    (by simpa [linked, tagged, fieldState] using pointer)) rfl outside memory represented runtime 24 25 .rcx (.imm 0) .eq
    ⟨rfl, by decide⟩ (by simp [fieldState, linked, tagged, wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core,
      AluSource.eval, link.padding, signExtend32]) (by decide)
  have advance := (advanceTrace layout padded).jump_readOnly rfl outside memory represented runtime (RuntimeTarget.checked foldCounters) 25 21
    ⟨rfl, by decide⟩ (hasBlock 21 (by decide))
  exact tag.append (tail.append (padding.append advance))

theorem inspectedState_register (state : State) (index : Nat) (register : GPR)
    (kept : register ∉ [.rcx, .rdx, .r8, .r9]) :
    (inspectedState state index).registers register = state.registers register := by
  cases register <;> simp_all [inspectedState, advanceState, fieldState]

theorem inspectedState_saved (state : State) (index : Nat) : PreservesSaved state (inspectedState state index) := by
  intro register saved
  apply inspectedState_register
  cases register <;> simp_all [Saved]

structure Scanned (layout : Layout) (length : Nat) (before after : State) : Prop where
  words : after.words = before.words
  root : after.registers .rdx = layout.cell length
  context : after.registers .rdi = before.registers .rdi
  length : after.registers .rsi = before.registers .rsi
  saved : PreservesSaved before after

theorem scanSteps (layout : Layout) (values : List Word) (remaining index : Nat) (state : State)
    (chain : DownChain layout state.words values) (capacity : values.length + 2 ≤ layout.capacity)
    (position : index + remaining = values.length)
    (previous : state.registers .rdx = layout.cell index)
    (pointer : state.registers .r8 = layout.cell (index + 1))
    (counter : state.registers .r9 = UInt64.ofNat remaining)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    ∃ after, Scanned layout values.length state after ∧
      Steps runtime (RuntimeTarget.checked foldCounters) (11 * remaining + 1) (leaf (state.core memory) 21 0)
        (leaf (after.core memory) 2 0) := by
  induction remaining generalizing index state with
  | zero =>
      have dispatch := (Trace.nil (layout := layout) state).branch_readOnly rfl outside memory represented runtime
        (RuntimeTarget.checked foldCounters) 21 2 22 (wordCompare .r9 (.imm 0)) .eq ⟨rfl, by decide⟩ true
        (by simp [wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core, AluSource.eval, counter, signExtend32])
        (hasBlock 2 (by decide))
      exact ⟨state, ⟨rfl, by simpa [show index = values.length by omega] using previous, rfl, rfl, PreservesSaved.refl state⟩, dispatch⟩
  | succ remaining ih =>
      have countSmall : remaining + 1 < UInt64.size := by
        have := layout.capacityBound
        change layout.capacity ≤ 66 at this
        change remaining + 1 < 18446744073709551616
        omega
      have nonzero : UInt64.ofNat (remaining + 1) ≠ 0 := by
        intro equal
        have natEqual := congrArg UInt64.toNat equal
        rw [UInt64.toNat_ofNat_of_lt' countSmall] at natEqual
        change remaining + 1 = 0 at natEqual
        omega
      have dispatch := (Trace.nil (layout := layout) state).branch_readOnly rfl outside memory represented runtime
        (RuntimeTarget.checked foldCounters) 21 2 22 (wordCompare .r9 (.imm 0)) .eq ⟨rfl, by decide⟩ false
        (by simpa [wordCompare, Compare.holds, Condition.holds, Core.readReg, State.core, AluSource.eval,
          counter, signExtend32] using nonzero) (hasBlock 22 (by decide))
      have inspect := inspectSteps (foldCounters := foldCounters) layout state index (by omega) pointer previous
        (down_link chain (index + 1) (by omega) (by omega)) outside memory represented runtime
      let next := inspectedState state (index + 1)
      obtain ⟨after, result, rest⟩ := ih (index + 1) next chain (by omega)
        (by simpa [next, inspectedState, advanceState, fieldState] using pointer)
        (by simp [next, inspectedState, advanceState, fieldState, pointer, cell_successor])
        (by simp [next, inspectedState, advanceState, fieldState, counter, UInt64.ofNat_add]) represented
      refine ⟨after, ⟨result.words, result.root, ?_, ?_, (inspectedState_saved state _).trans result.saved⟩, ?_⟩
      · exact result.context.trans (inspectedState_register state _ .rdi (by decide))
      · exact result.length.trans (inspectedState_register state _ .rsi (by decide))
      · have all := dispatch.append (inspect.append rest)
        simp only [List.length_nil, Nat.zero_add] at all
        have cost : 1 + (10 + (11 * remaining + 1)) = 11 * (remaining + 1) + 1 := by omega
        rw [cost] at all
        exact all

structure Prepared (layout : Layout) (values : List Word) (before after : State) : Prop where
  words : after.words = before.words
  root : after.registers .rdx = layout.cell values.length
  context : after.registers .rdi = layout.base
  saved : PreservesSaved before after

theorem validationSteps (layout : Layout) (values : List Word) (state : State)
    (input : Input layout values state) (capacity : values.length + 2 ≤ layout.capacity)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    ∃ after, Prepared layout values state after ∧
      Steps runtime (RuntimeTarget.checked foldCounters) (validationCost values.length) (leaf (state.core memory) 0 0)
        (leaf (after.core memory) 2 0) := by
  let described := descriptorState state
  let start := nilState layout described
  have headerRun := descriptorSteps (foldCounters := foldCounters) layout values.length state capacity input.counts input.context input.length
    outside memory represented runtime
  have describedContext : described.registers .rdi = layout.base :=
    (descriptorState_register state .rdi (by decide)).trans input.context
  have describedLength : described.registers .rsi = UInt64.ofNat values.length :=
    (descriptorState_register state .rsi (by decide)).trans input.length
  have nilRun := nilSteps (foldCounters := foldCounters) layout described describedContext (by omega) (down_nil input.chain) outside memory represented runtime
  obtain ⟨after, result, scan⟩ := scanSteps (foldCounters := foldCounters) layout values values.length 0 start input.chain capacity (by omega)
    (by simp [start, nilState, nilFieldsState, nilSetupState])
    (by simp [start, nilState, nilFieldsState, nilSetupState])
    (by simpa [start, nilState, nilFieldsState, nilSetupState] using describedLength)
    outside memory represented runtime
  have savedNil : PreservesSaved described start := by
    intro register saved
    cases register <;> simp_all [Saved, start, nilState, nilFieldsState, nilSetupState]
  refine ⟨after, ⟨result.words, result.root, ?_, ((descriptorState_saved state).trans savedNil).trans result.saved⟩, ?_⟩
  · exact result.context.trans (by simpa [start, nilState, nilFieldsState, nilSetupState] using describedContext)
  · have all := headerRun.append (nilRun.append scan)
    have cost : 33 + (11 + (11 * values.length + 1)) = validationCost values.length := by
      simp only [validationCost]
      omega
    rw [cost] at all
    exact all

end Ix.Compiler.X86.RuntimeExecution
