import Ix.Compiler.X86.UniqueExecution

/-! Instruction selection lemmas for arena allocation, reservation, reuse,
and release. The traces retain every selected load, store, and counter update. -/

namespace Ix.Compiler.X86.UniqueABI


theorem Layout.field_bound (layout : Layout) (field : Field) : field.index < layout.slots := by
  have := field.index_lt
  simp only [Layout.slots] at *
  omega

theorem Layout.cell_field_bound (layout : Layout) {index field : Nat}
    (indexBound : index < layout.capacity) (fieldBound : field < cellWords) :
    cellSlot index field < layout.slots := by
  simp only [cellSlot, Layout.slots, cellWords] at *
  omega

theorem Layout.cell_offset (layout : Layout) (index field : Nat) :
    layout.cell index + UInt64.ofNat (8 * field) = layout.address (cellSlot index field) := by
  simp [Layout.cell, Layout.address, cellSlot, Nat.mul_add, UInt64.ofNat_add, UInt64.add_assoc]

theorem Layout.allocate_address (layout : Layout) (index : Nat) :
    layout.base + UInt64.ofNat (cellBytes * index) + 80 = layout.cell index := by
  simp [Layout.cell, Layout.address, cellSlot, headerWords, cellWords, cellBytes,
    Nat.mul_add, ← Nat.mul_assoc, UInt64.ofNat_add,
    UInt64.add_comm, word_add_left_comm]

end Ix.Compiler.X86.UniqueABI

namespace Ix.Compiler.X86.UniqueExecution

open UniqueABI UniqueTarget

theorem operand_address (state : State) (register : GPR) (offset : Nat)
    (small : offset < 0x80000000) :
    state.address (memoryOperand register offset) = state.registers register + UInt64.ofNat offset := by
  have small32 : UInt32.ofNat offset < 0x80000000 := by
    change (UInt32.ofNat offset).toNat < 2147483648
    rw [UInt32.toNat_ofNat_of_lt' (by change offset < 4294967296; omega)]
    exact small
  have widened : (UInt32.ofNat offset).toUInt64 = UInt64.ofNat offset := by
    apply UInt64.toNat_inj.mp
    simp only [UInt32.toNat_toUInt64, UInt32.toNat_ofNat', UInt64.toNat_ofNat']
    omega
  simp [State.address, State.core, MemAddr.eval, Core.readReg, memoryOperand, signExtend32, small32, widened]

theorem header_address (state : State) (layout : Layout) (field : Field)
    (context : state.registers .rdi = layout.base) :
    state.address (header field) = layout.address field.index := by
  rw [header, operand_address _ _ _ (by have := field.index_lt; change field.index < 10 at this; omega), context]
  rfl

@[simp] theorem State.setReg_registers (state : State) (register candidate : GPR) (value : Word) :
    (state.setReg register value).registers candidate =
      if candidate == register then value else state.registers candidate := rfl
@[simp] theorem State.setWord_registers (state : State) (slot : Nat) (value : Word) :
    (state.setWord slot value).registers = state.registers := rfl
@[simp] theorem State.setReg_words (state : State) (register : GPR) (value : Word) :
    (state.setReg register value).words = state.words := rfl
@[simp] theorem State.setWord_words (state : State) (slot : Nat) (value : Word) :
    (state.setWord slot value).words = state.words.set slot value := rfl
@[simp] theorem State.move_imm (state : State) (value : Word) : state.move (.imm value) = value := rfl
@[simp] theorem State.move_reg (state : State) (register : GPR) :
    state.move (.reg register) = state.registers register := rfl
@[simp] theorem State.alu_imm (state : State) (value : Imm32) :
    state.alu (.imm value) = signExtend32 value := rfl
@[simp] theorem State.alu_reg (state : State) (register : GPR) :
    state.alu (.reg register) = state.registers register := rfl

@[simp] theorem State.setReg_setReg (state : State) (register : GPR) (first second : Word) :
    (state.setReg register first).setReg register second = state.setReg register second := by
  simp [State.setReg]

def counterState (state : State) (field : Field) (operation : AluOp) (amount : Imm32) : State :=
  let value := operation.eval (state.words field.index) (signExtend32 amount)
  (state.setReg .r11 value).setWord field.index value

theorem counterTrace (layout : Layout) (state : State) (field : Field) (operation : AluOp) (amount : Imm32)
    (context : state.registers .rdi = layout.base) :
    Trace layout (changeCounter field operation amount) state (counterState state field operation amount) := by
  refine .cons (.load _ _ _ field.index (layout.field_bound field) (header_address state layout field context)) ?_
  refine .cons (.alu _ _ _ _) ?_
  refine .cons (.store _ _ _ field.index (layout.field_bound field) ?_) ?_
  · apply header_address
    simpa using context
  · simpa [counterState] using
      (Trace.nil (layout := layout)
        (((state.setReg .r11 (state.words field.index)).setReg .r11
          (operation.eval (state.words field.index) (signExtend32 amount))).setWord field.index
            (operation.eval (state.words field.index) (signExtend32 amount))))

@[simp] theorem counterState_registers (state : State) (field : Field) (operation : AluOp)
    (amount : Imm32) (register : GPR) :
    (counterState state field operation amount).registers register =
      if register == .r11 then operation.eval (state.words field.index) (signExtend32 amount)
      else state.registers register := rfl

theorem field_address (layout : Layout) (state : State) (pointer : GPR) (index field : Nat)
    (fieldBound : field < cellWords) (atCell : state.registers pointer = layout.cell index) :
    state.address (memoryOperand pointer (8 * field)) = layout.address (cellSlot index field) := by
  rw [operand_address _ _ _ (by change field < 4 at fieldBound; omega), atCell, layout.cell_offset]

theorem loadField (layout : Layout) (state : State) (pointer destination : GPR) (index field : Nat)
    (indexBound : index < layout.capacity) (fieldBound : field < cellWords)
    (atCell : state.registers pointer = layout.cell index) :
    Effect layout (.load .w64 destination (memoryOperand pointer (8 * field))) state
      (state.setReg destination (state.words (cellSlot index field))) :=
  .load _ _ _ _ (layout.cell_field_bound indexBound fieldBound)
    (field_address layout state pointer index field fieldBound atCell)

theorem storeField (layout : Layout) (state : State) (pointer source : GPR) (index field : Nat)
    (indexBound : index < layout.capacity) (fieldBound : field < cellWords)
    (atCell : state.registers pointer = layout.cell index) :
    Effect layout (.store .w64 (memoryOperand pointer (8 * field)) source) state
      (state.setWord (cellSlot index field) (state.registers source)) :=
  .store _ _ _ _ (layout.cell_field_bound indexBound fieldBound)
    (field_address layout state pointer index field fieldBound atCell)

def writeSourceState (state : State) (slot : Nat) (source : MoveSource) : State :=
  (state.setReg .rcx (state.move source)).setWord slot (state.move source)

@[simp] theorem writeSourceState_registers (state : State) (slot : Nat) (source : MoveSource) (register : GPR) :
    (writeSourceState state slot source).registers register =
      if register == .rcx then state.move source else state.registers register := rfl

theorem writeSourceTrace (layout : Layout) (state : State) (pointer : GPR) (index field : Nat)
    (source : MoveSource) (indexBound : index < layout.capacity) (fieldBound : field < cellWords)
    (atCell : state.registers pointer = layout.cell index) (notScratch : pointer ≠ .rcx) :
    Trace layout [.mov .w64 .rcx source, .store .w64 (memoryOperand pointer (8 * field)) .rcx]
      state (writeSourceState state (cellSlot index field) source) := by
  refine .cons (.mov _ _ _) (.cons (storeField layout _ pointer .rcx index field indexBound fieldBound ?_) ?_)
  · simpa [notScratch] using atCell
  · simpa [writeSourceState] using
      (Trace.nil (layout := layout) ((state.setReg .rcx (state.move source)).setWord
        (cellSlot index field) (state.move source)))

def prepareAllocation (state : State) (layout : Layout) (index : Nat) : State :=
  ((state.setReg .rax (layout.cell index)).setReg .r11 (state.words Field.cursor.index + 32)).setWord
    Field.cursor.index (state.words Field.cursor.index + 32)

@[simp] theorem prepareAllocation_registers (state : State) (layout : Layout) (index : Nat) (register : GPR) :
    (prepareAllocation state layout index).registers register =
      if register == .r11 then state.words Field.cursor.index + 32
      else if register == .rax then layout.cell index else state.registers register := rfl

theorem prepareAllocationTrace (layout : Layout) (state : State) (index : Nat)
    (context : state.registers .rdi = layout.base)
    (cursor : state.words Field.cursor.index = UInt64.ofNat (cellBytes * index)) :
    Trace layout
      [.load .w64 .rax (header .cursor), .lea .r11 (memoryOperand .rax cellBytes),
       .store .w64 (header .cursor) .r11,
       .lea .rax { base := some .rdi, index := some .rax, displacement := 80 }]
      state (prepareAllocation state layout index) := by
  refine .cons (.load _ _ _ Field.cursor.index (layout.field_bound .cursor)
    (header_address state layout .cursor context)) (.cons (.lea _ _ _) ?_)
  refine .cons (.store _ _ _ Field.cursor.index (layout.field_bound .cursor) ?_) (.cons (.lea _ _ _) ?_)
  · apply header_address
    simpa using context
  · have bump : (state.setReg .rax (state.words Field.cursor.index)).address (memoryOperand .rax cellBytes) =
        state.words Field.cursor.index + 32 := by
      simpa [cellBytes] using operand_address (state.setReg .rax (state.words Field.cursor.index)) .rax cellBytes
        (by decide)
    simp only [bump, State.setReg_registers, beq_self_eq_true, ↓reduceIte]
    have atPointer :
        (((state.setReg .rax (state.words Field.cursor.index)).setReg .r11
          (state.words Field.cursor.index + 32)).setWord Field.cursor.index
            (state.words Field.cursor.index + 32)).address
          { base := some .rdi, index := some .rax, displacement := 80 } = layout.cell index := by
      simp [State.address, State.core, MemAddr.eval, Core.readReg, State.setReg, State.setWord,
        Registers.set, Scale.word, IndexReg.gpr, signExtend32, context, cursor]
      simpa only [UInt64.ofNat_mul] using layout.allocate_address index
    rw [atPointer]
    have reorder :
        ((((state.setReg .rax (state.words Field.cursor.index)).setReg .r11
          (state.words Field.cursor.index + 32)).setWord Field.cursor.index
            (state.words Field.cursor.index + 32)).setReg .rax (layout.cell index)) =
          prepareAllocation state layout index := by
      apply State.ext
      · funext register
        cases register <;> simp [prepareAllocation, State.setReg, State.setWord, Registers.set]
      · rfl
    rw [reorder]
    exact .nil _

def allocateState (state : State) (layout : Layout) (index : Nat)
    (tag head : Word) (tail : MoveSource) (destination : GPR) : State :=
  let s0 := prepareAllocation state layout index
  let s1 := writeSourceState s0 (cellSlot index 0) (.imm tag)
  let s2 := writeSourceState s1 (cellSlot index 1) (.imm head)
  let s3 := writeSourceState s2 (cellSlot index 2) tail
  let s4 := writeSourceState s3 (cellSlot index 3) (.imm 0)
  let s5 := counterState s4 .allocs .add 1
  let s6 := counterState s5 .live .add 1
  (s6.setWord Field.peak.index (s6.registers .r11)).setReg destination (s6.registers .rax)

theorem allocateTrace (layout : Layout) (state : State) (index : Nat)
    (tag head : Word) (tail : MoveSource) (destination : GPR)
    (indexBound : index < layout.capacity) (context : state.registers .rdi = layout.base)
    (cursor : state.words Field.cursor.index = UInt64.ofNat (cellBytes * index)) :
    Trace layout (allocate tag head tail destination) state
      (allocateState state layout index tag head tail destination) := by
  let s0 := prepareAllocation state layout index
  let s1 := writeSourceState s0 (cellSlot index 0) (.imm tag)
  let s2 := writeSourceState s1 (cellSlot index 1) (.imm head)
  let s3 := writeSourceState s2 (cellSlot index 2) tail
  let s4 := writeSourceState s3 (cellSlot index 3) (.imm 0)
  let s5 := counterState s4 .allocs .add 1
  let s6 := counterState s5 .live .add 1
  have h0 := prepareAllocationTrace layout state index context cursor
  have h1 := writeSourceTrace layout s0 .rax index 0 (.imm tag) indexBound (by decide) (by simp [s0]) (by decide)
  have h2 := writeSourceTrace layout s1 .rax index 1 (.imm head) indexBound (by decide) (by simp [s1, s0]) (by decide)
  have h3 := writeSourceTrace layout s2 .rax index 2 tail indexBound (by decide) (by simp [s2, s1, s0]) (by decide)
  have h4 := writeSourceTrace layout s3 .rax index 3 (.imm 0) indexBound (by decide) (by simp [s3, s2, s1, s0]) (by decide)
  have h5 := counterTrace layout s4 .allocs .add 1 (by simpa [s4, s3, s2, s1, s0] using context)
  have h6 := counterTrace layout s5 .live .add 1 (by simpa [s5, s4, s3, s2, s1, s0] using context)
  have last : Trace layout [.store .w64 (header .peak) .r11, .mov .w64 destination (.reg .rax)] s6
      ((s6.setWord Field.peak.index (s6.registers .r11)).setReg destination (s6.registers .rax)) := by
    refine .cons (.store _ _ _ Field.peak.index (layout.field_bound .peak) ?_) (.cons (.mov _ _ _) ?_)
    · apply header_address
      simpa [s6, s5, s4, s3, s2, s1, s0] using context
    · simpa using (Trace.nil (layout := layout)
        ((s6.setWord Field.peak.index (s6.registers .r11)).setReg destination (s6.registers .rax)))
  simpa [allocate, allocateState, List.append_assoc, s0, s1, s2, s3, s4, s5, s6] using
    h0.append (h1.append (h2.append (h3.append (h4.append (h5.append (h6.append last))))))

def reserveState (state : State) (index : Nat) : State :=
  let loaded := (state.setReg .r8 (state.words (cellSlot index 1))).setReg .r9 (state.words (cellSlot index 2))
  let reserved := writeSourceState loaded (cellSlot index 0) (.imm reservedTag)
  counterState (counterState reserved .reservations .add 1) .live .sub 1

theorem reserveTrace (layout : Layout) (state : State) (index : Nat) (indexBound : index < layout.capacity)
    (context : state.registers .rdi = layout.base) (pointer : state.registers .rdx = layout.cell index) :
    Trace layout reserveCons state (reserveState state index) := by
  let first := state.setReg .r8 (state.words (cellSlot index 1))
  let loaded := first.setReg .r9 (state.words (cellSlot index 2))
  let reserved := writeSourceState loaded (cellSlot index 0) (.imm reservedTag)
  let counted := counterState reserved .reservations .add 1
  have h0 : Trace layout [.load .w64 .r8 (memoryOperand .rdx 8), .load .w64 .r9 (memoryOperand .rdx 16)] state loaded := by
    refine .cons (loadField layout state .rdx .r8 index 1 indexBound (by decide) pointer)
      (.cons (loadField layout first .rdx .r9 index 2 indexBound (by decide) ?_) ?_)
    · simpa [first] using pointer
    · exact .nil _
  have h1 := writeSourceTrace layout loaded .rdx index 0 (.imm reservedTag) indexBound (by decide)
    (by simpa [loaded, first] using pointer) (by decide)
  have h2 := counterTrace layout reserved .reservations .add 1 (by simpa [reserved, loaded, first] using context)
  have h3 := counterTrace layout counted .live .sub 1 (by simpa [counted, reserved, loaded, first] using context)
  simpa [reserveCons, reserveState, loaded, first, reserved, counted, List.append_assoc] using
    h0.append (h1.append (h2.append h3))

def reuseState (state : State) (index : Nat) : State :=
  let payload := (state.setWord (cellSlot index 1) (state.registers .r8)).setWord
    (cellSlot index 2) (state.registers .rsi)
  let reused := writeSourceState payload (cellSlot index 0) (.imm consTag)
  let credited := counterState (counterState reused .reservations .sub 1) .live .add 1
  counterState (counterState credited .reuses .add 1) .payload .add 2

theorem reuseTrace (layout : Layout) (state : State) (index : Nat) (indexBound : index < layout.capacity)
    (context : state.registers .rdi = layout.base) (pointer : state.registers .rdx = layout.cell index) :
    Trace layout reuseCons state (reuseState state index) := by
  let first := state.setWord (cellSlot index 1) (state.registers .r8)
  let payload := first.setWord (cellSlot index 2) (state.registers .rsi)
  let reused := writeSourceState payload (cellSlot index 0) (.imm consTag)
  let unreserved := counterState reused .reservations .sub 1
  let credited := counterState unreserved .live .add 1
  let counted := counterState credited .reuses .add 1
  have h0 : Trace layout [.store .w64 (memoryOperand .rdx 8) .r8, .store .w64 (memoryOperand .rdx 16) .rsi] state payload := by
    exact .cons (storeField layout state .rdx .r8 index 1 indexBound (by decide) pointer)
      (.cons (storeField layout first .rdx .rsi index 2 indexBound (by decide) pointer) (.nil _))
  have h1 := writeSourceTrace layout payload .rdx index 0 (.imm consTag) indexBound (by decide) pointer (by decide)
  have h2 := counterTrace layout reused .reservations .sub 1 (by simpa [reused, payload, first] using context)
  have h3 := counterTrace layout unreserved .live .add 1 (by simpa [unreserved, reused, payload, first] using context)
  have h4 := counterTrace layout credited .reuses .add 1 (by simpa [credited, unreserved, reused, payload, first] using context)
  have h5 := counterTrace layout counted .payload .add 2 (by simpa [counted, credited, unreserved, reused, payload, first] using context)
  simpa [reuseCons, reuseState, first, payload, reused, unreserved, credited, counted, List.append_assoc] using
    h0.append (h1.append (h2.append (h3.append (h4.append h5))))

def releaseState (state : State) (index : Nat) : State :=
  let tagged := writeSourceState state (cellSlot index 0) (.imm freedTag)
  let cleared := ((writeSourceState tagged (cellSlot index 1) (.imm 0)).setWord (cellSlot index 2) 0).setWord
    (cellSlot index 3) 0
  counterState (counterState cleared .frees .add 1) .live .sub 1

theorem releaseTrace (layout : Layout) (state : State) (pointer : GPR) (index : Nat)
    (indexBound : index < layout.capacity) (context : state.registers .rdi = layout.base)
    (atCell : state.registers pointer = layout.cell index) (notScratch : pointer ≠ .rcx) :
    Trace layout (releaseCell pointer) state (releaseState state index) := by
  let tagged := writeSourceState state (cellSlot index 0) (.imm freedTag)
  let first := writeSourceState tagged (cellSlot index 1) (.imm 0)
  let second := first.setWord (cellSlot index 2) 0
  let cleared := second.setWord (cellSlot index 3) 0
  let counted := counterState cleared .frees .add 1
  have h0 := writeSourceTrace layout state pointer index 0 (.imm freedTag) indexBound (by decide) atCell notScratch
  have h1 := writeSourceTrace layout tagged pointer index 1 (.imm 0) indexBound (by decide)
    (by simpa [tagged, notScratch] using atCell) notScratch
  have h2 : Trace layout [.store .w64 (memoryOperand pointer 16) .rcx, .store .w64 (memoryOperand pointer 24) .rcx]
      first cleared := by
    refine .cons (storeField layout first pointer .rcx index 2 indexBound (by decide) ?_)
      (.cons (storeField layout second pointer .rcx index 3 indexBound (by decide) ?_) ?_)
    · simpa [first, tagged, notScratch] using atCell
    · simpa [second, first, tagged, notScratch] using atCell
    · simpa [cleared, second, first] using (Trace.nil (layout := layout) cleared)
  have h3 := counterTrace layout cleared .frees .add 1 (by simpa [cleared, second, first, tagged] using context)
  have h4 := counterTrace layout counted .live .sub 1 (by simpa [counted, cleared, second, first, tagged] using context)
  simpa [releaseCell, releaseState, tagged, first, second, cleared, counted, List.append_assoc] using
    h0.append (h1.append (h2.append (h3.append h4)))

def consState (state : State) (index : Nat) : State :=
  let reused := reuseState (reserveState state index) index
  (reused.setReg .rsi (reused.registers .rdx)).setReg .rdx (reused.registers .r9)

theorem consTrace (layout : Layout) (state : State) (index : Nat) (indexBound : index < layout.capacity)
    (context : state.registers .rdi = layout.base) (pointer : state.registers .rdx = layout.cell index) :
    Trace layout consInstructions state (consState state index) := by
  have first := reserveTrace layout state index indexBound context pointer
  have second := reuseTrace layout (reserveState state index) index indexBound
    (by simpa [reserveState] using context) (by simpa [reserveState] using pointer)
  have last : Trace layout [.mov .w64 .rsi (.reg .rdx), .mov .w64 .rdx (.reg .r9)]
      (reuseState (reserveState state index) index) (consState state index) := by
    refine .cons (.mov _ _ _) (.cons (.mov _ _ _) ?_)
    simpa [consState] using Trace.nil (layout := layout) (consState state index)
  exact first.append (second.append last)

end Ix.Compiler.X86.UniqueExecution
