import Compilatrix.X86.HeapCopies

namespace Compilatrix.X86.HeapMacros
open WordRegion PhysicalHeap HeapArena

def counter (state : State) (field : Nat) (change : Word → Word) : State :=
  (state.setReg .rcx (change (state.words field))).setWord field (change (state.words field))

theorem counter_stable (state : State) (field : Nat) (change : Word → Word) :
    Scalar.Stable state (counter state field change) :=
  (Scalar.Stable.setReg _ _ _ (by simp)).trans (Scalar.Stable.setWord _ _ _)

@[simp] theorem counter_register {state : State} {field : Nat} {change : Word → Word} {register : GPR}
    (different : register ≠ .rcx) : (counter state field change).registers register = state.registers register := by
  simp [counter, different]

theorem increment_trace {layout : HeapArena.Layout} {state : State} {holes : Stream.Holes}
    {returns : List ReturnFrame} (based : Based layout state) (access : Access layout holes returns)
    {field amount : Nat} (fieldBound : field < headerWords) (small : amount < 2147483648) :
    SafeTrace layout.region returns (HeapTarget.increment field amount) state holes
      (counter state field (· + UInt64.ofNat amount)) holes := by
  have read := load_header based access .rcx fieldBound
  have add := SafeTrace.alu layout.region returns (state.setReg .rcx (state.words field)) holes
    .add .rcx (.imm (UInt32.ofNat amount))
  simp only [State.setReg_registers, beq_self_eq_true, if_true, State.alu, AluSource.eval,
    signed_nat small, AluOp.eval, State.setReg_setReg] at add
  have write := store_header (layout := layout)
    (based.stable (Scalar.Stable.setReg _ _ _ (by simp))) access .rcx fieldBound
    (state := state.setReg .rcx (state.words field + UInt64.ofNat amount))
  simpa only [HeapTarget.increment, counter, List.cons_append, List.nil_append,
    State.setReg_registers, beq_self_eq_true, if_true] using (read.append add).append write

theorem decrement_trace {layout : HeapArena.Layout} {state : State} {holes : Stream.Holes}
    {returns : List ReturnFrame} (based : Based layout state) (access : Access layout holes returns)
    {field : Nat} (fieldBound : field < headerWords) :
    SafeTrace layout.region returns (HeapTarget.decrement field) state holes
      (counter state field (· - 1)) holes := by
  have read := load_header based access .rcx fieldBound
  have sub := SafeTrace.alu layout.region returns (state.setReg .rcx (state.words field)) holes
    .sub .rcx (.imm 1)
  simp only [State.setReg_registers, beq_self_eq_true, if_true, State.alu, AluSource.eval,
    show signExtend32 1 = 1 from by decide, AluOp.eval, State.setReg_setReg] at sub
  have write := store_header (layout := layout)
    (based.stable (Scalar.Stable.setReg _ _ _ (by simp))) access .rcx fieldBound
    (state := state.setReg .rcx (state.words field - 1))
  simpa only [HeapTarget.decrement, counter, List.cons_append, List.nil_append,
    State.setReg_registers, beq_self_eq_true, if_true] using (read.append sub).append write

def tag (state : State) (index : Nat) (word : Word) : State :=
  (state.setReg .rcx word).setWord (cellSlot index 0) word

theorem tag_stable (state : State) (index : Nat) (word : Word) :
    Scalar.Stable state (tag state index word) :=
  (Scalar.Stable.setReg _ _ _ (by simp)).trans (Scalar.Stable.setWord _ _ _)

@[simp] theorem tag_register {state : State} {index : Nat} {word : Word} {register : GPR}
    (different : register ≠ .rcx) : (tag state index word).registers register = state.registers register := by
  simp [tag, different]

theorem tag_trace {layout : HeapArena.Layout} {state : State} {holes : Stream.Holes}
    {returns : List ReturnFrame} (access : Access layout holes returns) {index : Nat}
    (allocated : index < capacity) (pointer : state.registers .rax = layout.pointer index) (word : Word) :
    SafeTrace layout.region returns (HeapTarget.setTag word) state holes (tag state index word) holes := by
  have moved := SafeTrace.mov layout.region returns state holes .rcx (.imm word)
  have written := store_field (state := state.setReg .rcx word) access .rcx allocated (by decide : 0 < cellWords)
    (by simpa using pointer)
  simpa only [HeapTarget.setTag, tag, List.singleton_append,
    State.move_imm, State.setReg_registers, beq_self_eq_true, if_true] using moved.append written

def writeCell (state : State) (index : Nat) (ctor : Constructor) : State :=
  (((tag state index ctor.tag).setWord (cellSlot index 1) (state.registers .r8)).setWord
    (cellSlot index 2) (state.registers .r9)).setReg .rcx 0 |>.setWord (cellSlot index 3) 0

theorem writeCell_stable (state : State) (index : Nat) (ctor : Constructor) :
    Scalar.Stable state (writeCell state index ctor) :=
  ((((tag_stable _ _ _).trans (Scalar.Stable.setWord _ _ _)).trans (Scalar.Stable.setWord _ _ _)).trans
    (Scalar.Stable.setReg _ _ _ (by simp))).trans (Scalar.Stable.setWord _ _ _)

@[simp] theorem writeCell_register {state : State} {index : Nat} {ctor : Constructor} {register : GPR}
    (different : register ≠ .rcx) : (writeCell state index ctor).registers register = state.registers register := by
  simp [writeCell, tag, different]

theorem writeCell_trace {layout : HeapArena.Layout} {state : State} {holes : Stream.Holes}
    {returns : List ReturnFrame} (access : Access layout holes returns) {index : Nat}
    (allocated : index < capacity) (pointer : state.registers .rax = layout.pointer index) (ctor : Constructor) :
    SafeTrace layout.region returns (HeapTarget.writeCell ctor) state holes (writeCell state index ctor) holes := by
  have tagged := tag_trace access allocated pointer ctor.tag
  have first := store_field (state := tag state index ctor.tag) access .r8 allocated (by decide : 1 < cellWords)
    (by simpa using pointer)
  have second := store_field (state := (tag state index ctor.tag).setWord (cellSlot index 1) (state.registers .r8))
    access .r9 allocated (by decide : 2 < cellWords) (by simpa using pointer)
  have zero := SafeTrace.mov layout.region returns
    (((tag state index ctor.tag).setWord (cellSlot index 1) (state.registers .r8)).setWord
      (cellSlot index 2) (state.registers .r9)) holes .rcx (.imm 0)
  have padding := store_field (state := (((tag state index ctor.tag).setWord (cellSlot index 1)
    (state.registers .r8)).setWord (cellSlot index 2) (state.registers .r9)).setReg .rcx 0)
    access .rcx allocated (by decide : 3 < cellWords) (by simpa using pointer)
  simpa only [HeapTarget.writeCell, writeCell, List.append_assoc,
    tag_register (by decide : GPR.r8 ≠ .rcx), tag_register (by decide : GPR.r9 ≠ .rcx),
    State.setWord_registers, State.move_imm, State.setReg_registers, beq_self_eq_true, if_true,
    List.cons_append, List.nil_append] using (((tagged.append first).append second).append zero).append padding

def fieldValue {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (arguments : Array Scalar.Atom) (index : Nat) : Word :=
  HeapCopies.atomValue frame state (arguments[index]?.getD (.constant 0))

def fields {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (arguments : Array Scalar.Atom) : State :=
  (state.setReg .r8 (fieldValue frame state arguments 0)).setReg .r9 (fieldValue frame state arguments 1)

theorem fields_stable {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (arguments : Array Scalar.Atom) : Scalar.Stable state (fields frame state arguments) :=
  (Scalar.Stable.setReg _ _ _ (by simp)).trans (Scalar.Stable.setReg _ _ _ (by simp))

theorem defaultAtom_valid {arguments : Array Scalar.Atom} (valid : arguments.all (·.valid maxValues) = true) (index : Nat) :
    (arguments[index]?.getD (.constant 0)).valid Scalar.maxLocals = true := by
  cases found : arguments[index]? with
  | none => rfl
  | some source =>
      obtain ⟨bound, same⟩ := Array.getElem?_eq_some_iff.mp found
      have small := Array.all_eq_true.mp valid index bound
      rw [same] at small
      cases source with
      | constant word => rfl
      | var slot =>
          change decide (slot < Scalar.maxLocals) = true
          have small : slot < maxValues := of_decide_eq_true small
          exact decide_eq_true (by simp only [maxValues, Scalar.maxLocals] at *; omega)

theorem fields_trace {layout : WordRegion.Layout} {frame : Scalar.Frame layout} {state : State}
    {holes : Stream.Holes} {returns : List ReturnFrame} {rootTop : Nat} {arguments : Array Scalar.Atom}
    (framed : Scalar.Framed frame state) (safe : Scalar.HolesIn layout rootTop holes)
    (valid : arguments.all (·.valid maxValues) = true) :
    SafeTrace layout returns (HeapTarget.fields arguments) state holes (fields frame state arguments) holes := by
  have first := Scalar.load_safeTrace (returns := returns) framed (HeapCopies.slots_at frame state) safe .r8
    (HeapCopies.atom_found frame state (defaultAtom_valid valid 0))
  have second := Scalar.load_safeTrace (returns := returns)
    ((Scalar.Stable.setReg _ _ _ (by simp)).framed framed)
    (HeapCopies.slots_at frame (state.setReg .r8 (fieldValue frame state arguments 0))) safe .r9
    (HeapCopies.atom_found frame (state.setReg .r8 (fieldValue frame state arguments 0)) (defaultAtom_valid valid 1))
  simpa only [HeapTarget.fields, fields, fieldValue, HeapCopies.atomValue_setReg,
    List.singleton_append] using first.append second

def capture {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index field destination : Nat) : State :=
  let word := state.words (cellSlot index (field + 1))
  (state.setReg .rcx word).setWord (frame.localIndex destination) word

theorem capture_stable {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index field destination : Nat) : Scalar.Stable state (capture frame state index field destination) :=
  (Scalar.Stable.setReg _ _ _ (by simp)).trans (Scalar.Stable.setWord _ _ _)

@[simp] theorem capture_register {layout : WordRegion.Layout} {frame : Scalar.Frame layout} {state : State}
    {index field destination : Nat} {register : GPR} (different : register ≠ .rcx) :
    (capture frame state index field destination).registers register = state.registers register := by
  simp [capture, different]

theorem capture_trace {layout : HeapArena.Layout} {frame : Scalar.Frame layout.region} {state : State}
    {holes : Stream.Holes} {returns : List ReturnFrame} {rootTop index field destination : Nat}
    (framed : Scalar.Framed frame state) (safe : Scalar.HolesIn layout.region rootTop holes)
    (frames : Scalar.FramesAbove layout.region frame.top returns) (access : Access layout holes returns)
    (allocated : index < capacity) (fieldBound : field < 2) (destinationBound : destination < Scalar.maxLocals)
    (pointer : state.registers .rax = layout.pointer index) :
    SafeTrace layout.region returns [.load .w64 .rcx (HeapArena.cellField (field + 1)),
      .spill (Scalar.slot destination) .rcx] state holes (capture frame state index field destination) holes := by
  have read := load_field (field := field + 1) access .rcx allocated (by simp only [cellWords]; omega) pointer
  have readable := safe.readable (frame.local_bound destination) (.inl (frame.local_ordinary destinationBound))
  have write := SafeTrace.spill layout.region returns
    (state.setReg .rcx (state.words (cellSlot index (field + 1)))) holes (Scalar.slot destination) .rcx
    (frame.localIndex destination) (frame.local_bound destination)
    (by simpa only [State.setReg_registers, show (GPR.rbp == .rcx) = false from by decide, Bool.false_eq_true, if_false,
      framed.1] using frame.local_address destinationBound) (frame.local_disjoint frames destination)
  simpa only [capture, State.setReg_registers, beq_self_eq_true, if_true, clear_readable readable,
    List.singleton_append] using read.append write

def captureFields {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index count destination : Nat) : State :=
  match count with
  | 0 => state
  | 1 => capture frame state index 0 destination
  | _ => capture frame (capture frame state index 0 destination) index 1 (destination + 1)

theorem captureFields_stable {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index count destination : Nat) : Scalar.Stable state (captureFields frame state index count destination) := by
  cases count with
  | zero => exact .refl _
  | succ count => cases count with
    | zero => exact capture_stable _ _ _ _ _
    | succ count => exact (capture_stable _ _ _ _ _).trans (capture_stable _ _ _ _ _)

@[simp] theorem captureFields_register {layout : WordRegion.Layout} {frame : Scalar.Frame layout} {state : State}
    {index count destination : Nat} {register : GPR} (different : register ≠ .rcx) :
    (captureFields frame state index count destination).registers register = state.registers register := by
  cases count with
  | zero => rfl
  | succ count => cases count <;> simp [captureFields, capture_register different]

theorem captureFields_trace {layout : HeapArena.Layout} {frame : Scalar.Frame layout.region} {state : State}
    {holes : Stream.Holes} {returns : List ReturnFrame} {rootTop index count destination : Nat}
    (framed : Scalar.Framed frame state) (safe : Scalar.HolesIn layout.region rootTop holes)
    (frames : Scalar.FramesAbove layout.region frame.top returns) (access : Access layout holes returns)
    (allocated : index < capacity) (countBound : count ≤ 2) (destinationBound : destination + count ≤ Scalar.maxLocals)
    (pointer : state.registers .rax = layout.pointer index) :
    SafeTrace layout.region returns (HeapTarget.reserveFields count destination) state holes
      (captureFields frame state index count destination) holes := by
  have cases : count = 0 ∨ count = 1 ∨ count = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · exact .nil _ _
  · simpa [HeapTarget.reserveFields, captureFields, List.range_succ] using
      capture_trace (destination := destination) framed safe frames access allocated (by decide : 0 < 2) (by omega) pointer
  · have first := capture_trace (destination := destination) framed safe frames access allocated (by decide : 0 < 2) (by omega) pointer
    have second := capture_trace (state := capture frame state index 0 destination)
      ((capture_stable _ _ _ _ _).framed framed) safe frames access allocated (by decide : 1 < 2)
      (by omega : destination + 1 < Scalar.maxLocals) (by simpa using pointer)
    simpa [HeapTarget.reserveFields, captureFields, List.range_succ] using first.append second

theorem cursor_trace {layout : HeapArena.Layout} {state : State} {holes : Stream.Holes}
    {returns : List ReturnFrame} {index : Nat} (based : Based layout state) (access : Access layout holes returns)
    (cursor : state.words 0 = UInt64.ofNat (32 * index)) :
    SafeTrace layout.region returns [.load .w64 .rax (HeapArena.header 0),
      .alu .add .w64 .rax (.reg .r15), .alu .add .w64 .rax (.imm 128)] state holes
      (state.setReg .rax (layout.pointer index)) holes := by
  have read := load_header based access .rax (by decide : 0 < headerWords)
  have base := SafeTrace.alu layout.region returns (state.setReg .rax (state.words 0)) holes .add .rax (.reg .r15)
  have offset := SafeTrace.alu layout.region returns
    (state.setReg .rax (state.words 0 + state.registers .r15)) holes .add .rax (.imm 128)
  simp only [State.setReg_registers, beq_self_eq_true, if_true, State.alu_reg, AluOp.eval,
    show (GPR.r15 == .rax) = false from by decide, Bool.false_eq_true, if_false, State.setReg_setReg] at base
  simp only [State.setReg_registers, beq_self_eq_true, if_true, State.alu, AluSource.eval,
    show signExtend32 128 = 128 from by decide, AluOp.eval, State.setReg_setReg] at offset
  have address : state.words 0 + state.registers .r15 + 128 = layout.pointer index := by
    rw [cursor, based]
    change UInt64.ofNat (32 * index) + layout.region.base + 128 =
      layout.region.base + UInt64.ofNat (8 * cellSlot index 0)
    have offset : 8 * cellSlot index 0 = 32 * index + 128 := by
      simp only [cellSlot, headerWords, cellWords]; omega
    rw [offset, UInt64.ofNat_add, UInt64.add_comm (UInt64.ofNat (32 * index)) layout.region.base,
      UInt64.add_assoc]
    rfl
  simpa only [address, List.cons_append, List.nil_append] using (read.append base).append offset

end Compilatrix.X86.HeapMacros
