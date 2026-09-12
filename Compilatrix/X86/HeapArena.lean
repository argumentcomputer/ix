import Compilatrix.X86.ScalarSafeFrames

/-! The first allocating CFG ABI uses a finite workspace. The first 272
words contain a 16-word descriptor and at most 64 four-word leaf cells;
ordinary 34-word scalar activations occupy the words above that prefix.
The internal arena register is `r15`, which every activation preserves.
An exported entry saves the caller's `r15` before installing the arena base.
-/

namespace Compilatrix.X86.HeapArena
open WordRegion

def capacity : Nat := 64
def headerWords : Nat := 16
def cellWords : Nat := 4
def heapWords : Nat := headerWords + cellWords * capacity

def cellSlot (index field : Nat) : Nat := headerWords + cellWords * index + field

def memory (base : GPR) (offset : Nat) : MemAddr :=
  { base := some base, displacement := UInt32.ofNat (8 * offset) }

def header (field : Nat) : MemAddr := memory .r15 field
def cellField (field : Nat) : MemAddr := memory .rax field

theorem signed_nat {number : Nat} (bound : number < 2147483648) :
    signExtend32 (UInt32.ofNat number) = UInt64.ofNat number := by
  have small : number < UInt32.size := by simp only [UInt32.size]; omega
  have positive : UInt32.ofNat number < 2147483648 := by
    change (UInt32.ofNat number).toNat < 2147483648
    simpa only [UInt32.toNat_ofNat_of_lt' small] using bound
  simp only [signExtend32, if_pos positive]
  apply UInt64.toNat_inj.mp
  have small64 : number < UInt64.size := by simp only [UInt64.size]; omega
  simp only [UInt32.toNat_toUInt64, UInt32.toNat_ofNat_of_lt' small,
    UInt64.toNat_ofNat_of_lt' small64]

theorem memory_eval (state : State) (base : GPR) {offset : Nat} (small : offset < 4096) :
    state.address (memory base offset) = state.registers base + UInt64.ofNat (8 * offset) := by
  have bound : 8 * offset < 2147483648 := by omega
  have small32 : 8 * offset < UInt32.size := by simp only [UInt32.size]; omega
  have small64 : 8 * offset < UInt64.size := by simp only [UInt64.size]; omega
  have convert : (UInt32.ofNat (8 * offset)).toUInt64 = UInt64.ofNat (8 * offset) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt32.toNat_toUInt64, UInt32.toNat_ofNat_of_lt' small32,
      UInt64.toNat_ofNat_of_lt' small64]
  change state.registers base + 0 + signExtend32 (UInt32.ofNat (8 * offset)) = _
  have positive : UInt32.ofNat (8 * offset) < 2147483648 := by
    change (UInt32.ofNat (8 * offset)).toNat < 2147483648
    rw [UInt32.toNat_ofNat_of_lt' small32]
    exact bound
  simp only [UInt64.add_zero, signExtend32, if_pos positive, convert]

theorem cellSlot_bound {index field : Nat} (allocated : index < capacity) (fieldBound : field < cellWords) :
    cellSlot index field < heapWords := by
  simp only [cellSlot, heapWords, headerWords, cellWords, capacity] at *
  omega

theorem cellSlot_injective {left right a b : Nat} (aBound : a < cellWords) (bBound : b < cellWords)
    (same : cellSlot left a = cellSlot right b) : left = right ∧ a = b := by
  simp only [cellSlot, cellWords] at *
  omega

theorem cellSlot_above (index field : Nat) : headerWords ≤ cellSlot index field := by
  simp only [cellSlot]; omega

structure Layout where
  region : WordRegion.Layout
  enough : heapWords ≤ region.slots

def Layout.pointer (layout : Layout) (index : Nat) : Word := layout.region.address (cellSlot index 0)

theorem Layout.cell_bound (layout : Layout) {index field : Nat}
    (allocated : index < capacity) (fieldBound : field < cellWords) :
    cellSlot index field < layout.region.slots :=
  Nat.lt_of_lt_of_le (cellSlot_bound allocated fieldBound) layout.enough

theorem Layout.header_bound (layout : Layout) {field : Nat} (fieldBound : field < headerWords) :
    field < layout.region.slots := by
  have := layout.enough
  simp only [heapWords] at this
  omega

theorem Layout.pointer_ne_zero (layout : Layout) {index : Nat} (allocated : index < capacity) :
    layout.pointer index ≠ 0 := by
  intro equal
  have same := congrArg UInt64.toNat equal
  change (layout.region.address (cellSlot index 0)).toNat = 0 at same
  rw [layout.region.address_toNat (layout.cell_bound allocated (by decide))] at same
  simp only [cellSlot, headerWords, cellWords] at same
  omega

theorem Layout.pointer_field (layout : Layout) (index field : Nat) :
    layout.pointer index + UInt64.ofNat (8 * field) = layout.region.address (cellSlot index field) := by
  rw [Layout.pointer, layout.region.add]
  rfl

def Based (layout : Layout) (state : State) : Prop := state.registers .r15 = layout.region.base

theorem Based.stable {layout : Layout} {before after : State} (based : Based layout before)
    (stable : Scalar.Stable before after) : Based layout after :=
  (stable .r15 (by simp)).trans based

/-- Return tokens may occupy stack words, but never the arena prefix. -/
structure Access (layout : Layout) (holes : Stream.Holes) (returns : List ReturnFrame) : Prop where
  reads : ∀ index < heapWords, Stream.ReadableData holes (layout.region.address index) 8
  writes : ∀ index < heapWords, Stream.FramesDisjoint returns (layout.region.address index) 8

theorem Access.empty (layout : Layout) : Access layout (fun _ => False) [] :=
  ⟨fun _ _ _ _ => id, by simp [Stream.FramesDisjoint]⟩

theorem Access.mono {layout : Layout} {holes smaller : Stream.Holes} {returns : List ReturnFrame}
    (access : Access layout holes returns) (subset : ∀ address, smaller address → holes address) :
    Access layout smaller returns := by
  refine ⟨?_, access.writes⟩
  intro _index bound offset offsetBound hidden
  exact access.reads _index bound offset offsetBound (subset _ hidden)

theorem Access.clear {layout : Layout} {holes : Stream.Holes} {returns : List ReturnFrame}
    (access : Access layout holes returns) (address : Word) (count : Nat) :
    Access layout (Stream.clearRange holes address count) returns := access.mono (fun _ h => h.1)

theorem Access.above {layout : Layout} {holes : Stream.Holes} {returns : List ReturnFrame}
    (reads : ∀ index < heapWords, Stream.ReadableData holes (layout.region.address index) 8)
    (frames : Scalar.FramesAbove layout.region heapWords returns) : Access layout holes returns :=
  ⟨reads, fun _index bound => frames.disjoint (Nat.lt_of_lt_of_le bound layout.enough) bound⟩

theorem header_address {layout : Layout} {state : State} (based : Based layout state)
    {field : Nat} (fieldBound : field < headerWords) :
    state.address (header field) = layout.region.address field := by
  rw [header, memory_eval state .r15 (by simp only [headerWords] at fieldBound; omega), based]
  rfl

theorem field_address (layout : Layout) (state : State) (index : Nat)
    (pointer : state.registers .rax = layout.pointer index) {field : Nat} (fieldBound : field < cellWords) :
    state.address (cellField field) = layout.region.address (cellSlot index field) := by
  rw [cellField, memory_eval state .rax (by simp only [cellWords] at fieldBound; omega), pointer,
    layout.pointer_field]

theorem load_header {layout : Layout} {state : State} {holes : Stream.Holes} {returns : List ReturnFrame}
    (based : Based layout state) (access : Access layout holes returns) (destination : GPR)
    {field : Nat} (fieldBound : field < headerWords) :
    SafeTrace layout.region returns [.load .w64 destination (header field)] state holes
      (state.setReg destination (state.words field)) holes :=
  SafeTrace.load _ _ _ _ _ _ _ (layout.header_bound fieldBound) (header_address based fieldBound)
    (access.reads field (by simp only [heapWords]; omega))

theorem load_field {layout : Layout} {state : State} {holes : Stream.Holes} {returns : List ReturnFrame}
    (access : Access layout holes returns) (destination : GPR) {index field : Nat}
    (allocated : index < capacity) (fieldBound : field < cellWords)
    (pointer : state.registers .rax = layout.pointer index) :
    SafeTrace layout.region returns [.load .w64 destination (cellField field)] state holes
      (state.setReg destination (state.words (cellSlot index field))) holes :=
  SafeTrace.load _ _ _ _ _ _ _ (layout.cell_bound allocated fieldBound)
    (field_address layout state index pointer fieldBound) (access.reads _ (cellSlot_bound allocated fieldBound))

theorem clear_readable {holes : Stream.Holes} {address : Word} {count : Nat}
    (readable : Stream.ReadableData holes address count) : Stream.clearRange holes address count = holes := by
  funext candidate
  apply propext
  constructor
  · exact And.left
  · intro hidden
    refine ⟨hidden, ?_⟩
    rintro ⟨offset, bound, rfl⟩
    exact readable offset bound hidden

theorem store_header {layout : Layout} {state : State} {holes : Stream.Holes} {returns : List ReturnFrame}
    (based : Based layout state) (access : Access layout holes returns) (source : GPR)
    {field : Nat} (fieldBound : field < headerWords) :
    SafeTrace layout.region returns [.store .w64 (header field) source] state holes
      (state.setWord field (state.registers source)) holes := by
  have bound : field < heapWords := by simp only [heapWords]; omega
  simpa only [clear_readable (access.reads field bound)] using
    SafeTrace.store layout.region returns state holes (header field) source field
      (layout.header_bound fieldBound) (header_address based fieldBound)
      (access.writes field bound)

theorem store_field {layout : Layout} {state : State} {holes : Stream.Holes} {returns : List ReturnFrame}
    (access : Access layout holes returns) (source : GPR) {index field : Nat}
    (allocated : index < capacity) (fieldBound : field < cellWords)
    (pointer : state.registers .rax = layout.pointer index) :
    SafeTrace layout.region returns [.store .w64 (cellField field) source] state holes
      (state.setWord (cellSlot index field) (state.registers source)) holes := by
  have bound := cellSlot_bound allocated fieldBound
  simpa only [clear_readable (access.reads _ bound)] using
    SafeTrace.store layout.region returns state holes (cellField field) source (cellSlot index field)
      (layout.cell_bound allocated fieldBound)
      (field_address layout state index pointer fieldBound) (access.writes _ bound)

end Compilatrix.X86.HeapArena
