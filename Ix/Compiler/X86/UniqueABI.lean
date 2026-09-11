import Ix.Compiler.X86.Memory

/-!
# Bounded unique-list arena ABI

The entry receives an eight-byte-aligned descriptor in `rdi`. Its ten words
contain a bump offset in bytes, capacity in bytes, and resource observations.
Four-word list cells follow immediately. Each cell stores a tag, scalar head,
tail pointer, and zero padding. Allocation, reservation, reuse, and release are
selected as ordinary x86 instructions; the caller supplies the bounded region.

Only the checked reversal schema uses this ABI. Tags have meaning relative to
that schema's complete constructor identities, retained by the compiler and
object provenance. This representation is not an open heap or extern ABI.
-/

namespace Ix.Compiler.X86.UniqueABI

def policyTag : String := "unique-list-arena/1"
def maxLength : Nat := 64
def headerWords : Nat := 10
def cellWords : Nat := 4
def headerBytes : Nat := 80
def cellBytes : Nat := 32

inductive Field where
  | cursor | capacity | allocs | frees | reuses | live | peak | rcops | payload | reservations
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Field.index : Field → Nat
  | .cursor => 0 | .capacity => 1 | .allocs => 2 | .frees => 3 | .reuses => 4
  | .live => 5 | .peak => 6 | .rcops => 7 | .payload => 8 | .reservations => 9

@[simp] theorem Field.index_lt (field : Field) : field.index < headerWords := by
  cases field <;> decide

def nilTag : Word := 0
def consTag : Word := 1
def reservedTag : Word := 2
def freedTag : Word := 3

structure Layout where
  base : Word
  capacity : Nat
  capacityBound : capacity ≤ maxLength + 2
  aligned : base % 8 = 0
  nonzero : base ≠ 0
  fits : base.toNat + headerBytes + cellBytes * capacity ≤ UInt64.size

def Layout.slots (layout : Layout) : Nat := headerWords + cellWords * layout.capacity
def Layout.address (layout : Layout) (slot : Nat) : Word := layout.base + UInt64.ofNat (8 * slot)
def cellSlot (index field : Nat) : Nat := headerWords + cellWords * index + field
def Layout.cell (layout : Layout) (index : Nat) : Word := layout.address (cellSlot index 0)

theorem Layout.address_toNat (layout : Layout) {slot : Nat} (bound : slot < layout.slots) :
    (layout.address slot).toNat = layout.base.toNat + 8 * slot := by
  have fits := layout.fits
  have small : layout.base.toNat + 8 * slot < UInt64.size := by
    simp only [Layout.slots, headerWords, cellWords] at bound
    simp only [headerBytes, cellBytes] at fits
    omega
  rw [Layout.address, UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega)]
  exact Nat.mod_eq_of_lt small

theorem Layout.address_aligned (layout : Layout) {slot : Nat} (bound : slot < layout.slots) :
    layout.address slot % 8 = 0 := by
  apply UInt64.toNat_inj.mp
  have aligned := congrArg UInt64.toNat layout.aligned
  simp only [UInt64.toNat_mod] at aligned ⊢
  change layout.base.toNat % 8 = 0 at aligned
  change (layout.address slot).toNat % 8 = 0
  rw [layout.address_toNat bound]
  omega

theorem Layout.address_injective (layout : Layout) {left right : Nat}
    (leftBound : left < layout.slots) (rightBound : right < layout.slots)
    (equal : layout.address left = layout.address right) : left = right := by
  have same := congrArg UInt64.toNat equal
  rw [layout.address_toNat leftBound, layout.address_toNat rightBound] at same
  omega

theorem Layout.byteAddress_toNat (layout : Layout) {slot offset : Nat}
    (slotBound : slot < layout.slots) (offsetBound : offset < 8) :
    (layout.address slot + UInt64.ofNat offset).toNat = layout.base.toNat + 8 * slot + offset := by
  have fits := layout.fits
  have small : layout.base.toNat + 8 * slot + offset < UInt64.size := by
    simp only [Layout.slots, headerWords, cellWords] at slotBound
    simp only [headerBytes, cellBytes] at fits
    omega
  rw [UInt64.toNat_add, layout.address_toNat slotBound, UInt64.toNat_ofNat_of_lt' (by omega)]
  exact Nat.mod_eq_of_lt small

def Layout.allowed (layout : Layout) (address : Word) : Bool :=
  decide (layout.base.toNat ≤ address.toNat ∧ address.toNat < layout.base.toNat + 8 * layout.slots)

theorem Layout.byteAllowed (layout : Layout) {slot offset : Nat}
    (slotBound : slot < layout.slots) (offsetBound : offset < 8) :
    layout.allowed (layout.address slot + UInt64.ofNat offset) = true := by
  simp only [Layout.allowed, decide_eq_true_eq, layout.byteAddress_toNat slotBound offsetBound]
  omega

abbrev Words := Nat → Word

def Words.set (words : Words) (slot : Nat) (value : Word) : Words :=
  fun candidate => if candidate == slot then value else words candidate

@[simp] theorem Words.set_same (words : Words) (slot : Nat) (value : Word) :
    words.set slot value slot = value := by simp [Words.set]

@[simp] theorem Words.set_other (words : Words) (slot other : Nat) (value : Word)
    (different : other ≠ slot) : words.set slot value other = words other := by
  simp [Words.set, different]

def initialWords (layout : Layout) : Words :=
  Words.set (fun _ => 0) Field.capacity.index (UInt64.ofNat (cellBytes * layout.capacity))

structure Realizes (layout : Layout) (outside : Memory) (words : Words) (memory : Memory) : Prop where
  view : ∀ slot < layout.slots, memory.read64 (layout.address slot) = words slot
  readable : ∀ slot < layout.slots, Memory.rangeAllowed memory.readable (layout.address slot) 8 = true
  writable : ∀ slot < layout.slots, Memory.rangeAllowed memory.writable (layout.address slot) 8 = true
  frame : ∀ address, layout.allowed address = false → memory.bytes address = outside.bytes address

theorem Realizes.write64 {layout : Layout} {outside memory : Memory} {words : Words}
    (represented : Realizes layout outside words memory) {slot : Nat} (bound : slot < layout.slots)
    (value : Word) :
    Realizes layout outside (words.set slot value) (memory.write64 (layout.address slot) value) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro other otherBound
    by_cases same : other = slot
    · subst other
      simp [Memory.read64_write64]
    · rw [Memory.read64_write64_ne _ _ _ _ (layout.address_aligned bound)
        (layout.address_aligned otherBound) (fun equal => same (layout.address_injective otherBound bound equal))]
      simp [represented.view other otherBound, same]
  · simpa using represented.readable
  · simpa using represented.writable
  · intro address notAllowed
    rw [Memory.write64_bytes_outside]
    · exact represented.frame address notAllowed
    · intro offset offsetBound same
      have allowed := layout.byteAllowed bound offsetBound
      rw [← same, notAllowed] at allowed
      contradiction

def fillWords (layout : Layout) (words : Words) (memory : Memory) : Nat → Memory
  | 0 => memory
  | count + 1 => (fillWords layout words memory count).write64 (layout.address count) (words count)

@[simp] theorem fillWords_readable (layout : Layout) (words : Words) (memory : Memory) (count : Nat) :
    (fillWords layout words memory count).readable = memory.readable := by
  induction count <;> simp [fillWords, *]

@[simp] theorem fillWords_writable (layout : Layout) (words : Words) (memory : Memory) (count : Nat) :
    (fillWords layout words memory count).writable = memory.writable := by
  induction count <;> simp [fillWords, *]

theorem fillWords_read (layout : Layout) (words : Words) (memory : Memory)
    {count slot : Nat} (countBound : count ≤ layout.slots) (slotBound : slot < count) :
    (fillWords layout words memory count).read64 (layout.address slot) = words slot := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [fillWords]
      by_cases same : slot = count
      · subst slot; exact Memory.read64_write64 _ _ _
      · rw [Memory.read64_write64_ne _ _ _ _ (layout.address_aligned (by omega))
          (layout.address_aligned (by omega)) (fun equal => same (layout.address_injective (by omega) (by omega) equal))]
        exact ih (by omega) (by omega)

theorem fillWords_frame (layout : Layout) (words : Words) (memory : Memory)
    {count : Nat} (countBound : count ≤ layout.slots) (address : Word)
    (notAllowed : layout.allowed address = false) :
    (fillWords layout words memory count).bytes address = memory.bytes address := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [fillWords, Memory.write64_bytes_outside]
      · exact ih (by omega)
      · intro offset offsetBound same
        have allowed := layout.byteAllowed (slot := count) (by omega) offsetBound
        rw [← same, notAllowed] at allowed
        contradiction

def initialMemory (layout : Layout) (outside : Memory) : Memory :=
  fillWords layout (initialWords layout)
    { outside with
      readable := fun address => layout.allowed address || outside.readable address
      writable := fun address => layout.allowed address || outside.writable address }
    layout.slots

theorem initialMemory_realizes (layout : Layout) (outside : Memory) :
    Realizes layout outside (initialWords layout) (initialMemory layout outside) := by
  refine ⟨fun slot bound => fillWords_read _ _ _ (by omega) bound, ?_, ?_, ?_⟩
  · intro slot bound
    simp only [initialMemory, fillWords_readable]
    apply Memory.rangeAllowed_of_forall
    intro offset offsetBound
    simp [layout.byteAllowed bound offsetBound]
  · intro slot bound
    simp only [initialMemory, fillWords_writable]
    apply Memory.rangeAllowed_of_forall
    intro offset offsetBound
    simp [layout.byteAllowed bound offsetBound]
  · intro address notAllowed
    exact fillWords_frame _ _ _ (by omega) address notAllowed

end Ix.Compiler.X86.UniqueABI
