import Ix.Compiler.X86.Execution

/-! An aligned finite word region over the existing byte memory. This view is
used for scalar stack frames, including saved registers and return slots.
Every access has a concrete capacity and nonwrapping-address proof. -/

namespace Ix.Compiler.X86.WordRegion

structure Layout where
  base : Word
  slots : Nat
  aligned : base % 8 = 0
  fits : base.toNat + 8 * slots ≤ UInt64.size

def Layout.address (layout : Layout) (slot : Nat) : Word :=
  layout.base + UInt64.ofNat (8 * slot)

theorem Layout.address_toNat (layout : Layout) {slot : Nat} (bound : slot < layout.slots) :
    (layout.address slot).toNat = layout.base.toNat + 8 * slot := by
  have fits := layout.fits
  have small : layout.base.toNat + 8 * slot < UInt64.size := by omega
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
  have small : layout.base.toNat + 8 * slot + offset < UInt64.size := by omega
  rw [UInt64.toNat_add, layout.address_toNat slotBound, UInt64.toNat_ofNat_of_lt' (by omega)]
  exact Nat.mod_eq_of_lt small

def Layout.allowed (layout : Layout) (address : Word) : Bool :=
  decide (layout.base.toNat ≤ address.toNat ∧ address.toNat < layout.base.toNat + 8 * layout.slots)

theorem Layout.byteAllowed (layout : Layout) {slot offset : Nat}
    (slotBound : slot < layout.slots) (offsetBound : offset < 8) :
    layout.allowed (layout.address slot + UInt64.ofNat offset) = true := by
  simp only [Layout.allowed, decide_eq_true_eq, layout.byteAddress_toNat slotBound offsetBound]
  omega

theorem Layout.subtract (layout : Layout) {slot count : Nat} (enough : count ≤ slot) :
    layout.address slot - UInt64.ofNat (8 * count) = layout.address (slot - count) := by
  have split : 8 * slot = 8 * (slot - count) + 8 * count := by omega
  simp only [Layout.address]
  rw [split, UInt64.ofNat_add, ← UInt64.add_assoc, UInt64.add_sub_cancel]

theorem Layout.add (layout : Layout) (slot count : Nat) :
    layout.address slot + UInt64.ofNat (8 * count) = layout.address (slot + count) := by
  simp [Layout.address, Nat.mul_add, UInt64.ofNat_add, UInt64.add_assoc]

abbrev Words := Nat → Word

def Words.set (words : Words) (slot : Nat) (value : Word) : Words :=
  fun candidate => if candidate == slot then value else words candidate

@[simp] theorem Words.set_same (words : Words) (slot : Nat) (value : Word) :
    words.set slot value slot = value := by simp [Words.set]

@[simp] theorem Words.set_other (words : Words) (slot other : Nat) (value : Word)
    (different : other ≠ slot) : words.set slot value other = words other := by
  simp [Words.set, different]

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

/-- No initialization of scratch slots is required by the native interface:
the word view can be read from any sufficiently mapped initial byte memory. -/
theorem realizes_initial (layout : Layout) (memory : Memory)
    (readable : ∀ slot < layout.slots, Memory.rangeAllowed memory.readable (layout.address slot) 8 = true)
    (writable : ∀ slot < layout.slots, Memory.rangeAllowed memory.writable (layout.address slot) 8 = true) :
    Realizes layout memory (fun slot => memory.read64 (layout.address slot)) memory :=
  ⟨fun _ _ => rfl, readable, writable, fun _ _ => rfl⟩

end Ix.Compiler.X86.WordRegion
