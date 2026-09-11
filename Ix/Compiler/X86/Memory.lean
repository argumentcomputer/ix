import Ix.Compiler.X86.Eval

/-! Word-access laws for the existing little-endian byte-memory semantics.
The native heap selector uses aligned 64-bit fields. These lemmas keep its
word-level invariant connected to the actual byte loads and stores. -/

namespace Ix.Compiler.X86.Memory

@[simp] theorem write64_readable (memory : Memory) (address value : Word) :
    (memory.write64 address value).readable = memory.readable := by
  rfl

@[simp] theorem write64_writable (memory : Memory) (address value : Word) :
    (memory.write64 address value).writable = memory.writable := by
  rfl

private theorem byteOffset_injective (address : Word) {left right : Nat}
    (leftBound : left < 8) (rightBound : right < 8)
    (equal : address + UInt64.ofNat left = address + UInt64.ofNat right) :
    left = right := by
  have equal := congrArg UInt64.toNat equal
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at equal
  omega

private theorem aligned_bytes_disjoint (left right : Word)
    (leftAligned : left % 8 = 0) (rightAligned : right % 8 = 0) (different : left ≠ right)
    {i j : Nat} (iBound : i < 8) (jBound : j < 8) :
    left + UInt64.ofNat i ≠ right + UInt64.ofNat j := by
  intro equal
  have equal := congrArg UInt64.toNat equal
  have leftAligned := congrArg UInt64.toNat leftAligned
  have rightAligned := congrArg UInt64.toNat rightAligned
  have leftSmall := left.toNat_lt_size
  have rightSmall := right.toNat_lt_size
  have different : left.toNat ≠ right.toNat := fun equal => different (UInt64.toNat_inj.mp equal)
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_mod] at equal leftAligned rightAligned
  change left.toNat % 8 = 0 at leftAligned
  change right.toNat % 8 = 0 at rightAligned
  simp only [UInt64.size] at leftSmall rightSmall
  omega

theorem writeLittle_bytes (memory : Memory) (address value : Word) {count offset : Nat}
    (countBound : count ≤ 8) (offsetBound : offset < count) :
    (memory.writeLittle address value count).bytes (address + UInt64.ofNat offset) =
      (value >>> UInt64.ofNat (8 * offset)).toUInt8 := by
  induction count with
  | zero => omega
  | succ count ih =>
      by_cases same : offset = count
      · subst offset; simp [writeLittle, writeByte]
      · have different : address + UInt64.ofNat offset ≠ address + UInt64.ofNat count :=
          fun equal => same (byteOffset_injective address (by omega) (by omega) equal)
        simp only [writeLittle, writeByte, beq_iff_eq, if_neg different]
        exact ih (by omega) (by omega)

/-- Reconstruct a word from its eight little-endian bytes. The proof inspects
bit positions with kernel-checked arithmetic; no native decision axiom is used. -/
theorem pack64 (value : Word) :
    value.toUInt8.toUInt64 ||| (value >>> 8).toUInt8.toUInt64 <<< 8 |||
      (value >>> 16).toUInt8.toUInt64 <<< 16 ||| (value >>> 24).toUInt8.toUInt64 <<< 24 |||
      (value >>> 32).toUInt8.toUInt64 <<< 32 ||| (value >>> 40).toUInt8.toUInt64 <<< 40 |||
      (value >>> 48).toUInt8.toUInt64 <<< 48 ||| (value >>> 56).toUInt8.toUInt64 <<< 56 = value := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_toUInt8, UInt8.toBitVec_toUInt64, UInt64.toBitVec_ofNat,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_umod, BitVec.toNat_ofNat,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  have ranges : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨
      (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨
      (48 ≤ i ∧ i < 56) ∨ (56 ≤ i ∧ i < 64) := by omega
  rcases ranges with h | h | h | h | h | h | h | h <;>
    simp (discharger := omega) [decide_eq_true, decide_eq_false]

theorem read64_write64 (memory : Memory) (address value : Word) :
    (memory.write64 address value).read64 address = value := by
  change (memory.writeLittle address value 8).readLittle address 8 = value
  simp (discharger := omega) only [readLittle, writeLittle_bytes]
  simpa using pack64 value

theorem readLittle_congr (left right : Memory) (address : Word) (count : Nat)
    (equal : ∀ offset < count, left.bytes (address + UInt64.ofNat offset) =
      right.bytes (address + UInt64.ofNat offset)) :
    left.readLittle address count = right.readLittle address count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [readLittle, readLittle, ih (fun offset bound => equal offset (by omega)), equal count (by omega)]

theorem rangeAllowed_of_forall (permission : Word → Bool) (address : Word)
    (count : Nat) (allowed : ∀ offset < count, permission (address + UInt64.ofNat offset) = true) :
    rangeAllowed permission address count = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [rangeAllowed, Bool.and_eq_true]
      exact ⟨ih (fun offset bound => allowed offset (by omega)), allowed count (by omega)⟩

theorem writeLittle_bytes_outside (memory : Memory) (address value other : Word) (count : Nat)
    (outside : ∀ offset < count, other ≠ address + UInt64.ofNat offset) :
    (memory.writeLittle address value count).bytes other = memory.bytes other := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [writeLittle, writeByte, beq_iff_eq, if_neg (outside count (by omega))]
      exact ih (fun offset bound => outside offset (by omega))

theorem write64_bytes_outside (memory : Memory) (address value other : Word)
    (outside : ∀ offset < 8, other ≠ address + UInt64.ofNat offset) :
    (memory.write64 address value).bytes other = memory.bytes other :=
  writeLittle_bytes_outside memory address value other 8 outside

theorem read64_write64_ne (memory : Memory) (address other value : Word)
    (addressAligned : address % 8 = 0) (otherAligned : other % 8 = 0)
    (different : other ≠ address) :
    (memory.write64 address value).read64 other = memory.read64 other := by
  apply readLittle_congr
  intro i iBound
  apply write64_bytes_outside
  intro j jBound
  exact aligned_bytes_disjoint other address otherAligned addressAligned different iBound jBound

end Ix.Compiler.X86.Memory

namespace Ix.Compiler.X86

theorem word_add_left_comm (left middle right : Word) : left + (middle + right) = middle + (left + right) := by
  rw [← UInt64.add_assoc, UInt64.add_comm left middle, UInt64.add_assoc]

@[simp] theorem Registers.set_same (registers : Registers) (register : GPR) (value : Word) :
    (registers.set register value) register = value := by simp [Registers.set]

@[simp] theorem Registers.set_other (registers : Registers) (register other : GPR) (value : Word)
    (different : other ≠ register) : (registers.set register value) other = registers other := by
  simp [Registers.set, different]

@[simp] theorem Registers.set_set (registers : Registers) (register : GPR) (first second : Word) :
    (registers.set register first).set register second = registers.set register second := by
  funext candidate
  by_cases same : candidate = register <;> simp [Registers.set, same]

end Ix.Compiler.X86
