import IxCC.Rt.Rc.Proof.LiveMemory
import IxCC.Rt.Rc.Proof.Memory
import IxCC.Rt.Proof.Words

/-! Preservation of the concrete live-cell representation by a physical
count update. This is a byte-memory theorem, not a presumed simulation. -/
namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem pack32 (value : Word) :
    value.toUInt8.toUInt64 ||| (value >>> 8).toUInt8.toUInt64 <<< 8 |||
      (value >>> 16).toUInt8.toUInt64 <<< 16 ||| (value >>> 24).toUInt8.toUInt64 <<< 24 =
        X86.Width.w32.truncate value := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hmask : (4294967295#64)[j] = decide (j < 32) := by
    rw [← BitVec.getLsbD_eq_getElem]
    change (BitVec.ofNat 64 (2^32-1)).getLsbD j = decide (j < 32)
    rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    simp only [hj, decide_true, Bool.true_and]
  simp only [X86.Width.truncate, X86.Width.mask,
    UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_toUInt8, UInt8.toBitVec_toUInt64, UInt64.toBitVec_ofNat,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_umod, BitVec.toNat_ofNat,
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth]
  have ranges : j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨
      (24 ≤ j ∧ j < 32) ∨ 32 ≤ j := by omega
  rcases ranges with h | h | h | h | h <;>
    simp (discharger := omega) [hmask, decide_eq_true, decide_eq_false]

theorem read32_write32 (mem : X86.Memory) (address value : Word) :
    (mem.write .w32 address value).read .w32 address = X86.Width.w32.truncate value := by
  change (mem.writeLittle address value 4).readLittle address 4 = _
  simp (discharger := omega) only [X86.Memory.readLittle, X86.Memory.writeLittle_bytes]
  simpa using pack32 value

theorem truncate32_small {value : Word} (h : value.toNat < 2^32) :
    X86.Width.w32.truncate value = value := by
  apply UInt64.toNat_inj.mp
  simp only [X86.Width.truncate, X86.Width.mask, UInt64.toNat_and]
  rw [show (UInt64.toNat 0xffffffff) = 2^32-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h

theorem LiveCell.update_count {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {refs : Nat} {body : Own.Body}
    (h : LiveCell addresses mem address refs body) (newRefs : Nat)
    (hp : 0 < newRefs) (hb : newRefs ≤ maxCount) :
    LiveCell addresses (storeCount mem address (UInt64.ofNat (newRefs-1))) address newRefs body := by
  have hfit : address.toNat + 8 ≤ 2^64 := by
    have hf := h.fit
    simp only [cellBytes] at hf
    omega
  have hframe := storeCount_frame mem address (UInt64.ofNat (newRefs-1)) hfit
  refine { h with
    positive := hp, bounded := hb, readable := ?_, writable := ?_
    header := ?_, count := ?_, fields := ?_ }
  · simpa [storeCount, X86.Memory.write] using h.readable
  · simpa [storeCount, X86.Memory.write] using h.writable
  · rw [← h.header]
    apply X86.Memory.readLittle_congr
    intro j hj
    apply hframe.outside
    left
    rw [addr_toNat (by simp only [X86.Width.bytes] at hj; omega)]
    simp only [X86.Width.bytes] at hj
    omega
  · unfold storeCount
    rw [read32_write32]
    apply truncate32_small
    rw [UInt64.toNat_ofNat']
    unfold maxCount at hb
    omega
  · intro j value hj
    obtain ⟨word, hv, hw⟩ := h.fields j value hj
    have hjbound : j < body.fields.length := (List.getElem?_eq_some_iff.mp hj).1
    have hf := h.fit
    simp only [cellBytes] at hf
    have ha : address.toNat + (8+8*j) < 2^64 := by omega
    refine ⟨word, hv, storeCount_word hw hfit ?_ ?_⟩
    · rw [addr_toNat ha]
      omega
    · right
      rw [addr_toNat ha]
      omega


end IxCC.Rt.Rc.Procs
