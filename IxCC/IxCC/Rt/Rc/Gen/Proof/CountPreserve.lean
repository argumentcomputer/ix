import IxCC.Rt.Rc.Gen.Proof.LiveMemory
import IxCC.Rt.Rc.Proof.CountPreserve

/-! Preservation of a live cell of any layout by a physical count update. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir

theorem LiveCell.update_count {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {refs : Nat} {body : Own.Body}
    (h : LiveCell addresses mem address refs body) (newRefs : Nat)
    (hp : 0 < newRefs) (hb : newRefs ≤ maxCount) :
    LiveCell addresses (storeCount mem address (UInt64.ofNat (newRefs-1))) address newRefs body := by
  have hbytes := h.bytes
  have hf := h.fit
  have hfit : address.toNat + 8 ≤ 2^64 := by omega
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
    have ha : address.toNat + (8+8*j) < 2^64 := by omega
    refine ⟨word, hv, storeCount_word hw hfit ?_ ?_⟩
    · rw [addr_toNat ha]
      omega
    · right
      rw [addr_toNat ha]
      omega

end IxCC.Rt.Rc.Gen
