import Compilatrix.Rt.Rc.Proof.LiveMemory

/-! Unique-parent detachment, first physical invariant. The first child is
read before payload field0 is replaced with the predecessor link. The suffix
still owns pending references; no live heap edge may count them again. -/
namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

def detachParent (mem : X86.Memory) (address predecessor : Word) (fields : Nat) : X86.Memory :=
  (mem.write .w64 (address+8) predecessor).write .w8 address (UInt64.ofNat (fields-1))

/-- Concrete state after detaching field0. This is a pending/reserved cell,
not LiveCell: the old child reference in field0 is replaced by metadata. -/
structure PendingParent (addresses : AddressMap) (before mem : X86.Memory)
    (address predecessor : Word) (original : Own.Body) : Prop where
  nonempty : 0 < original.fields.length
  small : original.fields.length < 32
  remaining : mem.bytes address = (UInt64.ofNat (original.fields.length-1)).toUInt8
  link : WordAt mem (address+8) predecessor
  header_tail : ∀ j, 0 < j → j < 8 →
    mem.bytes (address+UInt64.ofNat j) = before.bytes (address+UInt64.ofNat j)
  readable : mem.readable = before.readable
  writable : mem.writable = before.writable
  suffix : ∀ j value, original.fields[j]? = some value → 0 < j →
    ∃ word, valueWord addresses value = some word ∧
      WordAt mem (address + UInt64.ofNat (8+8*j)) word

theorem field0_address (address : Word) (j : Nat) :
    (address+8)+UInt64.ofNat j = address+UInt64.ofNat (8+j) := by
  rw [UInt64.ofNat_add]
  simp [UInt64.add_assoc]

/-- The child transferred to the current-value register is the actual first
field of the source cell, not a fresh or guessed word. -/
theorem LiveCell.first_child {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {refs : Nat} {body : Own.Body}
    (h : LiveCell addresses mem address refs body) {child : Own.RVal}
    (hc : body.fields[0]? = some child) :
    ∃ word, valueWord addresses child = some word ∧
      loadWord mem .w64 .zero (address+8) = some word := by
  obtain ⟨word, hv, hw⟩ := h.fields 0 child hc
  refine ⟨word, hv, ?_⟩
  have hr : mem.read? .w64 (address+8) = .ok word := by simpa using hw.read64
  simp [loadWord, hr]

theorem LiveCell.detach_pending {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {body : Own.Body}
    (h : LiveCell addresses mem address 1 body) (predecessor : Word) :
    PendingParent addresses mem (detachParent mem address predecessor body.fields.length)
      address predecessor body := by
  have hp := h.fields_positive
  have hf := h.fit
  simp only [cellBytes] at hf
  have ha8 : (address+8).toNat = address.toNat+8 := by
    exact addr_toNat (a := address) (i := 8) (by omega)
  have hread : ∀ j < 8, mem.readable ((address+8)+UInt64.ofNat j) = true := by
    intro j hj
    rw [field0_address]
    apply h.readable
    simp only [cellBytes]
    omega
  refine {
    nonempty := hp, small := h.fields_small, remaining := ?_, link := ?_
    header_tail := ?_, readable := ?_, writable := ?_, suffix := ?_ }
  · simp [detachParent, X86.Memory.write, X86.Width.bytes,
      X86.Memory.writeLittle, X86.Memory.writeByte]
  · apply (wordAt_write64 hread).write_disjoint
    · simp only [X86.Width.bytes]; omega
    · rw [ha8]; omega
    · right; simp only [X86.Width.bytes]; rw [ha8]; omega
  · intro j hj hbound
    have haj : (address + UInt64.ofNat j).toNat = address.toNat+j := addr_toNat (by omega)
    unfold detachParent X86.Memory.write
    simp only [X86.Width.bytes]
    rw [writeLittle_bytes_out (a := address) (by decide : 1 ≤ 8) (by omega)
      (by right; rw [haj]; omega)]
    exact writeLittle_bytes_out (by decide : 8 ≤ 8) (by rw [ha8]; omega)
      (by left; rw [ha8, haj]; omega)
  · simp [detachParent, X86.Memory.write]
  · simp [detachParent, X86.Memory.write]
  · intro j value hj hpos
    obtain ⟨word, hv, hw⟩ := h.fields j value hj
    have hjbound := (List.getElem?_eq_some_iff.mp hj).1
    have haj : (address + UInt64.ofNat (8+8*j)).toNat = address.toNat+(8+8*j) :=
      addr_toNat (by omega)
    refine ⟨word, hv, ?_⟩
    apply (hw.write_disjoint (w := .w64) (a := address+8) (u := predecessor)
      (by simp only [X86.Width.bytes]; rw [ha8]; omega)
      (by rw [haj]; omega)
      (by right; simp only [X86.Width.bytes]; rw [ha8, haj]; omega)).write_disjoint
    · simp only [X86.Width.bytes]; omega
    · rw [haj]; omega
    · right; simp only [X86.Width.bytes]; rw [haj]; omega



end Compilatrix.Rt.Rc.Procs
