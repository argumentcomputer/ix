import IxCC.Rt.Rc.Gen.Proof.LiveMemory
import IxCC.Rt.Rc.Proof.CountPreserve
import IxCC.Rt.Rc.Proof.Pending

/-! Unique-parent detachment for cells of any layout. The first child is read before field 0 is
replaced with the predecessor link; the countdown of scanned fields still to visit goes into the
dead cell's count word, so the header's low half (scan count, class, tag) is kept. Only the
scanned suffix is pending; the scalar words are never read as children. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

def detachParent (mem : X86.Memory) (address predecessor : Word) (scan : Nat) : X86.Memory :=
  storeCount (mem.write .w64 (address+8) predecessor) address (UInt64.ofNat (scan-1))

/-- Concrete state after detaching field 0: a pending cell, not a live one. -/
structure PendingParent (addresses : AddressMap) (before mem : X86.Memory)
    (address predecessor : Word) (original : Own.Body) : Prop where
  nonempty : 0 < original.ctor.nobj
  layout : (layoutOf original.ctor).ok = true
  arity : original.fields.length = original.ctor.nobj + original.ctor.nscalar
  scalars : ∀ j value, original.fields[j]? = some value → original.ctor.nobj ≤ j →
    ∃ n, value = .lit (.nat n)
  remaining : mem.read .w32 (address+4) = UInt64.ofNat (original.ctor.nobj-1)
  link : WordAt mem (address+8) predecessor
  header_low : ∀ j < 4,
    mem.bytes (address+UInt64.ofNat j) = before.bytes (address+UInt64.ofNat j)
  readable : mem.readable = before.readable
  writable : mem.writable = before.writable
  suffix : ∀ j value, original.fields[j]? = some value → 0 < j → j < original.ctor.nobj →
    ∃ word, valueWord addresses value = some word ∧
      WordAt mem (address + UInt64.ofNat (8+8*j)) word

/-- The child transferred to the current-value register is the actual first field of the cell. -/
theorem LiveCell.first_child {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {refs : Nat} {body : Own.Body}
    (h : LiveCell addresses mem address refs body) (hn : 0 < body.ctor.nobj) {child : Own.RVal}
    (hc : body.fields[0]? = some child) :
    ∃ word, valueWord addresses child = some word ∧
      loadWord mem .w64 .zero (address+8) = some word := by
  obtain ⟨word, hv, hw⟩ := h.scanned hc hn
  refine ⟨word, hv, ?_⟩
  have hr : mem.read? .w64 (address+8) = .ok word := by simpa using hw.read64
  simp [loadWord, hr]

theorem LiveCell.detach_pending {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {body : Own.Body}
    (h : LiveCell addresses mem address 1 body) (hn : 0 < body.ctor.nobj) (predecessor : Word) :
    PendingParent addresses mem (detachParent mem address predecessor body.ctor.nobj)
      address predecessor body := by
  have hb := h.bytes
  have hf := h.fit
  have ha8 : (address+8).toNat = address.toNat+8 := addr_toNat (a := address) (i := 8) (by omega)
  have hfit : address.toNat + 8 ≤ 2^64 := by omega
  have hread : ∀ j < 8, mem.readable ((address+8)+UInt64.ofNat j) = true := by
    intro j hj
    rw [field0_address]
    apply h.readable
    omega
  have hscan := h.nobj_le
  refine {
    nonempty := hn, layout := h.layout, arity := h.arity, scalars := h.scalar_values, remaining := ?_, link := ?_
    header_low := ?_, readable := ?_, writable := ?_, suffix := ?_ }
  · unfold detachParent storeCount
    rw [read32_write32]
    apply truncate32_small
    rw [UInt64.toNat_ofNat']
    unfold maxFields at hscan
    omega
  · apply storeCount_word (wordAt_write64 hread) hfit (by omega)
    rw [ha8]; omega
  · intro j hj
    have haj : (address + UInt64.ofNat j).toNat = address.toNat+j := addr_toNat (by omega)
    unfold detachParent
    rw [(storeCount_frame _ address _ hfit).outside _ (by left; rw [haj]; omega)]
    unfold X86.Memory.write
    simp only [X86.Width.bytes]
    exact writeLittle_bytes_out (by decide : 8 ≤ 8) (by rw [ha8]; omega)
      (by left; rw [ha8, haj]; omega)
  · simp [detachParent, storeCount, X86.Memory.write]
  · simp [detachParent, storeCount, X86.Memory.write]
  · intro j value hj hpos hs
    obtain ⟨word, hv, hw⟩ := h.scanned hj hs
    have hjbound := (List.getElem?_eq_some_iff.mp hj).1
    have haj : (address + UInt64.ofNat (8+8*j)).toNat = address.toNat+(8+8*j) :=
      addr_toNat (by omega)
    refine ⟨word, hv, ?_⟩
    apply storeCount_word ?_ hfit (by rw [haj]; omega) (by right; rw [haj]; omega)
    apply hw.write_disjoint (w := .w64) (a := address+8) (u := predecessor)
      (by simp only [X86.Width.bytes]; rw [ha8]; omega)
      (by rw [haj]; omega)
      (by right; simp only [X86.Width.bytes]; rw [ha8, haj]; omega)

end IxCC.Rt.Rc.Gen
