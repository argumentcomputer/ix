import IxCC.Rt.Rc.Gen.Proof.AllocatorReady

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem AllocatorReady.slot_access
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady cmax heap addresses mem external context base bump limit slots lists)
    {slot : Slot} (hs : slot ∈ slots) {j : Nat} (hj : j < 8*classWords slot.cls) :
    mem.readable (slot.address+UInt64.ofNat j) = true ∧
      mem.writable (slot.address+UInt64.ofNat j) = true := by
  have hv := h.idle.partition.valid slot hs
  have hb := h.idle.partition.bounds
  have ha : (slot.address+UInt64.ofNat j).toNat = slot.address.toNat+j :=
    addr_toNat (by omega)
  apply h.arena_access
  · rw [ha]; omega
  · rw [ha]; omega

theorem AllocatorReady.slot_nonzero
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady cmax heap addresses mem external context base bump limit slots lists)
    {slot : Slot} (hs : slot ∈ slots) : slot.address ≠ 0 := by
  have hv := h.idle.partition.valid slot hs
  have hc := h.context_before
  intro he
  have hz : slot.address.toNat = 0 := by rw [he]; rfl
  omega



end IxCC.Rt.Rc.Gen
