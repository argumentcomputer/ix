import IxCC.Rt.Rc.Gen.Proof.AllocatorMetadata
import IxCC.Rt.Rc.Gen.Proof.AllocatorAccess
import IxCC.Rt.Rc.Gen.Proof.AdvanceFrames
import IxCC.Rt.Rc.Gen.Proof.AllocBump
import IxCC.Rt.Rc.Proof.BumpFrames

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem AllocatorReady.bump_address_nat
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady cmax heap addresses mem external context base bump limit slots lists) :
    (bumpAddress context).toNat = context.toNat-40 := by
  rw [bumpAddress_eq, sub_toNat_of_le]
  · rfl
  · simpa using h.context_lower

theorem AllocatorReady.bump_slot_frame
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady cmax heap addresses mem external context base bump limit slots lists)
    {slot : Slot} (hs : slot ∈ slots) {L : CellLayout} {cls : Nat} (hcls : 1 ≤ cls)
    (hspace : bump.toNat+classBytes cls ≤ limit.toNat) (next : Word) :
    ObjectFrame mem (reserveBump mem context bump next L cls) slot.address (8*classWords slot.cls) := by
  have hv := h.idle.partition.valid slot hs
  have hb := h.idle.partition.bounds
  have hc := h.context_before
  have hl := h.context_lower
  have ha := h.bump_address_nat
  have hbytes : 8 ≤ classBytes cls := by have := classWords_pos hcls; unfold classBytes; omega
  have hf : slot.address.toNat+8*classWords slot.cls ≤ 2^64 := by omega
  have hcontrol : (bumpAddress context).toNat+8 ≤ 2^64 := by omega
  have hnew : bump.toNat+8 ≤ 2^64 := by omega
  have first := objectFrame_write mem slot.address (bumpAddress context) next
    _ .w64 hf hcontrol (Or.inr (by simp only [X86.Width.bytes]; omega))
  have last := objectFrame_write (mem.write .w64 (bumpAddress context) next)
    slot.address bump (dynamicHeader L.nobj cls L.tag 1)
    _ .w64 hf hnew (Or.inl hv.2.2.2.2.1)
  exact first.trans last

theorem AllocatorReady.bump_live
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady cmax heap addresses mem external context base bump limit slots lists)
    {L : CellLayout} {cls : Nat} (hcls : 1 ≤ cls) (hspace : bump.toNat+classBytes cls ≤ limit.toNat)
    (next : Word) :
    HeapLive heap addresses (reserveBump mem context bump next L cls) := by
  apply h.idle.frame_live_slots
  intro slot hs loc hk
  exact h.bump_slot_frame (L := L) hs hcls hspace next

end IxCC.Rt.Rc.Gen
