import Compilatrix.Rt.Rc.Proof.AllocatorMetadata
import Compilatrix.Rt.Rc.Proof.AllocatorAccess
import Compilatrix.Rt.Rc.Proof.AdvanceFrames

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

theorem AllocatorReady.bump_address_nat
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem external context base bump limit slots lists) :
    (bumpAddress context).toNat = context.toNat-40 := by
  rw [bumpAddress_eq, sub_toNat_of_le]
  · rfl
  · simpa using h.context_lower

theorem AllocatorReady.bump_slot_frame
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem external context base bump limit slots lists)
    {slot : Slot} (hs : slot ∈ slots) {fields : Nat} (hpos : 0 < fields)
    (hspace : bump.toNat+cellBytes fields ≤ limit.toNat) (tag : Nat) (next : Word) :
    ObjectFrame mem (reserveBump mem context bump next fields tag) slot.address (8*slot.cls) := by
  have hv := h.idle.partition.valid slot hs
  have hb := h.idle.partition.bounds
  have hc := h.context_before
  have hl := h.context_lower
  have ha := h.bump_address_nat
  have hbytes : 8 ≤ cellBytes fields := by simp [cellBytes]; omega
  have hf : slot.address.toNat+8*slot.cls ≤ 2^64 := by omega
  have hcontrol : (bumpAddress context).toNat+8 ≤ 2^64 := by omega
  have hnew : bump.toNat+8 ≤ 2^64 := by omega
  have first := objectFrame_write mem slot.address (bumpAddress context) next
    _ .w64 hf hcontrol (Or.inr (by simp only [X86.Width.bytes]; omega))
  have last := objectFrame_write (mem.write .w64 (bumpAddress context) next)
    slot.address bump (dynamicHeader fields (smallClass fields) tag 1)
    _ .w64 hf hnew (Or.inl hv.2.2.2.2)
  exact first.trans last

theorem AllocatorReady.bump_live
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem external context base bump limit slots lists)
    {fields : Nat} (hpos : 0 < fields) (hspace : bump.toNat+cellBytes fields ≤ limit.toNat)
    (tag : Nat) (next : Word) :
    HeapLive heap addresses (reserveBump mem context bump next fields tag) := by
  apply h.idle.frame_live_slots
  intro slot hs loc hk
  exact h.bump_slot_frame hs hpos hspace tag next




end Compilatrix.Rt.Rc.Procs
