import Compilatrix.Rt.Rc.Proof.AllocatorMetadata
import Compilatrix.Rt.Rc.Proof.ReserveLists
import Compilatrix.Rt.Rc.Proof.AdvanceFrames
import Compilatrix.Rt.Rc.Proof.ProtectedOps

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

theorem ReleaseInvariant.reserve_slot_frame
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {target slot : Slot} (ht : target ∈ slots) (hs : slot ∈ slots) (hne : slot ≠ target)
    {fields : Nat} (hc : target.cls = smallClass fields) (tag : Nat) (next : Word) :
    ObjectFrame mem (reserveFree mem context target.address next fields tag) slot.address (8*slot.cls) := by
  have vt := h.partition.valid target ht
  have vs := h.partition.valid slot hs
  have hb := h.partition.bounds
  have hd := h.partition.disjoint_members hs ht hne
  have hh := h.head_disjoint target.cls vt.1 vt.2.1 slot hs
  have hfit : slot.address.toNat+8*slot.cls ≤ 2^64 := by omega
  have htfit : target.address.toNat+8 ≤ 2^64 := by omega
  have hsep : slot.address.toNat+8*slot.cls ≤ target.address.toNat ∨ target.address.toNat+8 ≤ slot.address.toNat := by
    rcases hd with hd | hd <;> omega
  have first := objectFrame_write mem slot.address (freeHeadAddress context (UInt64.ofNat target.cls)) next
    _ .w64 hfit (h.head_fit target.cls vt.1 vt.2.1) hh.symm
  have last := objectFrame_write (mem.write .w64 (headAddress context fields) next)
    slot.address target.address (dynamicHeader fields (smallClass fields) tag 1) _ .w64 hfit htfit hsep
  apply ObjectFrame.trans (b := mem.write .w64 (headAddress context fields) next)
  · simpa only [headAddress_eq, hc] using first
  · exact last

theorem ReleaseInvariant.reserve_live
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) (hk : target.kind = .free)
    {fields : Nat} (hc : target.cls = smallClass fields) (tag : Nat) (next : Word) :
    HeapLive heap addresses (reserveFree mem context target.address next fields tag) := by
  apply h.frame_live_slots
  intro slot hs loc hkind
  apply h.reserve_slot_frame ht hs _ hc tag next
  intro eq
  subst slot
  rw [hk] at hkind
  cases hkind

theorem ReleaseInvariant.reserve_protected
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots)
    {fields : Nat} (hc : target.cls = smallClass fields) (tag : Nat) (next : Word) :
    ProtectedFrame mem (reserveFree mem context target.address next fields tag) context base bump := by
  have vt := h.partition.valid target ht
  apply ProtectedFrame.trans (middle := mem.write .w64 (headAddress context fields) next)
  · simpa only [headAddress_eq, hc] using h.head_store_frame mem vt.1 vt.2.1 next
  · simpa [reserveFree] using h.object_store_frame ht (mem.write .w64 (headAddress context fields) next) 0 .w64
      (dynamicHeader fields (smallClass fields) tag 1) (by simp [X86.Width.bytes]; omega)




end Compilatrix.Rt.Rc.Procs
