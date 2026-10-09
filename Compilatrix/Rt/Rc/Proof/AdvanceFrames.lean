import Compilatrix.Rt.Rc.Proof.ReleaseInvariant
import Compilatrix.Rt.Rc.Proof.PartitionRecycle
import Compilatrix.Rt.Rc.Proof.ObjectFrame

namespace Compilatrix.Rt.Rc.Procs
open Lir

theorem ReleaseInvariant.advance_slot_frame
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent slot : Slot} (hp : parent ∈ slots) (hs : slot ∈ slots) (hne : slot ≠ parent)
    (remaining : Word) :
    ObjectFrame mem (resumeParent mem parent.address remaining) slot.address (8*slot.cls) := by
  have vp := h.partition.valid parent hp
  have vs := h.partition.valid slot hs
  have hb := h.partition.bounds
  have hd := h.partition.disjoint_members hs hp hne
  apply objectFrame_write mem slot.address parent.address (remaining-1) _ .w8
  · omega
  · simp only [X86.Width.bytes]; omega
  · simp only [X86.Width.bytes]
    rcases hd with hd | hd <;> omega

/-- A reusable byte-to-live-heap frame rule. The physical per-slot premise is
discharged by actual write separation in each runtime transition. -/
theorem ReleaseInvariant.frame_live_slots
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {after : X86.Memory}
    (hf : ∀ slot ∈ slots, ∀ location, slot.kind = .live location →
      ObjectFrame mem after slot.address (8*slot.cls)) :
    HeapLive heap addresses after := by
  refine { h.live with cell := ?_ }
  intro loc refs mode body hc
  obtain ⟨hmode, addr, haddr, hcell⟩ := h.live.cell loc refs mode body hc
  subst mode
  obtain ⟨slot, hm, hkind⟩ := h.partition.placed loc refs body hc
  obtain ⟨refs', body', hc', haddr', hclass⟩ := h.partition.live slot hm loc hkind
  rw [hc] at hc'
  have eqs : refs = refs' ∧ body = body' := by simpa using hc'
  have hbody : body' = body := eqs.2.symm
  subst body'
  have had : slot.address = addr := by
    rw [haddr] at haddr'
    exact (Option.some.inj haddr').symm
  refine ⟨rfl, addr, haddr, hcell.frame ?_⟩
  simpa only [had, hclass, cellBytes, smallClass, Nat.add_comm] using hf slot hm loc hkind

theorem ReleaseInvariant.advance_live
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {location suffix predecessor}
    (hk : parent.kind = .pending location suffix predecessor) (remaining : Word) :
    HeapLive heap addresses (resumeParent mem parent.address remaining) := by
  apply h.frame_live_slots
  intro slot hm loc hkind
  apply h.advance_slot_frame hp hm _ remaining
  intro he
  subst slot
  rw [hk] at hkind
  cases hkind




end Compilatrix.Rt.Rc.Procs
