import IxCC.Rt.Rc.Proof.ProtectedFrame

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc

theorem ReleaseInvariant.count_protected
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {location refs body address} (hc : heap.cell? location = some (.live refs .dyn body))
    (ha : addresses location = some address) (count : Word) :
    ProtectedFrame mem (storeCount mem address count) context base bump := by
  obtain ⟨slot, hm, hk⟩ := h.partition.placed location refs body hc
  obtain ⟨r, b, hc', had, hcls⟩ := h.partition.live slot hm location hk
  have he : slot.address = address := by rw [ha] at had; exact (Option.some.inj had).symm
  have hv := h.partition.valid slot hm
  simpa [storeCount, he] using h.object_store_frame hm mem 4 .w32 count (by simp [X86.Width.bytes]; omega)

theorem ReleaseInvariant.detach_protected
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {location refs body address} (hc : heap.cell? location = some (.live refs .dyn body))
    (ha : addresses location = some address) (predecessor : Word) :
    ProtectedFrame mem (detachParent mem address predecessor body.fields.length) context base bump := by
  obtain ⟨slot, hm, hk⟩ := h.partition.placed location refs body hc
  obtain ⟨r, b, hc', had, hcls⟩ := h.partition.live slot hm location hk
  have he : slot.address = address := by rw [ha] at had; exact (Option.some.inj had).symm
  rw [hc] at hc'
  have hbody : b = body := by cases hc'; rfl
  subst b
  obtain ⟨_, a, ham, cell⟩ := h.live.cell location refs .dyn body hc
  have hclass : 2 ≤ slot.cls := by rw [hcls]; have := cell.fields_positive; simp only [smallClass]; omega
  have first := h.object_store_frame hm mem 8 .w64 predecessor (by simp [X86.Width.bytes]; omega)
  have last := h.object_store_frame hm (mem.write .w64 (address+8) predecessor) 0 .w8
    (UInt64.ofNat (body.fields.length-1)) (by simp [X86.Width.bytes]; omega)
  apply ProtectedFrame.trans (middle := mem.write .w64 (address+8) predecessor)
  · simpa [he] using first
  · simpa [he, detachParent] using last

theorem ReleaseInvariant.advance_protected
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {slot : Slot} (hm : slot ∈ slots) (remaining : Word) :
    ProtectedFrame mem (resumeParent mem slot.address remaining) context base bump := by
  have hv := h.partition.valid slot hm
  simpa [resumeParent] using h.object_store_frame hm mem 0 .w8 (remaining-1)
    (by simp [X86.Width.bytes]; omega)

theorem ReleaseInvariant.recycle_protected
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {slot : Slot} (hm : slot ∈ slots) (oldHead : Word) :
    ProtectedFrame mem (recycleParent mem context (UInt64.ofNat slot.cls) slot.address oldHead)
      context base bump := by
  have hv := h.partition.valid slot hm
  apply ProtectedFrame.trans (middle := mem.write .w64 slot.address oldHead)
  · simpa using h.object_store_frame hm mem 0 .w64 oldHead (by simp [X86.Width.bytes]; omega)
  · exact h.head_store_frame _ hv.1 hv.2.1 slot.address





end IxCC.Rt.Rc.Procs
