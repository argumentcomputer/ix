import IxCC.Rt.Rc.Proof.AdvanceFrames
import IxCC.Rt.Rc.Proof.RecycleFrames
import IxCC.Rt.Rc.Proof.ResumeStep

namespace IxCC.Rt.Rc.Procs
open Lir

theorem ReleaseInvariant.advance_tail_frame
    {heap addresses mem external current top tail context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current (top :: tail)
      context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) (ha : parent.address = top.address)
    (remaining : Word) {frame : CursorFrame} (hm : frame ∈ tail) :
    ObjectFrame mem (resumeParent mem parent.address remaining)
      frame.address (cellBytes frame.original.fields.length) := by
  obtain ⟨earlier, later, he⟩ := List.mem_iff_append.mp hm
  obtain ⟨slot, hs, had, hc, hk⟩ := h.cursors_placed (top :: earlier) frame later (by simp [he])
  have hn : top.address ∉ tail.map CursorFrame.address := by
    have hd := h.cursor_distinct
    simp only [List.map_cons, List.nodup_cons] at hd
    exact hd.1
  have hne : slot ≠ parent := by
    intro eq
    apply hn
    exact List.mem_map.mpr ⟨frame, hm, had.symm.trans ((congrArg Slot.address eq).trans ha)⟩
  have hf := h.advance_slot_frame hp hs hne remaining
  simpa only [had, hc, cellBytes, smallClass, Nat.add_comm] using hf

theorem ReleaseInvariant.advance_cursors
    {heap addresses mem external current top tail context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current (top :: tail)
      context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) (ha : parent.address = top.address)
    (hv : top.visited < top.original.fields.length) :
    CursorChain addresses heap
      (resumeParent mem parent.address (UInt64.ofNat (top.original.fields.length-top.visited)))
      (advanceFrame top :: tail) := by
  refine ⟨h.cursors.1, ?_, h.cursors.2.2.1, ?_⟩
  · simpa only [ha, advanceFrame] using h.cursors.2.1.advance hv h.cursors.2.2.1
  · apply h.cursors.2.2.2.frame
    intro frame hm
    exact h.advance_tail_frame hp ha _ hm



end IxCC.Rt.Rc.Procs
