import Compilatrix.Rt.Rc.Proof.RecycleFrames

namespace Compilatrix.Rt.Rc.Procs
open Lir

theorem ReleaseInvariant.recycle_tail_frame
    {heap addresses mem external current top tail context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current (top :: tail)
      context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) (ha : parent.address = top.address)
    (oldHead : Word) {frame : CursorFrame} (hm : frame ∈ tail) :
    ObjectFrame mem (recycleParent mem context (UInt64.ofNat parent.cls) parent.address oldHead)
      frame.address (cellBytes frame.original.fields.length) := by
  obtain ⟨earlier, later, he⟩ := List.mem_iff_append.mp hm
  obtain ⟨slot, hs, had, hc, hk⟩ := h.cursors_placed (top :: earlier) frame later (by simp [he])
  have hn : top.address ∉ tail.map CursorFrame.address := by
    have hd := h.cursor_distinct
    simp only [List.map_cons, List.nodup_cons] at hd
    exact hd.1
  have hne : slot ≠ parent := by
    intro eq
    have heq : frame.address = top.address := had.symm.trans ((congrArg Slot.address eq).trans ha)
    apply hn
    exact List.mem_map.mpr ⟨frame, hm, heq⟩
  have hf := h.recycle_slot_frame hp hs hne oldHead
  simpa only [had, hc, cellBytes, smallClass, Nat.add_comm] using hf

theorem ReleaseInvariant.recycle_cursors
    {heap addresses mem external current top tail context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current (top :: tail)
      context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) (ha : parent.address = top.address)
    (oldHead : Word) :
    CursorChain addresses heap
      (recycleParent mem context (UInt64.ofNat parent.cls) parent.address oldHead) tail := by
  apply h.cursors.2.2.2.frame
  intro frame hm
  exact h.recycle_tail_frame hp ha oldHead hm



end Compilatrix.Rt.Rc.Procs
