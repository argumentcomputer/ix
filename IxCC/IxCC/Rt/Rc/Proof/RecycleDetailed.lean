import IxCC.Rt.Rc.Proof.RecyclePlacement
import IxCC.Rt.Rc.Proof.RecycleCursors
import IxCC.Rt.Rc.Proof.RecycleLive

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc

/-- Complete finished-parent invariant transition for the actual two-store
memory update. Its companion finished_parent_step supplies the real Lir path.
No operation simulation or postcondition is assumed. -/
theorem ReleaseInvariant.recycle_complete_details
    {heap addresses mem external top tail context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external none (top :: tail)
      context base bump limit slots lists)
    (hfinished : top.visited = top.original.fields.length) :
    ∃ parent ∈ slots, parent.address = top.address ∧ parent.cls = smallClass top.original.fields.length ∧
      ReleaseInvariant heap addresses
        (recycleParent mem context (UInt64.ofNat parent.cls) parent.address ((lists parent.cls).headD 0))
        external none tail context base bump limit (recycleSlots parent.address slots)
        (pushFree lists parent.cls parent.address) := by
  obtain ⟨parent, hp, ha, hc, hk⟩ := h.cursors_placed [] top tail (by rfl)
  have hcursor := h.cursors.2.1
  have hr : ∀ j < 8, mem.readable (parent.address+UInt64.ofNat j) = true := by
    intro j hj
    rw [ha]
    apply (h.cursor_access top (by simp) j ?_).1
    have := hcursor.visited_positive
    have := hcursor.visited_le
    simp only [cellBytes]
    omega
  refine ⟨parent, hp, ha, hc, {
    balance := ?_
    live := h.recycle_live hp hk _
    partition := h.partition.recycle_pending hp hk
    cursors := h.recycle_cursors hp ha _
    cursor_distinct := ?_
    cursor_nonzero := ?_
    cursor_access := ?_
    cursor_class := ?_
    cursors_placed := ?_
    pending_exact := ?_
    free_exact := h.recycle_free_exact hp
    free_distinct := h.recycle_distinct hp hk
    free_placed := ?_
    free_chains := h.recycle_chains hp hk hr
    free_heads := ?_
    head_writable := ?_
    head_fit := h.head_fit
    context_fit := h.context_fit
    head_disjoint := ?_ }⟩
  · simpa [cursorTokens, CursorFrame.suffix, flattenPending, hfinished] using h.balance
  · have hd := h.cursor_distinct
    simp only [List.map_cons, List.nodup_cons] at hd
    exact hd.2
  · intro frame hm
    exact h.cursor_nonzero frame (by simp [hm])
  · intro frame hm j hj
    simpa [recycleParent, X86.Memory.write] using h.cursor_access frame (by simp [hm]) j hj
  · intro frame hm
    have hf := h.recycle_tail_frame hp ha ((lists parent.cls).headD 0) hm
    have hb := hf.bytes_eq 1 (by simp [cellBytes]; omega)
    have hbyte :
        (recycleParent mem context (UInt64.ofNat parent.cls) parent.address ((lists parent.cls).headD 0)).bytes
          (frame.address+1) = mem.bytes (frame.address+1) := by simpa using hb
    exact hbyte.trans (h.cursor_class frame (by simp [hm]))
  · intro earlier frame later he
    exact h.recycle_cursors_placed hp ha earlier frame later he
  · simpa only [ha] using h.recycle_pending_exact
  · intro cls address hm
    exact h.recycle_free_placed hp hk hm
  · intro cls hl hu
    exact h.recycle_heads hp ((lists parent.cls).headD 0) hl hu
  · intro cls hl hu j hj
    simpa [recycleParent, X86.Memory.write] using h.head_writable cls hl hu j hj
  · intro cls hl hu slot hm
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    have hs := h.head_disjoint cls hl hu old hold
    by_cases he : old.address = parent.address <;> simpa [he] using hs


end IxCC.Rt.Rc.Procs
