import IxCC.Rt.Rc.Gen.Proof.RecyclePlacement
import IxCC.Rt.Rc.Gen.Proof.RecycleCursors
import IxCC.Rt.Rc.Gen.Proof.RecycleLive

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir
open IxCC.Own IxCC.Own.Rc

/-- Complete finished-parent invariant transition for the actual two-store
memory update. Its companion finished_parent_step supplies the real Lir path.
No operation simulation or postcondition is assumed. -/
theorem ReleaseInvariant.recycle_complete_details
    {heap addresses mem external top tail context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external none (top :: tail)
      context base bump limit slots lists)
    (hfinished : top.visited = top.original.ctor.nobj) :
    ∃ parent ∈ slots, parent.address = top.address ∧ parent.cls = classOf top.original.ctor ∧
      ReleaseInvariant cmax heap addresses
        (recycleParent mem context (UInt64.ofNat parent.cls) parent.address ((lists parent.cls).headD 0))
        external none tail context base bump limit (recycleSlots parent.address slots)
        (pushFree lists parent.cls parent.address) := by
  obtain ⟨parent, hp, ha, hc, hk⟩ := h.cursors_placed [] top tail (by rfl)
  have hcursor := h.cursors.2.1
  have hr : ∀ j < 8, mem.readable (parent.address+UInt64.ofNat j) = true := by
    intro j hj
    rw [ha]
    apply (h.cursor_access top (by simp) j ?_).1
    have := h.cursor_bytes (frame := top) (by simp)
    omega
  refine ⟨parent, hp, ha, hc, {
    balance := ?_
    live := h.recycle_live hp hk _
    partition := h.partition.recycle_pending hp hk
    cursors := h.recycle_cursors hp ha _
    cursor_distinct := ?_
    cursor_nonzero := ?_
    cursor_layout := ?_
    cursor_access := ?_
    cursor_class := ?_
    cursor_scan := ?_
    cursors_placed := ?_
    pending_exact := ?_
    free_exact := h.recycle_free_exact hp
    free_distinct := h.recycle_distinct hp (pending_ne_free hk)
    free_placed := ?_
    free_chains := h.recycle_chains hp (pending_ne_free hk) hr
    free_heads := ?_
    head_writable := ?_
    head_fit := h.head_fit
    context_fit := h.context_fit
    head_disjoint := ?_ }⟩
  · have hb : Balance heap external (top.suffix ++ cursorTokens tail) := by
      simpa [cursorTokens, flattenPending] using h.balance
    exact Balance.drop_scalars hb (hcursor.suffix_scalars hfinished)
  · have hd := h.cursor_distinct
    simp only [List.map_cons, List.nodup_cons] at hd
    exact hd.2
  · intro frame hm
    exact h.cursor_nonzero frame (by simp [hm])
  · intro frame hm
    exact h.cursor_layout frame (by simp [hm])
  · intro frame hm j hj
    simpa [recycleParent, X86.Memory.write] using h.cursor_access frame (by simp [hm]) j hj
  · intro frame hm
    have hf := h.recycle_tail_frame hp ha ((lists parent.cls).headD 0) hm
    have hb := hf.bytes_eq 1 (by have := h.cursor_bytes (frame := frame) (by simp [hm]); omega)
    have hbyte :
        (recycleParent mem context (UInt64.ofNat parent.cls) parent.address ((lists parent.cls).headD 0)).bytes
          (frame.address+1) = mem.bytes (frame.address+1) := by simpa using hb
    exact hbyte.trans (h.cursor_class frame (by simp [hm]))
  · intro frame hm
    have hf := h.recycle_tail_frame hp ha ((lists parent.cls).headD 0) hm
    have hb := hf.bytes_eq 0 (by have := h.cursor_bytes (frame := frame) (by simp [hm]); omega)
    have hbyte :
        (recycleParent mem context (UInt64.ofNat parent.cls) parent.address ((lists parent.cls).headD 0)).bytes
          frame.address = mem.bytes frame.address := by simpa using hb
    exact hbyte.trans (h.cursor_scan frame (by simp [hm]))
  · intro earlier frame later he
    exact h.recycle_cursors_placed hp ha earlier frame later he
  · simpa only [ha] using h.recycle_pending_exact
  · intro cls address hm
    exact h.recycle_free_placed hp (pending_ne_free hk) hm
  · intro cls hl hu
    exact h.recycle_heads hp ((lists parent.cls).headD 0) hl hu
  · intro cls hl hu j hj
    simpa [recycleParent, X86.Memory.write] using h.head_writable cls hl hu j hj
  · intro cls hl hu slot hm
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    have hs := h.head_disjoint cls hl hu old hold
    by_cases he : old.address = parent.address <;> simpa [he] using hs


end IxCC.Rt.Rc.Gen
