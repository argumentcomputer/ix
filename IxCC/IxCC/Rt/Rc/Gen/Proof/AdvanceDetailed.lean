import IxCC.Rt.Rc.Gen.Proof.AdvanceCursorPlacement
import IxCC.Rt.Rc.Gen.Proof.AdvanceCursors
import IxCC.Rt.Rc.Gen.Proof.AdvancePlacement
import IxCC.Rt.Rc.Gen.Proof.AdvanceFree

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir
open IxCC.Own IxCC.Own.Rc

/-- Complete next-child invariant transition under the actual scan-byte
write. The independently proved resume_step supplies its real Lir path. -/
theorem ReleaseInvariant.advance_complete_details
    {heap addresses mem external top tail context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external none (top :: tail)
      context base bump limit slots lists)
    (hv : top.visited < top.original.ctor.nobj)
    (hlen : top.visited < top.original.fields.length) :
    ∃ parent ∈ slots, parent.address = top.address ∧ parent.cls = classOf top.original.ctor ∧
      ReleaseInvariant cmax heap addresses
        (resumeParent mem parent.address (UInt64.ofNat (top.original.ctor.nobj-top.visited)))
        external (some top.original.fields[top.visited]) (advanceFrame top :: tail)
        context base bump limit
        (advanceSlots parent.address top.location (advanceFrame top).suffix (cursorHead tail) slots) lists := by
  obtain ⟨parent, hp, ha, hc, hk⟩ := h.cursors_placed [] top tail (by rfl)
  refine ⟨parent, hp, ha, hc, {
    balance := ?_
    live := h.advance_live hp hk _
    partition := h.partition.advance_pending hp hk _
    cursors := h.advance_cursors hp ha hv
    cursor_distinct := ?_
    cursor_nonzero := ?_
    cursor_layout := ?_
    cursor_access := ?_
    cursor_class := ?_
    cursor_scan := ?_
    cursors_placed := h.advance_cursors_placed hp ha hc
    pending_exact := h.advance_pending_exact hp ha hc
    free_exact := h.advance_free_exact hp hk _
    free_distinct := h.free_distinct
    free_placed := ?_
    free_chains := h.advance_chains hp hk _
    free_heads := ?_
    head_writable := ?_
    head_fit := h.head_fit
    context_fit := h.context_fit
    head_disjoint := ?_ }⟩
  · have hb : Balance heap external (cursorTokens (top :: tail)) := by simpa using h.balance
    rw [cursorTokens_advance top tail hlen] at hb
    simpa using hb
  · simpa only [List.map_cons, advanceFrame] using h.cursor_distinct
  · intro frame hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h.cursor_nonzero top (by simp)
    · exact h.cursor_nonzero frame (by simp [hm])
  · intro frame hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h.cursor_layout top (by simp)
    · exact h.cursor_layout frame (by simp [hm])
  · intro frame hm j hj
    rcases List.mem_cons.mp hm with rfl | hm
    · simpa [resumeParent, storeCount, X86.Memory.write, advanceFrame] using h.cursor_access top (by simp) j hj
    · simpa [resumeParent, storeCount, X86.Memory.write] using h.cursor_access frame (by simp [hm]) j hj
  · intro frame hm
    rcases List.mem_cons.mp hm with rfl | hm
    · have hn := h.cursors.2.1.advance hv h.cursors.2.2.1
      have hb := (hn.header_low 1 (by decide)).trans
        (h.cursors.2.1.header_low 1 (by decide)).symm
      have hc0 := h.cursor_class top (by simp)
      have he :
          (resumeParent mem top.address (UInt64.ofNat (top.original.ctor.nobj-top.visited))).bytes
            (top.address+1) = mem.bytes (top.address+1) := by simpa using hb
      simpa only [ha, advanceFrame] using he.trans hc0
    · have hf := h.advance_tail_frame hp ha (UInt64.ofNat (top.original.ctor.nobj-top.visited)) hm
      have hb := hf.bytes_eq 1 (by have := h.cursor_bytes (frame := frame) (by simp [hm]); omega)
      have he :
          (resumeParent mem parent.address (UInt64.ofNat (top.original.ctor.nobj-top.visited))).bytes
            (frame.address+1) = mem.bytes (frame.address+1) := by simpa using hb
      exact he.trans (h.cursor_class frame (by simp [hm]))
  · intro frame hm
    rcases List.mem_cons.mp hm with rfl | hm
    · have hn := h.cursors.2.1.advance hv h.cursors.2.2.1
      have hb := (hn.header_low 0 (by decide)).trans
        (h.cursors.2.1.header_low 0 (by decide)).symm
      have hc0 := h.cursor_scan top (by simp)
      have he :
          (resumeParent mem top.address (UInt64.ofNat (top.original.ctor.nobj-top.visited))).bytes
            top.address = mem.bytes top.address := by simpa using hb
      simpa only [ha, advanceFrame] using he.trans hc0
    · have hf := h.advance_tail_frame hp ha (UInt64.ofNat (top.original.ctor.nobj-top.visited)) hm
      have hb := hf.bytes_eq 0 (by have := h.cursor_bytes (frame := frame) (by simp [hm]); omega)
      have he :
          (resumeParent mem parent.address (UInt64.ofNat (top.original.ctor.nobj-top.visited))).bytes
            frame.address = mem.bytes frame.address := by simpa using hb
      exact he.trans (h.cursor_scan frame (by simp [hm]))
  · intro cls address hm
    exact h.advance_free_placed hp hk _ hm
  · intro cls hl hu
    exact h.advance_heads hp _ hl hu
  · intro cls hl hu j hj
    simpa [resumeParent, storeCount, X86.Memory.write] using h.head_writable cls hl hu j hj
  · intro cls hl hu slot hm
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    have hs := h.head_disjoint cls hl hu old hold
    by_cases he : old.address = parent.address <;> simpa [he] using hs


end IxCC.Rt.Rc.Gen
