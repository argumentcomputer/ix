import IxCC.Rt.Rc.Proof.CountHeap
import IxCC.Rt.Rc.Proof.PartitionCount
import IxCC.Rt.Rc.Proof.CountFree
import IxCC.Rt.Rc.Proof.RecycleFrames

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc

/-- Full current shared-reference transition: exact source count update,
actual count bytes, and all live/pending/free/context invariants. -/
theorem ReleaseInvariant.shared_complete
    {heap addresses mem external location frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external (some (.loc location)) frames
      context base bump limit slots lists)
    {rc body address} (hc : heap.cell? location = some (.live (rc+2) .dyn body))
    (ha : addresses location = some address) :
    ReleaseInvariant (setCell heap location (.live (rc+1) .dyn body)) addresses
      (storeCount mem address (UInt64.ofNat rc)) external none frames context base bump limit slots lists := by
  obtain ⟨_, a, ham, hcell⟩ := h.live.cell location (rc+2) .dyn body hc
  have heq : a = address := by rw [ha] at ham; exact (Option.some.inj ham).symm
  subst a
  obtain ⟨target, ht, hk⟩ := h.partition.placed location (rc+2) body hc
  obtain ⟨r, b, htarget, haddr, hclass⟩ := h.partition.live target ht location hk
  have had : target.address = address := by rw [ha] at haddr; exact (Option.some.inj haddr).symm
  have hbound : rc+1 ≤ maxCount := by have := hcell.bounded; omega
  have hframes : ∀ frame ∈ frames,
      ObjectFrame mem (storeCount mem address (UInt64.ofNat rc))
        frame.address (cellBytes frame.original.fields.length) := by
    intro frame hm
    simpa only [had] using h.count_cursor_frame ht hk (UInt64.ofNat rc) hm
  refine {
    balance := ?_
    live := ?_
    partition := h.partition.update_count hc (rc+1)
    cursors := ?_
    cursor_distinct := h.cursor_distinct
    cursor_nonzero := h.cursor_nonzero
    cursor_access := ?_
    cursor_class := ?_
    cursors_placed := h.cursors_placed
    pending_exact := h.pending_exact
    free_exact := h.free_exact
    free_distinct := h.free_distinct
    free_placed := h.free_placed
    free_chains := ?_
    free_heads := ?_
    head_writable := ?_
    head_fit := h.head_fit
    context_fit := h.context_fit
    head_disjoint := h.head_disjoint }
  · have hb : Balance heap external (.loc location :: cursorTokens frames) := by simpa using h.balance
    simpa using balance_shared hc hb
  · simpa using h.live.update_count hc ha (rc+1) (by omega) hbound
  · exact (h.cursors.update_count hc (rc+1)).frame hframes
  · intro frame hm j hj
    simpa [storeCount, X86.Memory.write] using h.cursor_access frame hm j hj
  · intro frame hm
    have hb := (hframes frame hm).bytes_eq 1 (by simp [cellBytes]; omega)
    have he : (storeCount mem address (UInt64.ofNat rc)).bytes (frame.address+1) =
        mem.bytes (frame.address+1) := by simpa using hb
    exact he.trans (h.cursor_class frame hm)
  · intro cls
    simpa only [had] using h.count_free_chains ht hk (UInt64.ofNat rc) cls
  · intro cls hl hu
    simpa only [had] using h.count_free_heads ht (UInt64.ofNat rc) hl hu
  · intro cls hl hu j hj
    simpa [storeCount, X86.Memory.write] using h.head_writable cls hl hu j hj


end IxCC.Rt.Rc.Procs
