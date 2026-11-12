import IxCC.Rt.Rc.Gen.Proof.ReserveChains
import IxCC.Rt.Rc.Gen.Proof.ReserveHeads

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir

/-- Reserving a free cell leaves the logical heap and every external token
unchanged. The selected physical slot is reserved, never silently live. -/
theorem ReleaseInvariant.reserve_idle
    {heap addresses mem external context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external none [] context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) {tail : List Word}
    (hhead : lists target.cls = target.address :: tail)
    {L : CellLayout} {k : Nat} (hc : target.cls = k) :
    ReleaseInvariant cmax heap addresses (reserveFree mem context target.address (tail.headD 0) L k)
      external none [] context base bump limit (reserveSlots target.address slots)
      (popFree lists target.cls) := by
  have hk : target.kind = .free := (h.free_exact target ht).mpr (by rw [hhead]; simp)
  refine {
    balance := h.balance
    live := h.reserve_live (L := L) ht hk hc _
    partition := h.partition.reserve_free ht hk
    cursors := by trivial
    cursor_distinct := by simp
    cursor_nonzero := by simp
    cursor_layout := by simp
    cursor_access := by simp
    cursor_class := by simp
    cursor_scan := by simp
    cursors_placed := ?_
    pending_exact := ?_
    free_exact := h.reserve_free_exact ht hhead
    free_distinct := ?_
    free_placed := fun _ _ hm => h.reserve_free_placed ht hhead hm
    free_chains := h.reserve_chains (L := L) ht hhead hc
    free_heads := fun _ hl hu => h.reserve_heads (L := L) ht hhead hc hl hu
    head_writable := ?_
    head_fit := h.head_fit
    context_fit := h.context_fit
    head_disjoint := ?_ }
  · intro earlier frame later he
    have := congrArg List.length he
    simp at this
  · intro slot hm location suffix predecessor
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    have hp := h.pending_exact old hold location suffix predecessor
    by_cases he : old.address = target.address
    · simp [he]
    · simpa [he] using hp
  · intro cls
    by_cases he : cls = target.cls
    · simpa [popFree, he, List.Nodup] using (h.free_distinct cls).tail
    · simpa [popFree, he] using h.free_distinct cls
  · intro cls hl hu j hj
    simpa [reserveFree, X86.Memory.write] using h.head_writable cls hl hu j hj
  · intro cls hl hu slot hm
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    have hs := h.head_disjoint cls hl hu old hold
    by_cases he : old.address = target.address <;> simpa [he] using hs


end IxCC.Rt.Rc.Gen
