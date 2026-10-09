import Compilatrix.Rt.Rc.Proof.ReserveChains
import Compilatrix.Rt.Rc.Proof.ReserveHeads

namespace Compilatrix.Rt.Rc.Procs
open Lir

/-- Reserving a free cell leaves the logical heap and every external token
unchanged. The selected physical slot is reserved, never silently live. -/
theorem ReleaseInvariant.reserve_idle
    {heap addresses mem external context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists)
    {target : Slot} (ht : target ∈ slots) {tail : List Word}
    (hhead : lists target.cls = target.address :: tail)
    {fields : Nat} (hc : target.cls = smallClass fields) (tag : Nat) :
    ReleaseInvariant heap addresses (reserveFree mem context target.address (tail.headD 0) fields tag)
      external none [] context base bump limit (reserveSlots target.address slots)
      (popFree lists target.cls) := by
  have hk : target.kind = .free := (h.free_exact target ht).mpr (by rw [hhead]; simp)
  refine {
    balance := h.balance
    live := h.reserve_live ht hk hc tag _
    partition := h.partition.reserve_free ht hk
    cursors := by trivial
    cursor_distinct := by simp
    cursor_nonzero := by simp
    cursor_access := by simp
    cursor_class := by simp
    cursors_placed := ?_
    pending_exact := ?_
    free_exact := h.reserve_free_exact ht hhead
    free_distinct := ?_
    free_placed := fun _ _ hm => h.reserve_free_placed ht hhead hm
    free_chains := h.reserve_chains ht hhead hc tag
    free_heads := fun _ hl hu => h.reserve_heads ht hhead hc tag hl hu
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


end Compilatrix.Rt.Rc.Procs
