import IxCC.Own.Rc.Proof.Allocation
import IxCC.Rt.Rc.Proof.SharedInvariant

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc

/-- One retained reference updates actual count bytes and the external-root
balance, preserving the complete idle live/free/region representation. -/
theorem ReleaseInvariant.increment_idle
    {heap addresses mem external context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists)
    {location refs body address} (hc : heap.cell? location = some (.live refs .dyn body))
    (ha : addresses location = some address) (hroom : refs < maxCount) :
    ReleaseInvariant (setCell heap location (.live (refs+1) .dyn body)) addresses
      (storeCount mem address (UInt64.ofNat refs))
      (fun k => external k + refsIn k [.loc location]) none [] context base bump limit slots lists := by
  obtain ⟨_, a, ham, cell⟩ := h.live.cell location refs .dyn body hc
  have heq : a = address := by rw [ha] at ham; exact (Option.some.inj ham).symm
  subst a
  obtain ⟨target, ht, hk⟩ := h.partition.placed location refs body hc
  obtain ⟨r, b, htarget, haddr, hclass⟩ := h.partition.live target ht location hk
  have had : target.address = address := by rw [ha] at haddr; exact (Option.some.inj haddr).symm
  refine {
    balance := ?_
    live := ?_
    partition := h.partition.update_count hc (refs+1)
    cursors := by trivial
    cursor_distinct := h.cursor_distinct
    cursor_nonzero := h.cursor_nonzero
    cursor_access := by intro frame hm; simp at hm
    cursor_class := by intro frame hm; simp at hm
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
  · have hb : Balance heap external [] := by simpa [cursorTokens, flattenPending] using h.balance
    have hb' := balance_inc_cell hc hb
    intro k
    simpa [cursorTokens, flattenPending, refsIn, Nat.add_assoc] using hb' k
  · simpa using h.live.update_count hc ha (refs+1) (by omega) (by omega)
  · intro cls
    simpa only [had] using h.count_free_chains ht hk (UInt64.ofNat refs) cls
  · intro cls hl hu
    simpa only [had] using h.count_free_heads ht (UInt64.ofNat refs) hl hu
  · intro cls hl hu j hj
    simpa [storeCount, X86.Memory.write] using h.head_writable cls hl hu j hj


end IxCC.Rt.Rc.Procs
