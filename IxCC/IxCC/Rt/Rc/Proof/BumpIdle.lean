import IxCC.Rt.Rc.Proof.BumpPartition
import IxCC.Rt.Rc.Proof.BumpLists

namespace IxCC.Rt.Rc.Procs
open Lir

theorem AllocatorReady.bump_not_free
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem external context base bump limit slots lists)
    (cls : Nat) : bump ∉ lists cls := by
  intro hm
  obtain ⟨slot, hs, ha, hc, hk⟩ := h.idle.free_placed cls bump hm
  have hv := h.idle.partition.valid slot hs
  rw [ha] at hv
  omega

theorem AllocatorReady.bump_idle
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem external context base bump limit slots lists)
    {fields tag : Nat} (hpos : 0 < fields) (hsmall : fields < 32) {next : Word}
    (hn : next.toNat = bump.toNat+cellBytes fields) (hspace : next.toNat ≤ limit.toNat) :
    ReleaseInvariant heap addresses (reserveBump mem context bump next fields tag)
      external none [] context base next limit (bumpSlot bump fields :: slots) lists := by
  have hfit : bump.toNat+cellBytes fields ≤ limit.toNat := by omega
  refine {
    balance := h.idle.balance
    live := h.bump_live hpos hfit tag next
    partition := h.idle.partition.reserve_bump hsmall h.bump_aligned ?_ hspace
    cursors := by trivial
    cursor_distinct := by simp
    cursor_nonzero := by simp
    cursor_access := by simp
    cursor_class := by simp
    cursors_placed := ?_
    pending_exact := ?_
    free_exact := ?_
    free_distinct := h.idle.free_distinct
    free_placed := ?_
    free_chains := h.bump_chains hpos hfit tag next
    free_heads := fun _ hl hu => h.bump_heads hfit tag next hl hu
    head_writable := ?_
    head_fit := h.idle.head_fit
    context_fit := h.idle.context_fit
    head_disjoint := ?_ }
  · simpa [cellBytes, smallClass, Nat.add_comm] using hn
  · intro earlier frame later he
    have := congrArg List.length he
    simp at this
  · intro slot hm loc suffix pred
    rcases List.mem_cons.mp hm with he | hm
    · subst slot; simp [bumpSlot]
    · exact h.idle.pending_exact slot hm loc suffix pred
  · intro slot hm
    rcases List.mem_cons.mp hm with he | hm
    · subst slot; simp [bumpSlot, h.bump_not_free]
    · exact h.idle.free_exact slot hm
  · intro cls address hm
    obtain ⟨slot, hs, ha, hc, hk⟩ := h.idle.free_placed cls address hm
    exact ⟨slot, by simp [hs], ha, hc, hk⟩
  · simpa [reserveBump, X86.Memory.write] using h.idle.head_writable
  · intro cls hl hu slot hm
    rcases List.mem_cons.mp hm with he | hm
    · subst slot
      have hh := freeHead_toNat h.idle.context_fit hu
      have hc := h.context_before
      have hb := h.idle.partition.bounds
      exact Or.inl (by simp only [bumpSlot]; omega)
    · exact h.idle.head_disjoint cls hl hu slot hm



end IxCC.Rt.Rc.Procs
