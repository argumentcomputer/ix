import IxCC.Rt.Rc.Gen.Proof.BumpPartition
import IxCC.Rt.Rc.Gen.Proof.BumpLists

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir

theorem AllocatorReady.bump_not_free
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady cmax heap addresses mem external context base bump limit slots lists)
    (cls : Nat) : bump ∉ lists cls := by
  intro hm
  obtain ⟨slot, hs, ha, hc, hk⟩ := h.idle.free_placed cls bump hm
  have hv := h.idle.partition.valid slot hs
  rw [ha] at hv
  omega

theorem AllocatorReady.bump_idle
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady cmax heap addresses mem external context base bump limit slots lists)
    {L : CellLayout} {cls : Nat} (hcls : 1 ≤ cls) (hmax : cls ≤ maxClass) (hcm : cls ≤ cmax)
    {next : Word}
    (hn : next.toNat = bump.toNat+(classBytes cls)) (hspace : next.toNat ≤ limit.toNat) :
    ReleaseInvariant cmax heap addresses (reserveBump mem context bump next L cls)
      external none [] context base next limit (bumpSlot bump cls :: slots) lists := by
  have hfit : bump.toNat+(classBytes cls) ≤ limit.toNat := by omega
  refine {
    balance := h.idle.balance
    live := h.bump_live (L := L) hcls hfit next
    partition := h.idle.partition.reserve_bump hcls hmax hcm h.bump_aligned ?_ hspace
    cursors := by trivial
    cursor_distinct := by simp
    cursor_nonzero := by simp
    cursor_layout := by simp
    cursor_access := by simp
    cursor_class := by simp
    cursor_scan := by simp
    cursors_placed := ?_
    pending_exact := ?_
    free_exact := ?_
    free_distinct := h.idle.free_distinct
    free_placed := ?_
    free_chains := h.bump_chains (L := L) hcls hfit next
    free_heads := fun _ hl hu => h.bump_heads (L := L) hcls hfit next hl hu
    head_writable := ?_
    head_fit := h.idle.head_fit
    context_fit := h.idle.context_fit
    head_disjoint := ?_ }
  · simpa [classBytes] using hn
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



end IxCC.Rt.Rc.Gen
