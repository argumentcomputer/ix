import IxCC.Rt.Rc.Proof.BumpFrames

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem AllocatorReady.limit_address_nat
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem external context base bump limit slots lists) :
    (limitAddress context).toNat = context.toNat-32 := by
  rw [limitAddress_eq, sub_toNat_of_le]
  · rfl
  · have := h.context_lower; simpa using (show 32 ≤ context.toNat by omega)

theorem AllocatorReady.after_bump
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem external context base bump limit slots lists)
    {fields tag : Nat} {next : Word} {slots' : List Slot}
    (hn : next.toNat = bump.toNat+cellBytes fields)
    (hspace : next.toNat ≤ limit.toNat)
    (hi : ReleaseInvariant heap addresses (reserveBump mem context bump next fields tag)
      external none [] context base next limit slots' lists) :
    AllocatorReady heap addresses (reserveBump mem context bump next fields tag)
      external context base next limit slots' lists := by
  have hb := h.idle.partition.bounds
  have hc := h.context_before
  have hl := h.context_lower
  have ha := h.bump_address_nat
  have hz := h.limit_address_nat
  have hbytes : 8 ≤ cellBytes fields := by simp [cellBytes]; omega
  have hbf : (bumpAddress context).toNat+8 ≤ 2^64 := by omega
  have hlf : (limitAddress context).toNat+8 ≤ 2^64 := by omega
  have hnew : bump.toNat+8 ≤ 2^64 := by omega
  refine {
    idle := hi
    context_lower := h.context_lower
    context_before := h.context_before
    bump_aligned := ?_
    bump_word := ?_
    limit_word := ?_
    bump_writable := ?_
    arena_access := ?_ }
  · rw [hn]
    simp [cellBytes, Nat.add_mod, Nat.mul_mod, h.bump_aligned]
  · have hw := wordAt_write64 (v := next) h.bump_word.readable
    exact hw.write_disjoint (w := .w64) (a := bump)
      (u := dynamicHeader fields (smallClass fields) tag 1)
      hnew hbf (Or.inl (by omega))
  · have hw := h.limit_word.write_disjoint (w := .w64) (a := bumpAddress context)
      (u := next) hbf hlf (Or.inr (by simp only [X86.Width.bytes]; omega))
    exact hw.write_disjoint (w := .w64) (a := bump)
      (u := dynamicHeader fields (smallClass fields) tag 1)
      hnew hlf (Or.inl (by omega))
  · simpa [reserveBump, X86.Memory.write] using h.bump_writable
  · simpa [reserveBump, X86.Memory.write] using h.arena_access



end IxCC.Rt.Rc.Procs
