import Compilatrix.Rt.Rc.Proof.BumpIdle
import Compilatrix.Rt.Rc.Proof.BumpMetadata

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

theorem AllocatorReady.reserve_bump
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem external context base bump limit slots lists)
    {fields tag : Nat} (hpos : 0 < fields) (hsmall : fields < 32) (htag : tag ≤ maxTag)
    (hempty : lists (smallClass fields) = [])
    (hspace : bump.toNat+cellBytes fields ≤ limit.toNat) (clock : Nat) :
    let next := bump+UInt64.ofNat (cellBytes fields)
    let after := reserveBump mem context bump next fields tag
    eval (allocProgram fields tag) clock [] mem context = .ok ([bump], after) ∧
    AllocatorReady heap addresses after external context base next limit
      (bumpSlot bump fields :: slots) lists ∧
    WordAt after bump (dynamicHeader fields (smallClass fields) tag 1) := by
  let next := bump+UInt64.ofNat (cellBytes fields)
  have hb := h.idle.partition.bounds
  have hn : next.toNat = bump.toNat+cellBytes fields := addr_toNat (by omega)
  have hnlim : next.toNat ≤ limit.toNat := by omega
  have hc : 1 ≤ smallClass fields ∧ smallClass fields ≤ 32 := by
    simp only [smallClass]; omega
  have wh := h.idle.free_heads (smallClass fields) hc.1 hc.2
  rw [hempty] at wh
  have hh : loadWord mem .w64 .zero (headAddress context fields) = some 0 := by
    rw [headAddress_eq]
    simp [loadWord, wh.read64, truncate_w64]
  have hbu : loadWord mem .w64 .zero (bumpAddress context) = some bump := by
    simp [loadWord, h.bump_word.read64, truncate_w64]
  have hli : loadWord mem .w64 .zero (limitAddress context) = some limit := by
    simp [loadWord, h.limit_word.read64, truncate_w64]
  have hcarry : ¬ next < bump := by rw [UInt64.lt_iff_toNat_lt, hn]; omega
  have hfits : Cond.holds .ule .w64 next limit = true := by
    simp only [Cond.holds, truncate_w64, decide_eq_true_eq, UInt64.le_iff_toNat_le]
    exact hnlim
  have haccess : ∀ j < 8, mem.readable (bump+UInt64.ofNat j) = true ∧
      mem.writable (bump+UInt64.ofNat j) = true := by
    intro j hj
    have hbytes : 8 ≤ cellBytes fields := by simp [cellBytes]; omega
    have ha : (bump+UInt64.ofNat j).toNat = bump.toNat+j := addr_toNat (by omega)
    apply h.arena_access
    · rw [ha]; omega
    · rw [ha]; omega
  refine ⟨alloc_bump mem context bump limit fields tag clock hpos hsmall htag hh hbu hli
    hcarry hfits h.bump_writable (fun j hj => (haccess j hj).2),
    h.after_bump hn hnlim (h.bump_idle hpos hsmall hn hnlim), ?_⟩
  apply wordAt_write64
  simpa [X86.Memory.write] using (fun j hj => (haccess j hj).1)


end Compilatrix.Rt.Rc.Procs
