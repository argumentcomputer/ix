import IxCC.Rt.Rc.Gen.Proof.BumpIdle
import IxCC.Rt.Rc.Gen.Proof.BumpMetadata

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem AllocatorReady.reserve_bump
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady cmax heap addresses mem external context base bump limit slots lists)
    {L : CellLayout} {cls : Nat} (hL : L.ok = true) (hcl : L.cls? = some cls) (hcmax : cls ≤ cmax)
    (hempty : lists (cls) = [])
    (hspace : bump.toNat+(classBytes cls) ≤ limit.toNat) (clock : Nat) :
    let next := bump+UInt64.ofNat (classBytes cls)
    let after := reserveBump mem context bump next L cls
    eval (allocProgram L) clock [] mem context = .ok ([bump], after) ∧
    AllocatorReady cmax heap addresses after external context base next limit
      (bumpSlot bump cls :: slots) lists ∧
    WordAt after bump (dynamicHeader L.nobj cls L.tag 1) := by
  let next := bump+UInt64.ofNat (classBytes cls)
  have hb := h.idle.partition.bounds
  have hn : next.toNat = bump.toNat+(classBytes cls) := addr_toNat (by omega)
  have hnlim : next.toNat ≤ limit.toNat := by omega
  obtain ⟨hc2, hcm, hb16, hbytes, _⟩ := layout_class hL hcl
  have hc : 1 ≤ cls ∧ cls ≤ maxClass := ⟨by omega, hcm⟩
  have wh := h.idle.free_heads (cls) hc.1 hc.2
  rw [hempty] at wh
  have hh : loadWord mem .w64 .zero (headAddress context cls) = some 0 := by
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
    have ha : (bump+UInt64.ofNat j).toNat = bump.toNat+j := addr_toNat (by omega)
    apply h.arena_access
    · rw [ha]; omega
    · rw [ha]; omega
  refine ⟨alloc_bump mem context bump limit L cls clock hL hcl hh hbu hli
    hcarry hfits h.bump_writable (fun j hj => (haccess j hj).2),
    h.after_bump (by omega) hn hnlim (h.bump_idle (L := L) (by omega) hcm hcmax hn hnlim), ?_⟩
  apply wordAt_write64
  simpa [X86.Memory.write] using (fun j hj => (haccess j hj).1)


end IxCC.Rt.Rc.Gen
