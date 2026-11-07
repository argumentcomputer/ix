import IxCC.Rt.Rc.Proof.AllocBump
import IxCC.Rt.Rc.Proof.AllocatorMetadata

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

/-- Exhausted bounded storage follows the actual cold heap-failure edge.
No header or allocator-control store is executed on this path. -/
theorem alloc_short (mem : X86.Memory) (context cell limit : Word) (fields tag clock : Nat)
    (hpos : 0 < fields) (hsmall : fields < 32) (htag : tag ≤ maxTag)
    (hhead : loadWord mem .w64 .zero (headAddress context fields) = some 0)
    (hbump : loadWord mem .w64 .zero (bumpAddress context) = some cell)
    (hlimit : loadWord mem .w64 .zero (limitAddress context) = some limit)
    (hcarry : ¬ cell+UInt64.ofNat (cellBytes fields) < cell)
    (hfit : Cond.holds .ule .w64 (cell+UInt64.ofNat (cellBytes fields)) limit = false) :
    eval (allocProgram fields tag) clock [] mem context = .resource .heap := by
  have hz : fields ≠ 0 := by omega
  have hl : ¬ 32 ≤ fields := Nat.not_le.mpr hsmall
  have ht : ¬ maxTag < tag := Nat.not_lt.mpr htag
  let next := cell+UInt64.ofNat (cellBytes fields)
  let e1 := bumpEnv cell limit
  let e2 := e1.insert 4 next
  have hc : e1[2]? = some cell := by simp only [e1, bumpEnv, Std.HashMap.getElem?_insert]; rfl
  have he : e2[3]? = some limit := by simp only [e2, e1, bumpEnv, Std.HashMap.getElem?_insert]; rfl
  apply (runs_eval (alloc_free_initial mem context fields tag hpos hsmall htag)).eq
  have finish : Sem.Reaches (semStep (allocProgram fields tag)) (allocState mem context e1 2 2)
      clock (.resource .heap) := by
    apply Sem.Reaches.free (s' := allocState mem context e2 3 0)
    · apply semStep_next.mpr
      simp [step, allocProgram, allocState, alloc, hz, hl, ht, v, i, to,
        Arg.eval, Ovf.eval, evalArgs, takeEdge, bindParams, hc, hcarry, e2, next]
    apply Sem.Reaches.free (s' := allocState mem context e2 6 0)
    · apply semStep_next.mpr
      simp [step, allocProgram, allocState, alloc, hz, hl, ht, v, to,
        Arg.eval, evalArgs, takeEdge, bindParams, he, e2, next, hfit]
    apply Sem.Reaches.final
    rw [show semStep (allocProgram fields tag) (allocState mem context e2 6 0) = .fail .heap by
      apply semStep_fail.mpr
      simp [step, allocProgram, allocState, alloc, hz, hl, ht]]
    exact .fail
  simpa [e1] using Sem.Reaches.star
    (alloc_bump_prefix mem context cell limit fields tag hpos hsmall htag hhead hbump hlimit) finish



theorem AllocatorReady.reserve_short
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady heap addresses mem external context base bump limit slots lists)
    {fields tag : Nat} (hpos : 0 < fields) (hsmall : fields < 32) (htag : tag ≤ maxTag)
    (hempty : lists (smallClass fields) = [])
    (hshort : limit.toNat < bump.toNat+cellBytes fields) (clock : Nat) :
    eval (allocProgram fields tag) clock [] mem context = .resource .heap := by
  have hb := h.idle.partition.bounds
  have hbytes : cellBytes fields ≤ 256 := by simp only [cellBytes]; omega
  have hn : (bump+UInt64.ofNat (cellBytes fields)).toNat = bump.toNat+cellBytes fields :=
    addr_toNat (by omega)
  have hc : 1 ≤ smallClass fields ∧ smallClass fields ≤ 32 := by
    simp only [smallClass]; omega
  have wh := h.idle.free_heads (smallClass fields) hc.1 hc.2
  rw [hempty] at wh
  apply alloc_short mem context bump limit fields tag clock hpos hsmall htag
  · rw [headAddress_eq]
    simp [loadWord, wh.read64]
  · simp [loadWord, h.bump_word.read64]
  · simp [loadWord, h.limit_word.read64]
  · rw [UInt64.lt_iff_toNat_lt, hn]; omega
  · simp only [Cond.holds, truncate_w64, decide_eq_false_iff_not, UInt64.le_iff_toNat_le]
    omega


end IxCC.Rt.Rc.Procs
