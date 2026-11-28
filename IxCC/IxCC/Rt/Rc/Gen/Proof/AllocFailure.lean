import IxCC.Rt.Rc.Gen.Proof.AllocBump
import IxCC.Rt.Rc.Gen.Proof.AllocatorMetadata

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

/-- Exhausted bounded storage follows the actual cold heap-failure edge.
No header or allocator-control store is executed on this path. -/
theorem alloc_short (mem : X86.Memory) (context cell limit : Word) (L : CellLayout) (cls clock : Nat)
    (hL : L.ok = true) (hcl : L.cls? = some cls)
    (hhead : loadWord mem .w64 .zero (headAddress context cls) = some 0)
    (hbump : loadWord mem .w64 .zero (bumpAddress context) = some cell)
    (hlimit : loadWord mem .w64 .zero (limitAddress context) = some limit)
    (hcarry : ¬ cell+UInt64.ofNat (classBytes cls) < cell)
    (hfit : Cond.holds .ule .w64 (cell+UInt64.ofNat (classBytes cls)) limit = false) :
    eval (allocProgram L) clock [] mem context = .resource .heap := by
  let next := cell+UInt64.ofNat (classBytes cls)
  let e1 := bumpEnv cell limit
  let e2 := e1.insert 4 next
  have hc : e1[2]? = some cell := by simp only [e1, bumpEnv, Std.HashMap.getElem?_insert]; rfl
  have he : e2[3]? = some limit := by simp only [e2, e1, bumpEnv, Std.HashMap.getElem?_insert]; rfl
  apply (runs_eval (alloc_free_initial mem context L cls hL hcl)).eq
  have finish : Sem.Reaches (semStep (allocProgram L)) (allocState mem context e1 2 2)
      clock (.resource .heap) := by
    apply Sem.Reaches.free (s' := allocState mem context e2 3 0)
    · apply semStep_next.mpr
      simp [step, allocProgram, allocState, alloc_eq hL hcl, allocFunc, v, i, to,
        Arg.eval, Ovf.eval, evalArgs, takeEdge, bindParams, hc, hcarry, e2, next]
    apply Sem.Reaches.free (s' := allocState mem context e2 6 0)
    · apply semStep_next.mpr
      simp [step, allocProgram, allocState, alloc_eq hL hcl, allocFunc, v, to,
        Arg.eval, evalArgs, takeEdge, bindParams, he, e2, next, hfit]
    apply Sem.Reaches.final
    rw [show semStep (allocProgram L) (allocState mem context e2 6 0) = .fail .heap by
      apply semStep_fail.mpr
      simp [step, allocProgram, allocState, alloc_eq hL hcl, allocFunc]]
    exact .fail
  simpa [e1] using Sem.Reaches.star
    (alloc_bump_prefix mem context cell limit L cls hL hcl hhead hbump hlimit) finish



theorem AllocatorReady.reserve_short
    {heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady cmax heap addresses mem external context base bump limit slots lists)
    {L : CellLayout} {cls : Nat} (hL : L.ok = true) (hcl : L.cls? = some cls)
    (hempty : lists (cls) = [])
    (hshort : limit.toNat < bump.toNat+(classBytes cls)) (clock : Nat) :
    eval (allocProgram L) clock [] mem context = .resource .heap := by
  have hb := h.idle.partition.bounds
  obtain ⟨hc2, hcm, hb16, hbytes, _⟩ := layout_class hL hcl
  have hn : (bump+UInt64.ofNat (classBytes cls)).toNat = bump.toNat+(classBytes cls) :=
    addr_toNat (by omega)
  have wh := h.idle.free_heads cls (by omega) hcm
  rw [hempty] at wh
  apply alloc_short mem context bump limit L cls clock hL hcl
  · rw [headAddress_eq]
    simp [loadWord, wh.read64]
  · simp [loadWord, h.bump_word.read64]
  · simp [loadWord, h.limit_word.read64]
  · rw [UInt64.lt_iff_toNat_lt, hn]; omega
  · simp only [Cond.holds, truncate_w64, decide_eq_false_iff_not, UInt64.le_iff_toNat_le]
    omega


end IxCC.Rt.Rc.Gen
