import IxCC.Rt.Rc.Proof.InitHeads

namespace IxCC.Rt.Rc.Procs.Init
open IxCC.Rt IxCC.Rt.Proof IxCC.Lir
open IxCC.X86 (Memory)

/-- Empty physical partition and exact zero ownership, from concrete initialized
control words, permission bytes, and class-head words. -/
theorem empty_ready {T : Lower.Tables} {ctx base limit : Word} {m : Memory}
    (hh : HeapAt T [] { cells := #[] } ctx m base limit)
    (heads : ∀ cls, 1 ≤ cls → cls ≤ 32 →
      WordAt m (freeHeadAddress ctx (UInt64.ofNat cls)) 0)
    (writable : ∀ cls, 1 ≤ cls → cls ≤ 32 → ∀ j < 8,
      m.writable (freeHeadAddress ctx (UInt64.ofNat cls)+UInt64.ofNat j) = true) :
    AllocatorReady { cells := #[] } (fun _ => none) m (fun _ => 0)
      ctx base base limit [] (fun _ => []) := by
  have hfit : ctx.toNat+576 < 2^64 := by
    have := hh.start; have := hh.bumpLe; have := hh.limitLt; omega
  refine {
    idle := {
      balance := ?_
      live := ?_
      partition := ?_
      cursors := trivial
      cursor_distinct := by simp
      cursor_nonzero := by simp
      cursor_access := by simp
      cursor_class := by simp
      cursors_placed := by simp
      pending_exact := by simp
      free_exact := by simp
      free_distinct := by simp
      free_placed := by simp
      free_chains := fun _ => trivial
      free_heads := heads
      head_writable := writable
      head_fit := ?_
      context_fit := by have := hh.start; have := hh.bumpLe; have := hh.limitLt; omega
      head_disjoint := by simp }
    context_lower := by have := hh.ctxLo; omega
    context_before := by have := hh.start; omega
    bump_aligned := hh.bumpAligned
    bump_word := by rw [bumpAddress_eq]; exact hh.bumpWord
    limit_word := by rw [limitAddress_eq]; exact hh.limitWord
    bump_writable := by rw [bumpAddress_eq]; exact hh.bumpWritable
    arena_access := ?_ }
  · intro l
    simp [Own.Rc.dynCount, Own.Heap.cell?, cursorTokens, flattenPending,
      Own.Rc.refsIn, Own.Rc.edgeCount, Own.Rc.total]
  · exact {
      cell := by intros; simp_all [Own.Heap.cell?]
      fields_live := by intros; simp_all [Own.Heap.cell?]
      disjoint := by intros; simp_all [Own.Heap.cell?] }
  · exact {
      bounds := ⟨Nat.le_refl _, hh.bumpLe, hh.limitLt⟩
      valid := by simp
      disjoint := by simp
      accounted := by intros; omega
      live := by simp
      placed := by intros; simp_all [Own.Heap.cell?]
      pending := by simp }
  · intro cls hc hc'
    rw [head_nat hfit (by omega)]
    omega
  · intro a hlo hhi
    simpa using hh.free a.toNat hlo hhi

/-- The actual cx_init execution establishes the complete empty allocator
invariant directly from its physical region and permissions. -/
theorem cxInit_ready {q : Program} {g : FunId}
    (hq : q.funcs[g]? = some Procs.cxInit) (hmain : q.main = g)
    {size budget ctx : Word} {mem : Memory}
    (hok : RegionOk ctx size) (hreg : LirRegion mem ctx size) :
    ∃ left mem' base limit,
      (∀ k, eval q k [size, budget] mem ctx = .ok ([left], mem')) ∧
      InitPost ctx budget mem mem' ∧
      AllocatorReady { cells := #[] } (fun _ => none) mem' (fun _ => 0)
        ctx base base limit [] (fun _ => []) := by
  rcases cxInit_cases_exact hq hmain size budget ctx mem with ⟨_, hbad⟩ | ⟨_, hgood⟩
  · exact False.elim (hbad hok)
  obtain ⟨left, mem', heval, hp, hm⟩ := hgood hreg
  obtain ⟨base, limit, hh⟩ := hp.heap
    { ctors := [], known := {}, bools := none, natPow := 0, natGcd := 0 }
  have hfit : ctx.toNat+576 < 2^64 := by
    have := hh.start; have := hh.bumpLe; have := hh.limitLt; omega
  have hb : (ctx-64).toNat = ctx.toNat-64 := ctx_sub_toNat hh.ctxLo (by decide)
  have hlo := hh.ctxLo
  have hmin : 4096 ≤ size.toNat := hok.2.1
  have hlim := hok.2.2
  have access : ∀ cls, 1 ≤ cls → cls ≤ 32 → ∀ j < 8,
      mem.readable (freeHeadAddress ctx (UInt64.ofNat cls)+UInt64.ofNat j) = true ∧
      mem.writable (freeHeadAddress ctx (UInt64.ofNat cls)+UInt64.ofNat j) = true := by
    intro cls hc hc' j hj
    have hn := head_nat hfit (cls := cls) (by omega)
    exact lirRegion_at hreg (by omega) (by omega) (by omega)
  refine ⟨left, mem', base, limit, heval, hp, empty_ready hh ?_ ?_⟩
  · intro cls hc hc'
    rw [hm]
    exact initMemory_head hh.ctxLo hfit hc hc' (fun j hj => (access cls hc hc' j hj).1)
  · intro cls hc hc' j hj
    rw [hp.writable]
    exact (access cls hc hc' j hj).2



end IxCC.Rt.Rc.Procs.Init
