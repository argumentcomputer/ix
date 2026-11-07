import IxCC.Rt.Rc.Proof.InitReady

set_option autoImplicit false
namespace IxCC.Rt.Rc.Procs.Init
open IxCC.Rt IxCC.Rt.Proof IxCC.Lir
open IxCC.X86 (Memory)

/-- The executed initializer's limit word, retained separately from the
existential legacy HeapInv postcondition. Existing accepted files stay intact. -/
theorem initMemory_limit {mem : Memory} {ctx size budget : Word}
    (hok : RegionOk ctx size) (hreg : LirRegion mem ctx size)
    (hc : 64 ≤ ctx.toNat) (hfit : ctx.toNat+576 < 2^64) :
    WordAt (initMemory mem ctx size budget) (ctx-32) (ctx-64+size) := by
  have hb : (ctx-64).toNat = ctx.toNat-64 := ctx_sub_toNat hc (by decide)
  have h32 : (ctx-32).toNat = ctx.toNat-32 := ctx_sub_toNat hc (by decide)
  have h24 : (ctx-24).toNat = ctx.toNat-24 := ctx_sub_toNat hc (by decide)
  have hmin : 4096 ≤ size.toNat := hok.2.1
  have hlim := hok.2.2
  let m := (mem.write .w64 (ctx-48) budget).write .w64 (ctx-40) (bumpOf (ctx-64))
  have readable : ∀ j < 8, m.readable (ctx-32+UInt64.ofNat j) = true := by
    intro j hj
    change mem.readable (ctx-32+UInt64.ofNat j) = true
    exact (lirRegion_at hreg (by omega) (by omega) (by omega)).1
  have written : WordAt (m.write .w64 (ctx-32) (ctx-64+size)) (ctx-32) (ctx-64+size) :=
    wordAt_write64 readable
  have retained := written.write_disjoint (a := ctx-24) (u := ctx-64) (w := .w64)
    (by change (ctx-24).toNat+8 ≤ 2^64; omega) (by omega) (Or.inl (by omega))
  apply zeros_keep (by omega) _ _ retained
  intro d member
  have address := zeroAddr hc hfit member
  exact ⟨by omega, Or.inl (by omega)⟩

/-- Initialization supplies the fixed arena extent needed for the actual
driver's region-size/8 readback fuel. It is not an additional driver premise. -/
theorem cxInit_ready_extent {q : Program} {g : FunId}
    (hq : q.funcs[g]? = some Procs.cxInit) (hmain : q.main = g)
    {size budget ctx : Word} {mem : Memory}
    (hok : RegionOk ctx size) (hreg : LirRegion mem ctx size) :
    ∃ left mem' base limit,
      (∀ k, eval q k [size,budget] mem ctx = .ok ([left],mem')) ∧
      InitPost ctx budget mem mem' ∧
      AllocatorReady {cells := #[]} (fun _ => none) mem' (fun _ => 0)
        ctx base base limit [] (fun _ => []) ∧
      limit.toNat-base.toNat ≤ size.toNat := by
  obtain ⟨left, mem', base, limit, run, post, ready⟩ := cxInit_ready hq hmain hok hreg
  rcases cxInit_cases_exact hq hmain size budget ctx mem with ⟨_, bad⟩ | ⟨_, good⟩
  · exact False.elim (bad hok)
  obtain ⟨left', exactMem, exactRun, _, exactEq⟩ := good hreg
  have memEq : mem' = exactMem :=
    congrArg Prod.snd (Sem.Result.ok.inj ((run 0).symm.trans (exactRun 0)))
  have initialized : mem' = initMemory mem ctx size budget := memEq.trans exactEq
  have hc : 64 ≤ ctx.toNat := by
    obtain ⟨_, _, hh⟩ := post.heap
      {ctors := [], known := {}, bools := none, natPow := 0, natGcd := 0}
    exact hh.ctxLo
  have hb : (ctx-64).toNat = ctx.toNat-64 := ctx_sub_toNat hc (by decide)
  have hreglim := hok.2.2
  have hfit : ctx.toNat+576 < 2^64 := by
    have hmin : 4096 ≤ size.toNat := hok.2.1
    omega
  have expected := initMemory_limit (budget := budget) hok hreg hc hfit
  rw [← initialized] at expected
  have actual := ready.limit_word
  rw [limitAddress_eq] at actual
  have limitEq : limit = ctx-64+size := Except.ok.inj (actual.read64.symm.trans expected.read64)
  refine ⟨left, mem', base, limit, run, post, ready, ?_⟩
  rw [limitEq, add_word_toNat, Nat.mod_eq_of_lt (by omega)]
  have lower := ready.context_before
  omega



end IxCC.Rt.Rc.Procs.Init
