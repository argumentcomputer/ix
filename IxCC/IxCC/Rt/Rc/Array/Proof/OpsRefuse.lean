import IxCC.Rt.Rc.Array.Proof.OpsBoxed

/-! # Refusal: an allocation the arena cannot meet is a heap failure

`alloc_refuses`: `Ops.alloc k` refuses a request above `k.maxCap`, or one whose class has no
free cell and no room below the limit, by the runtime's heap-resource failure (`.resource .heap`),
whatever its caller. `reaches_call` carries a callee's failure to its caller, so a procedure whose
allocation is refused fails the same way (`push_grow_refuses`). -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok)
open IxCC.Rt.Rc (maxClass classBytes classWords maxCellWords)
open IxCC.Rt.Rc.Procs (v i to cellAddr freeHeadAddress)
open IxCC.X86 (Memory)
open Ops

/-- A callee's end result is its caller's: the call is one charge. -/
theorem reaches_call {p : Program} {fn lbl pos : Nat} {f gFunc : Func} {blk : Block}
    {dsts : List VReg} {g : FunId} {args : List Arg} {vals : List Word} {env calleeEnv : Env}
    {mem : Memory} {context : Word} {rest : List Frame} {k : Nat} {r : Sem.Result (List Word × Memory)}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos < blk.body.size) (hst : blk.body[pos]'hpos = .call dsts g args)
    (hargs : evalArgs env args = some vals) (hg : p.funcs[g]? = some gFunc)
    (hbind : bindParams {} gFunc.params vals = some calleeEnv)
    (hk : Sem.Reaches (semStep p) (State.mk mem context
      ({ fn := g, label := 0, pos := 0, env := calleeEnv } ::
        { fn, label := lbl, pos := pos + 1, env, dsts } :: rest)) k r) :
    Sem.Reaches (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) (k + 1) r :=
  .charge (step_call hf hb hpos hst hargs hg hbind) hk

/-- The registers of `alloc` at its entry. -/
def allocEnv (n : Nat) : Env := ({} : Env).insert 0 (UInt64.ofNat n)

/-- **Refusal.** A request above the largest capacity, or one the arena cannot meet. -/
theorem alloc_refuses {P : Program} {fn : FunId} {t : Fns} {k : ElemKind}
    (hfn : P.funcs[fn]? = some (alloc t k)) (hcf : P.funcs[t.classFor]? = some arrClassFor)
    (hcw : P.funcs[t.classWords]? = some arrClassWords)
    {mem : Memory} {ctx base bump limit : Word} {lists : Nat → List Word}
    (halloc : ArrayAllocator mem ctx base bump limit lists) {n : Nat} (hn64 : n < 2 ^ 64)
    (hno : k.maxCap < n ∨ (n ≤ k.maxCap ∧ lists (allocClass k n) = [] ∧
      limit.toNat < bump.toNat + classBytes (allocClass k n)))
    (rest : List Frame) (clock : Nat) :
    Sem.Reaches (semStep P) (State.mk mem ctx ({ fn, label := 0, pos := 0, env := allocEnv n } ::
      rest)) (clock + 2) (.resource .heap) := by
  unfold allocEnv
  have hmcl := ElemKind.maxCap_lt k
  rcases hno with hbig | ⟨hn, hlist, hlim⟩
  · have hugt : Cond.holds .ugt .w64 (UInt64.ofNat n) (UInt64.ofNat k.maxCap) = true := by
      rw [cond_ugt_w64, u64_toNat_ofNat_lt hn64, u64_toNat_ofNat_lt (by omega)]
      exact decide_eq_true hbig
    exact Sem.Reaches.star (c := 0) (k := clock + 2) (star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hugt
      (evalArgs_nil _) rfl rfl (.refl _)) (reaches_fail (lbl := 7) (pos := 0) hfn rfl rfl rfl)
  · obtain ⟨hlo, hhi, _⟩ := allocClass_spec k hn
    have hc1 : 1 ≤ allocClass k n := by unfold minArrayClass at hlo; omega
    have hhead := wordAt_load64 (halloc.free_heads _ hc1 hhi)
    rw [hlist, List.headD_nil] at hhead
    obtain ⟨e, h5, h6, h7, hpre⟩ := alloc_prefix hfn hcf hcw hn hhead
    have hcwm := IxCC.Rt.Rc.classWords_le_max hhi
    have hmax : maxCellWords = 2 ^ 26 := IxCC.Rt.Rc.maxCellWords_eq
    have hcbytes : classBytes (allocClass k n) = 8 * classWords (allocClass k n) := rfl
    have hlf := halloc.limit_fit
    have hbl := halloc.bump_le_limit
    have hshl3 : BinOp.eval .shl .w64 (UInt64.ofNat (classWords (allocClass k n))) (UInt64.ofNat 3) =
        some (UInt64.ofNat (classBytes (allocClass k n))) := by
      rw [binOp_shl64 _ 3 (by decide) (by omega) (by rw [Nat.shiftLeft_eq]; omega), Nat.shiftLeft_eq,
        hcbytes, Nat.mul_comm]
    have hcbw : (UInt64.ofNat (classBytes (allocClass k n))).toNat = classBytes (allocClass k n) :=
      u64_toNat_ofNat_lt (by omega)
    have hbn' : (bump + UInt64.ofNat (classBytes (allocClass k n))).toNat =
        bump.toNat + classBytes (allocClass k n) := addr_toNat (by omega)
    have hule : Cond.holds .ule .w64 (bump + UInt64.ofNat (classBytes (allocClass k n))) limit = false := by
      rw [cond_ule_w64, hbn']; exact decide_eq_false (by omega)
    have hrun := (hpre rest).trans (star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval)
      (by decide) (evalArgs_nil _) rfl rfl
      (star_assign hfn rfl (by body_pos) rfl
        (rhs_load_eval (ctxAddr_eval_bump _ _) (wordAt_load64 halloc.bump_word))
      (star_assign hfn rfl (by body_pos) rfl
        (rhs_load_eval (ctxAddr_eval_limit _ _) (wordAt_load64 halloc.limit_word))
      (star_assign hfn rfl (by body_pos) rfl (rhs_bin_eval (by arg_eval) (by arg_eval) hshl3)
      (star_brOvf_ok_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval)
        (ovf_addC_ok (by rw [hcbw]; omega)) (evalArgs_nil _) rfl rfl
      (star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hule
        (evalArgs_nil _) rfl rfl (.refl _)))))))
    have := Sem.Reaches.star hrun (reaches_fail (lbl := 7) (pos := 0) (k := clock) hfn rfl rfl rfl)
    simpa [Nat.add_comm] using this

end IxCC.Rt.Rc.Array
