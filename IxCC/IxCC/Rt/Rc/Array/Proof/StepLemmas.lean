import IxCC.Rt.Rc.Array.Procs
import IxCC.Rt.Rc.Array.Invariant
import IxCC.Lir.Proof.Run

/-! # Generic Fast Lir Step Combinators for Array Runtime Proofs

Provides zero-unfolding small-step lemmas (`step_assign`, `step_store`,
`step_br_true`, `step_br_false`, `step_brOvf_ok`, `step_brOvf_ovf`, `step_jump`,
`step_call`, `step_tail`, `step_ret_one`, `step_ret_zero`, `step_fail`,
`step_trap`, `state_initial_of`) and `arrayProgram` direct function lookup
lemmas so proofs never unfold `arrayRuntimeFuncs` and typecheck in milliseconds. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok)
open IxCC.Rt.Rc (maxClass classWords classFor maxCellWords)
open IxCC.Rt.Rc.Procs (v i to cellAddr freeHeadAddress)
open IxCC.X86 (Memory)

/-! ## `arrayProgram` direct function lookup lemmas -/

@[simp] theorem arrayProgram_main (m : FunId) : (arrayProgram m).main = m := rfl
@[simp] theorem arrayProgram_func_inc (m : FunId) : (arrayProgram m).funcs[fnInc]? = some IxCC.Rt.Rc.Procs.inc := rfl
@[simp] theorem arrayProgram_func_dec (m : FunId) : (arrayProgram m).funcs[fnDec]? = some arrDec := rfl
@[simp] theorem arrayProgram_func_classFor (m : FunId) : (arrayProgram m).funcs[fnClassFor]? = some arrClassFor := rfl
@[simp] theorem arrayProgram_func_classWords (m : FunId) : (arrayProgram m).funcs[fnClassWords]? = some arrClassWords := rfl
@[simp] theorem arrayProgram_func_allocCell (m : FunId) : (arrayProgram m).funcs[fnAllocCell]? = some arrAllocCell := rfl
@[simp] theorem arrayProgram_func_emptyCapBoxed (m : FunId) : (arrayProgram m).funcs[fnEmptyCapBoxed]? = some arrEmptyCapBoxed := rfl
@[simp] theorem arrayProgram_func_emptyCapLimbs (m : FunId) : (arrayProgram m).funcs[fnEmptyCapLimbs]? = some arrEmptyCapLimbs := rfl
@[simp] theorem arrayProgram_func_byteEmptyCap (m : FunId) : (arrayProgram m).funcs[fnByteEmptyCap]? = some byteArrEmptyCap := rfl
@[simp] theorem arrayProgram_func_size (m : FunId) : (arrayProgram m).funcs[fnSize]? = some arrSize := rfl
@[simp] theorem arrayProgram_func_cap (m : FunId) : (arrayProgram m).funcs[fnCap]? = some arrCap := rfl
@[simp] theorem arrayProgram_func_getWord (m : FunId) : (arrayProgram m).funcs[fnGetWord]? = some arrGet := rfl
@[simp] theorem arrayProgram_func_byteGet (m : FunId) : (arrayProgram m).funcs[fnByteGet]? = some byteArrGet := rfl
@[simp] theorem arrayProgram_func_setBoxed (m : FunId) : (arrayProgram m).funcs[fnSetBoxed]? = some arrSetBoxed := rfl
@[simp] theorem arrayProgram_func_setLimbs (m : FunId) : (arrayProgram m).funcs[fnSetLimbs]? = some arrSetLimbs := rfl
@[simp] theorem arrayProgram_func_pushBoxed (m : FunId) : (arrayProgram m).funcs[fnPushBoxed]? = some arrPushBoxed := rfl
@[simp] theorem arrayProgram_func_pushLimbs (m : FunId) : (arrayProgram m).funcs[fnPushLimbs]? = some arrPushLimbs := rfl
@[simp] theorem arrayProgram_func_popBoxed (m : FunId) : (arrayProgram m).funcs[fnPopBoxed]? = some arrPopBoxed := rfl
@[simp] theorem arrayProgram_func_popLimbs (m : FunId) : (arrayProgram m).funcs[fnPopLimbs]? = some arrPopLimbs := rfl
@[simp] theorem arrayProgram_func_extractLimbs (m : FunId) : (arrayProgram m).funcs[fnExtractLimbs]? = some arrExtractLimbs := rfl
@[simp] theorem arrayProgram_func_copySliceLimbs (m : FunId) : (arrayProgram m).funcs[fnCopySliceLimbs]? = some arrCopySliceLimbs := rfl
@[simp] theorem arrayProgram_func_byteSet (m : FunId) : (arrayProgram m).funcs[fnByteSet]? = some byteArrSet := rfl
@[simp] theorem arrayProgram_func_bytePush (m : FunId) : (arrayProgram m).funcs[fnBytePush]? = some byteArrPush := rfl
@[simp] theorem arrayProgram_func_bytePop (m : FunId) : (arrayProgram m).funcs[fnBytePop]? = some byteArrPop := rfl
@[simp] theorem arrayProgram_func_byteExtract (m : FunId) : (arrayProgram m).funcs[fnByteExtract]? = some byteArrExtract := rfl
@[simp] theorem arrayProgram_func_byteCopySlice (m : FunId) : (arrayProgram m).funcs[fnByteCopySlice]? = some byteArrCopySlice := rfl

/-! ## Word and address arithmetic helpers -/

theorem u64_toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h

theorem w64_trunc (w : Word) : X86.Width.truncate .w64 w = w := by
  simp only [X86.Width.truncate, X86.Width.mask]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, show (0xffffffffffffffff : Word).toNat = 2 ^ 64 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt w.toNat_lt_size

theorem cond_eq_w64 (a b : Word) : Cond.holds .eq .w64 a b = (a == b) := by
  simp only [Cond.holds, w64_trunc]

theorem cond_ne_w64 (a b : Word) : Cond.holds .ne .w64 a b = (a != b) := by
  simp only [Cond.holds, w64_trunc]

theorem cond_ult_w64 (a b : Word) : Cond.holds .ult .w64 a b = decide (a.toNat < b.toNat) := by
  simp only [Cond.holds, w64_trunc, UInt64.lt_iff_toNat_lt]

theorem cond_ule_w64 (a b : Word) : Cond.holds .ule .w64 a b = decide (a.toNat ≤ b.toNat) := by
  simp only [Cond.holds, w64_trunc, UInt64.le_iff_toNat_le]

theorem cond_ugt_w64 (a b : Word) : Cond.holds .ugt .w64 a b = decide (b.toNat < a.toNat) := by
  simp only [Cond.holds, w64_trunc, gt_iff_lt, UInt64.lt_iff_toNat_lt]

theorem u64_add_ofNat {a b : Nat} (h : a + b < 2 ^ 64) :
    UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega),
    u64_toNat_ofNat_lt h, Nat.mod_eq_of_lt h]

theorem u64_sub_ofNat {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ 64) :
    UInt64.ofNat a - UInt64.ofNat b = UInt64.ofNat (a - b) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by
    rw [UInt64.le_iff_toNat_le, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt ha]; exact hba),
    u64_toNat_ofNat_lt ha, u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by omega)]

theorem u64_shl_ofNat {a s : Nat} (hs : s < 64) (ha : a < 2 ^ 64) (hres : a <<< s < 2 ^ 64) :
    UInt64.ofNat a <<< UInt64.ofNat s = UInt64.ofNat (a <<< s) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, u64_toNat_ofNat_lt ha, u64_toNat_ofNat_lt (by omega),
    Nat.mod_eq_of_lt hs, u64_toNat_ofNat_lt hres, Nat.mod_eq_of_lt hres]

theorem u64_shr_ofNat {a s : Nat} (hs : s < 64) (ha : a < 2 ^ 64) :
    UInt64.ofNat a >>> UInt64.ofNat s = UInt64.ofNat (a >>> s) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, u64_toNat_ofNat_lt ha, u64_toNat_ofNat_lt (by omega),
    Nat.mod_eq_of_lt hs,
    u64_toNat_ofNat_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem u64_and_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNat a &&& UInt64.ofNat b = UInt64.ofNat (a &&& b) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, u64_toNat_ofNat_lt ha, u64_toNat_ofNat_lt hb,
    u64_toNat_ofNat_lt (Nat.lt_of_le_of_lt Nat.and_le_left ha)]

theorem shiftMask64_ofNat {s : Nat} (hs : s < 64) :
    (UInt64.ofNat s &&& shiftMask .w64) = UInt64.ofNat s := by
  rw [show shiftMask .w64 = UInt64.ofNat 63 from rfl, u64_and_ofNat (by omega) (by decide)]
  congr 1
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt hs

theorem binOp_sub64 (a b : Nat) (hba : b ≤ a) (ha : a < 2 ^ 64) :
    BinOp.eval .sub .w64 (UInt64.ofNat a) (UInt64.ofNat b) = some (UInt64.ofNat (a - b)) := by
  simp only [BinOp.eval, w64_trunc, u64_sub_ofNat hba ha]

theorem binOp_add64 (a b : Nat) (h : a + b < 2 ^ 64) :
    BinOp.eval .add .w64 (UInt64.ofNat a) (UInt64.ofNat b) = some (UInt64.ofNat (a + b)) := by
  simp only [BinOp.eval, w64_trunc, u64_add_ofNat h]

theorem binOp_and64 (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BinOp.eval .and .w64 (UInt64.ofNat a) (UInt64.ofNat b) = some (UInt64.ofNat (a &&& b)) := by
  simp only [BinOp.eval, w64_trunc, u64_and_ofNat ha hb]

theorem binOp_shl64 (a s : Nat) (hs : s < 64) (ha : a < 2 ^ 64) (hres : a <<< s < 2 ^ 64) :
    BinOp.eval .shl .w64 (UInt64.ofNat a) (UInt64.ofNat s) = some (UInt64.ofNat (a <<< s)) := by
  simp only [BinOp.eval, w64_trunc, shiftMask64_ofNat hs, u64_shl_ofNat hs ha hres]

theorem binOp_shr64 (a s : Nat) (hs : s < 64) (ha : a < 2 ^ 64) :
    BinOp.eval .shr .w64 (UInt64.ofNat a) (UInt64.ofNat s) = some (UInt64.ofNat (a >>> s)) := by
  simp only [BinOp.eval, w64_trunc, shiftMask64_ofNat hs, u64_shr_ofNat hs ha]

theorem binOp_or64 (a b : Word) :
    BinOp.eval .or .w64 a b = some (a ||| b) := by
  simp only [BinOp.eval, w64_trunc]

theorem dispWord_ofNat (n : Nat) : dispWord (Int.ofNat n) = UInt64.ofNat n := by
  change UInt64.ofBitVec (BitVec.ofInt 64 (n : Int)) = UInt64.ofNat n
  rw [BitVec.ofInt_natCast]
  rfl

theorem cellAddr_eval {ρ : Env} {ctx addr : Word} {base : VReg} {off : Nat}
    (hb : ρ[base]? = some addr) :
    (cellAddr base (Int.ofNat off)).eval ρ ctx = some (addr + UInt64.ofNat off) := by
  simp only [cellAddr, Addr.eval, hb, bind, Option.bind, UInt64.add_zero, dispWord_ofNat]

theorem cellAddr_eval_1 {ρ : Env} {ctx addr : Word} {base : VReg}
    (hb : ρ[base]? = some addr) :
    (cellAddr base 1).eval ρ ctx = some (addr + 1) := cellAddr_eval (off := 1) hb

theorem cellAddr_eval_4 {ρ : Env} {ctx addr : Word} {base : VReg}
    (hb : ρ[base]? = some addr) :
    (cellAddr base 4).eval ρ ctx = some (addr + 4) := cellAddr_eval (off := 4) hb

theorem cellAddr_eval_8 {ρ : Env} {ctx addr : Word} {base : VReg}
    (hb : ρ[base]? = some addr) :
    (cellAddr base 8).eval ρ ctx = some (addr + 8) := cellAddr_eval (off := 8) hb

theorem cellAddr_eval_16 {ρ : Env} {ctx addr : Word} {base : VReg}
    (hb : ρ[base]? = some addr) :
    (cellAddr base 16).eval ρ ctx = some (addr + 16) := cellAddr_eval (off := 16) hb

theorem ctxAddr_eval (ρ : Env) (ctx : Word) (off : Int) :
    (IxCC.Rt.Rc.Procs.ctx off).eval ρ ctx = some (ctx + dispWord off) := by
  simp only [IxCC.Rt.Rc.Procs.ctx, Addr.eval, bind, Option.bind, UInt64.add_zero]

theorem ctxAddr_eval_bump (ρ : Env) (ctx : Word) :
    (IxCC.Rt.Rc.Procs.ctx IxCC.Rt.bumpOff).eval ρ ctx = some (IxCC.Rt.Rc.Procs.bumpAddress ctx) :=
  ctxAddr_eval ρ ctx IxCC.Rt.bumpOff

theorem ctxAddr_eval_limit (ρ : Env) (ctx : Word) :
    (IxCC.Rt.Rc.Procs.ctx IxCC.Rt.limitOff).eval ρ ctx = some (IxCC.Rt.Rc.Procs.limitAddress ctx) :=
  ctxAddr_eval ρ ctx IxCC.Rt.limitOff

theorem cellAddr0_eval {ρ : Env} {ctx addr : Word} {base : VReg}
    (hb : ρ[base]? = some addr) :
    (cellAddr base 0).eval ρ ctx = some addr := by
  simp [cellAddr, Addr.eval, hb, dispWord]

theorem wordElemAddr_eval {ρ : Env} {ctx addr : Word} {base idxReg : VReg} {j : Nat}
    (hb : ρ[base]? = some addr) (hi : ρ[idxReg]? = some (UInt64.ofNat j))
    (hj : 24 + 8 * j < 2 ^ 64) :
    (wordElemAddr base idxReg).eval ρ ctx =
      some (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)) := by
  simp only [wordElemAddr, Addr.eval, hb, hi, X86.Scale.word, bind, Option.bind,
    Functor.map, Option.map]
  congr 1
  have h24 : dispWord 24 = UInt64.ofNat 24 := dispWord_ofNat 24
  have hm : UInt64.ofNat j * 8 = UInt64.ofNat (8 * j) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mul, u64_toNat_ofNat_lt (by omega), show (8 : Word).toNat = 8 from rfl,
      u64_toNat_ofNat_lt (by omega), Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
  rw [h24, hm, UInt64.add_assoc, u64_add_ofNat (by omega)]
  unfold arrayPayloadOffset
  rw [Nat.add_comm (8 * j) 24]

theorem byteElemAddr_eval {ρ : Env} {ctx addr : Word} {base idxReg : VReg} {j : Nat}
    (hb : ρ[base]? = some addr) (hi : ρ[idxReg]? = some (UInt64.ofNat j))
    (hj : 24 + j < 2 ^ 64) :
    (byteElemAddr base idxReg).eval ρ ctx =
      some (addr + UInt64.ofNat (arrayPayloadOffset + j)) := by
  simp only [byteElemAddr, Addr.eval, hb, hi, X86.Scale.word, bind, Option.bind,
    Functor.map, Option.map]
  congr 1
  have h24 : dispWord 24 = UInt64.ofNat 24 := dispWord_ofNat 24
  rw [h24, UInt64.mul_one, UInt64.add_assoc, u64_add_ofNat (by omega)]
  unfold arrayPayloadOffset
  rw [Nat.add_comm j 24]

theorem ctxHeadAddr_eval {ρ : Env} {ctx : Word} {r : VReg} {cls : Nat}
    (hr : ρ[r]? = some (UInt64.ofNat cls)) :
    (ctxHeadAddr r).eval ρ ctx = some (freeHeadAddress ctx (UInt64.ofNat cls)) := by
  simp only [ctxHeadAddr, Addr.eval, hr, X86.Scale.word, bind, Option.bind,
    Functor.map, Option.map, dispWord, freeHeadAddress]
  congr 1
  rw [show UInt64.ofBitVec (BitVec.ofInt 64 0) = 0 from rfl, UInt64.add_zero]

theorem env_get_insert (ρ : Env) (k k' : VReg) (val : Word) :
    (ρ.insert k val)[k']? = if k = k' then some val else ρ[k']? := by
  simp [Std.HashMap.getElem?_insert]

theorem env_get_insert_self (ρ : Env) (k : VReg) (val : Word) :
    (ρ.insert k val)[k]? = some val := by
  simp

theorem evalArgs_singleton {ρ : Env} {a : Arg} {val : Word}
    (ha : a.eval ρ = some val) : evalArgs ρ [a] = some [val] := by
  simp [evalArgs, ha]

theorem evalArgs_pair {ρ : Env} {a b : Arg} {va vb : Word}
    (ha : a.eval ρ = some va) (hb : b.eval ρ = some vb) :
    evalArgs ρ [a, b] = some [va, vb] := by
  simp [evalArgs, ha, hb]

theorem wordAt_write64_disjoint {m : Memory} {a wa val v : Word}
    (h : WordAt m a v)
    (hwa : wa.toNat + 8 ≤ 2 ^ 64) (ha : a.toNat + 8 ≤ 2 ^ 64)
    (hsep : a.toNat + 8 ≤ wa.toNat ∨ wa.toNat + 8 ≤ a.toNat) :
    WordAt (m.write .w64 wa val) a v :=
  h.write_disjoint hwa ha hsep

theorem addr_toNat_1 {a : Word} (h : a.toNat + 1 < 2 ^ 64) : (a + 1).toNat = a.toNat + 1 :=
  addr_toNat (i := 1) h

theorem addr_toNat_8 {a : Word} (h : a.toNat + 8 < 2 ^ 64) : (a + 8).toNat = a.toNat + 8 :=
  addr_toNat (i := 8) h

theorem addr_toNat_16 {a : Word} (h : a.toNat + 16 < 2 ^ 64) : (a + 16).toNat = a.toNat + 16 :=
  addr_toNat (i := 16) h

/-! ## Generic zero-unfolding Lir small-step lemmas -/

theorem state_initial_of {p : Program} {f : Func} {args : List Word} {env : Env}
    {mem : Memory} {context : Word}
    (hf : p.funcs[p.main]? = some f)
    (hbind : bindParams {} f.params args = some env) :
    State.initial p args mem context =
      some (State.mk mem context [{ fn := p.main, label := 0, pos := 0, env }]) := by
  simp [State.initial, enter, hf, hbind]

theorem step_assign {p : Program} {fn lbl pos : Nat} {f : Func} {blk : Block}
    {dst : VReg} {rhs : Rhs} {val : Word} {env : Env} {mem : Memory} {context : Word}
    {rest : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos < blk.body.size) (hst : blk.body[pos]'hpos = .assign dst rhs)
    (hrhs : rhs.eval env mem context = some val) :
    semStep p (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) =
      .next (State.mk mem context ({ fn, label := lbl, pos := pos + 1, env := env.insert dst val } :: rest)) false := by
  apply semStep_next.mpr
  simp [step, hf, hb, hpos, hst, Stmt.exec, hrhs]

theorem step_store {p : Program} {fn lbl pos : Nat} {f : Func} {blk : Block}
    {w : Width} {m : Addr} {a : Arg} {addr val : Word} {env : Env} {mem mem' : Memory}
    {context : Word} {rest : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos < blk.body.size) (hst : blk.body[pos]'hpos = .store w m a)
    (hm : m.eval env context = some addr) (ha : a.eval env = some val)
    (hwr : mem.write? w addr val = .ok mem') :
    semStep p (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) =
      .next (State.mk mem' context ({ fn, label := lbl, pos := pos + 1, env } :: rest)) false := by
  apply semStep_next.mpr
  simp [step, hf, hb, hpos, hst, Stmt.exec, hm, ha, hwr]

theorem step_call {p : Program} {fn lbl pos : Nat} {f gFunc : Func} {blk : Block}
    {dsts : List VReg} {g : FunId} {args : List Arg} {vals : List Word}
    {env calleeEnv : Env} {mem : Memory} {context : Word} {rest : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos < blk.body.size) (hst : blk.body[pos]'hpos = .call dsts g args)
    (hargs : evalArgs env args = some vals)
    (hg : p.funcs[g]? = some gFunc)
    (hbind : bindParams {} gFunc.params vals = some calleeEnv) :
    semStep p (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) =
      .next (State.mk mem context
        ({ fn := g, label := 0, pos := 0, env := calleeEnv } ::
          { fn, label := lbl, pos := pos + 1, env, dsts } :: rest)) true := by
  apply semStep_next.mpr
  simp [step, hf, hb, hpos, hst, hargs, enter, hg, hbind]

theorem step_jump {p : Program} {fn lbl : Nat} {f : Func} {blk target : Block}
    {edge : Edge} {vals : List Word} {env env' : Env} {mem : Memory} {context : Word}
    {rest : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (ht : blk.term = .jump edge)
    (hargs : evalArgs env edge.args = some vals)
    (htgt : f.blocks[edge.target]? = some target)
    (hbind : bindParams env target.params vals = some env') :
    semStep p (State.mk mem context ({ fn, label := lbl, pos := blk.body.size, env } :: rest)) =
      .next (State.mk mem context ({ fn, label := edge.target, pos := 0, env := env' } :: rest))
        (decide (edge.target ≤ lbl)) := by
  apply semStep_next.mpr
  simp [step, hf, hb, ht, takeEdge, hargs, htgt, hbind]

theorem step_br_true {p : Program} {fn lbl : Nat} {f : Func} {blk target : Block}
    {c : Cond} {w : Width} {a b : Arg} {t e : Edge} {va vb : Word} {vals : List Word}
    {env env' : Env} {mem : Memory} {context : Word} {rest : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (ht : blk.term = .br c w a b t e)
    (ha : a.eval env = some va) (hbv : b.eval env = some vb)
    (hc : c.holds w va vb = true)
    (hargs : evalArgs env t.args = some vals)
    (htgt : f.blocks[t.target]? = some target)
    (hbind : bindParams env target.params vals = some env') :
    semStep p (State.mk mem context ({ fn, label := lbl, pos := blk.body.size, env } :: rest)) =
      .next (State.mk mem context ({ fn, label := t.target, pos := 0, env := env' } :: rest))
        (decide (t.target ≤ lbl)) := by
  apply semStep_next.mpr
  simp [step, hf, hb, ht, ha, hbv, hc, takeEdge, hargs, htgt, hbind]

theorem step_br_false {p : Program} {fn lbl : Nat} {f : Func} {blk target : Block}
    {c : Cond} {w : Width} {a b : Arg} {t e : Edge} {va vb : Word} {vals : List Word}
    {env env' : Env} {mem : Memory} {context : Word} {rest : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (ht : blk.term = .br c w a b t e)
    (ha : a.eval env = some va) (hbv : b.eval env = some vb)
    (hc : c.holds w va vb = false)
    (hargs : evalArgs env e.args = some vals)
    (htgt : f.blocks[e.target]? = some target)
    (hbind : bindParams env target.params vals = some env') :
    semStep p (State.mk mem context ({ fn, label := lbl, pos := blk.body.size, env } :: rest)) =
      .next (State.mk mem context ({ fn, label := e.target, pos := 0, env := env' } :: rest))
        (decide (e.target ≤ lbl)) := by
  apply semStep_next.mpr
  simp [step, hf, hb, ht, ha, hbv, hc, takeEdge, hargs, htgt, hbind]

theorem step_brOvf_ok {p : Program} {fn lbl : Nat} {f : Func} {blk target : Block}
    {o : Ovf} {x : VReg} {a b : Arg} {ok ovf : Edge} {va vb res : Word} {vals : List Word}
    {env env' : Env} {mem : Memory} {context : Word} {rest : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (ht : blk.term = .brOvf o x a b ok ovf)
    (ha : a.eval env = some va) (hbv : b.eval env = some vb)
    (ho : o.eval va vb = (res, false))
    (hargs : evalArgs (env.insert x res) ok.args = some vals)
    (htgt : f.blocks[ok.target]? = some target)
    (hbind : bindParams (env.insert x res) target.params vals = some env') :
    semStep p (State.mk mem context ({ fn, label := lbl, pos := blk.body.size, env } :: rest)) =
      .next (State.mk mem context ({ fn, label := ok.target, pos := 0, env := env' } :: rest))
        (decide (ok.target ≤ lbl)) := by
  apply semStep_next.mpr
  simp [step, hf, hb, ht, ha, hbv, ho, takeEdge, hargs, htgt, hbind]

theorem step_brOvf_ovf {p : Program} {fn lbl : Nat} {f : Func} {blk target : Block}
    {o : Ovf} {x : VReg} {a b : Arg} {ok ovf : Edge} {va vb res : Word} {vals : List Word}
    {env env' : Env} {mem : Memory} {context : Word} {rest : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (ht : blk.term = .brOvf o x a b ok ovf)
    (ha : a.eval env = some va) (hbv : b.eval env = some vb)
    (ho : o.eval va vb = (res, true))
    (hargs : evalArgs (env.insert x res) ovf.args = some vals)
    (htgt : f.blocks[ovf.target]? = some target)
    (hbind : bindParams (env.insert x res) target.params vals = some env') :
    semStep p (State.mk mem context ({ fn, label := lbl, pos := blk.body.size, env } :: rest)) =
      .next (State.mk mem context ({ fn, label := ovf.target, pos := 0, env := env' } :: rest))
        (decide (ovf.target ≤ lbl)) := by
  apply semStep_next.mpr
  simp [step, hf, hb, ht, ha, hbv, ho, takeEdge, hargs, htgt, hbind]

theorem step_tail {p : Program} {fn lbl : Nat} {f gFunc : Func} {blk : Block}
    {g : FunId} {args : List Arg} {vals : List Word} {env calleeEnv : Env}
    {mem : Memory} {context : Word} {rest : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (ht : blk.term = .tail g args)
    (hargs : evalArgs env args = some vals)
    (hg : p.funcs[g]? = some gFunc)
    (hbind : bindParams {} gFunc.params vals = some calleeEnv) :
    semStep p (State.mk mem context ({ fn, label := lbl, pos := blk.body.size, env } :: rest)) =
      .next (State.mk mem context ({ fn := g, label := 0, pos := 0, env := calleeEnv } :: rest)) true := by
  apply semStep_next.mpr
  simp [step, hf, hb, ht, hargs, enter, hg, hbind]

theorem step_ret_one {p : Program} {fn lbl : Nat} {f : Func} {blk : Block}
    {arg : Arg} {env : Env} {mem : Memory} {context res : Word} {rest : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (ht : blk.term = .ret [arg]) (ha : arg.eval env = some res) :
    match rest with
    | [] => semStep p (State.mk mem context ({ fn, label := lbl, pos := blk.body.size, env } :: rest)) =
        .done ([res], mem)
    | caller :: tail =>
        ∀ dst, caller.dsts = [dst] →
          semStep p (State.mk mem context ({ fn, label := lbl, pos := blk.body.size, env } :: rest)) =
            .next (State.mk mem context ({ caller with env := caller.env.insert dst res, dsts := [] } :: tail)) false := by
  cases rest with
  | nil =>
    apply semStep_done.mpr
    simp [step, hf, hb, ht, evalArgs, ha]
  | cons caller tail =>
    intro dst hdst
    apply semStep_next.mpr
    simp [step, hf, hb, ht, evalArgs, ha, hdst, bindParams]

theorem step_ret_zero_done {p : Program} {fn lbl : Nat} {f : Func} {blk : Block}
    {env : Env} {mem : Memory} {context : Word}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (ht : blk.term = .ret []) :
    semStep p (State.mk mem context [{ fn, label := lbl, pos := blk.body.size, env }]) =
      .done ([], mem) := by
  apply semStep_done.mpr
  simp [step, hf, hb, ht, evalArgs]

theorem step_fail {p : Program} {fn lbl : Nat} {f : Func} {blk : Block}
    {r : Sem.Resource} {env : Env} {mem : Memory} {context : Word} {rest : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (ht : blk.term = .fail r) :
    semStep p (State.mk mem context ({ fn, label := lbl, pos := blk.body.size, env } :: rest)) =
      .fail r := by
  apply semStep_fail.mpr
  simp [step, hf, hb, ht]

theorem step_trap {p : Program} {fn lbl : Nat} {f : Func} {blk : Block}
    {env : Env} {mem : Memory} {context : Word} {rest : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (ht : blk.term = .trap) :
    semStep p (State.mk mem context ({ fn, label := lbl, pos := blk.body.size, env } :: rest)) =
      .trap := by
  apply semStep_trap.mpr
  simp [step, hf, hb, ht]

theorem rhs_load_eval {env : Env} {mem : Memory} {ctx addr val : Word} {w : Width} {ext : Ext} {a : Addr}
    (ha : a.eval env ctx = some addr) (hl : loadWord mem w ext addr = some val) :
    Rhs.eval env mem ctx (.load w ext a) = some val := by
  simp only [Rhs.eval, ha, hl, bind, Option.bind]

theorem rhs_bin_eval {env : Env} {mem : Memory} {ctx va vb val : Word} {op : BinOp} {w : Width} {a b : Arg}
    (ha : a.eval env = some va) (hb : b.eval env = some vb) (ho : op.eval w va vb = some val) :
    Rhs.eval env mem ctx (.bin op w a b) = some val := by
  simp only [Rhs.eval, ha, hb, ho, bind, Option.bind]

theorem rhs_bsr64_eval {env : Env} {mem : Memory} {ctx : Word} {a : Arg} {x : Nat}
    (ha : a.eval env = some (UInt64.ofNat x)) (hpos : 0 < x) (hlt : x < 2 ^ 64) :
    Rhs.eval env mem ctx (.bsr64 a) = some (UInt64.ofNat x.log2) := by
  have hne : (UInt64.ofNat x == 0) = false := beq_false_of_ne (fun h => by
    have := congrArg UInt64.toNat h
    rw [u64_toNat_ofNat_lt hlt] at this; simp at this; omega)
  simp only [Rhs.eval, ha, bind, Option.bind, hne, Bool.false_eq_true, ↓reduceIte, u64_toNat_ofNat_lt hlt]

theorem final_ret_one {p : Program} {fn lbl : Nat} {f : Func} {blk : Block}
    {arg : Arg} {env : Env} {mem : Memory} {context res : Word}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (ht : blk.term = .ret [arg]) (ha : arg.eval env = some res) :
    Sem.Final (semStep p (State.mk mem context [{ fn, label := lbl, pos := blk.body.size, env }]))
      (.ok ([res], mem)) := by
  rw [step_ret_one (rest := []) hf hb ht ha]; exact .done

theorem final_ret_zero {p : Program} {fn lbl : Nat} {f : Func} {blk : Block}
    {env : Env} {mem : Memory} {context : Word}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (ht : blk.term = .ret []) :
    Sem.Final (semStep p (State.mk mem context [{ fn, label := lbl, pos := blk.body.size, env }]))
      (.ok ([], mem)) := by
  rw [step_ret_zero_done hf hb ht]; exact .done

theorem final_fail {p : Program} {fn lbl : Nat} {f : Func} {blk : Block}
    {r : Sem.Resource} {env : Env} {mem : Memory} {context : Word} {rest : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (ht : blk.term = .fail r) :
    Sem.Final (semStep p (State.mk mem context ({ fn, label := lbl, pos := blk.body.size, env } :: rest)))
      (.resource r) := by
  rw [step_fail hf hb ht]; exact .fail

theorem final_trap {p : Program} {fn lbl : Nat} {f : Func} {blk : Block}
    {env : Env} {mem : Memory} {context : Word} {rest : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (ht : blk.term = .trap) :
    Sem.Final (semStep p (State.mk mem context ({ fn, label := lbl, pos := blk.body.size, env } :: rest)))
      .trap := by
  rw [step_trap hf hb ht]; exact .trap

end IxCC.Rt.Rc.Array
