import IxCC.Rt.Rc.Array.Proof.Exec
import IxCC.Rt.Rc.Array.Proof.BasicOps
import IxCC.Rt.Rc.Gen.Procs
import IxCC.Rt.Rc.Proof.FreeList
import IxCC.Rt.Rc.Proof.CountPreserve

/-! # The one release, path by path (`Rt.Rc.Gen.decArr`)

`decArr` is a loop over two cutpoints: block 1 dispatches the current value (`v1`) under a chain
of suspended parents (`v2`), block 6 resumes the chain (`v8`). This module gives one theorem for
every path between two cutpoints, in any program that holds `decArr` at some index and above any
suspended stack:

| from block 1 | to | theorem |
| --- | --- | --- |
| an immediate | 6 | `decArr_step_immediate` |
| a static cell | 6 | `decArr_step_static` |
| a shared cell | 6 | `decArr_step_shared` |
| the last reference, nothing to scan | 6 | `decArr_step_leaf` |
| the last reference, an empty boxed array | 6 | `decArr_step_array_empty` |
| the last reference, a boxed array | 1 | `decArr_step_array_detach` |
| the last reference, a constructor | 1 | `decArr_step_ctor_detach` |

| from block 6 | to | theorem |
| --- | --- | --- |
| no parent | 10 | `decArr_step_finish` |
| a finished parent | 6 | `decArr_step_recycle` |
| an array with elements left | 1 | `decArr_step_array_next` |
| a constructor with fields left | 1 | `decArr_step_ctor_next` |

The hypotheses of a step are the loads, branches and stores of its blocks and nothing else, so a
step applies to a cell of any invariant. `decArr_entry`, `decArr_ret` and `decArr_done` are the
ends of a call.

The second half states the paths that close over the array invariant alone (`LiveArrayCell`,
`StaticArrayCell`): an immediate, a static array, a shared array, the last reference of a packed
array, of an empty boxed array, and of a boxed array of immediates. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok wordAt_write64)
open IxCC.Rt.Rc (maxClass classBytes)
open IxCC.Rt.Rc.Gen (decArr arrayScan)
open IxCC.Rt.Rc.Procs (v i to cellAddr FreeChain freeHeadAddress storeCount countAddress
  recycleParent recycled_head)
open IxCC.X86 (Memory)

/-- The registers of `decArr` at its entry. -/
def decArrEnv (word : Word) : Env := ({} : Env).insert 0 word

/-! ## Addresses -/

/-- The free-list head slot of the class in register `r`. -/
theorem ctxHead_eval {ρ : Env} {ctx c : Word} {r : VReg} (hr : ρ[r]? = some c) :
    ({ base := some .ctx, index := some (r, .eight) } : Addr).eval ρ ctx =
      some (freeHeadAddress ctx c) := by
  simp only [Addr.eval, hr, X86.Scale.word, bind, Option.bind, Functor.map, Option.map, dispWord,
    freeHeadAddress]
  congr 1
  rw [show UInt64.ofBitVec (BitVec.ofInt 64 0) = 0 from rfl, UInt64.add_zero]

/-- A word-scaled field address `p + 8·idx + d`. -/
theorem scaledAddr_eval {ρ : Env} {ctx p idx : Word} {base idxReg : VReg} {d : Int}
    (hb : ρ[base]? = some p) (hi : ρ[idxReg]? = some idx) :
    ({ base := some (.v base), index := some (idxReg, .eight), disp := d } : Addr).eval ρ ctx =
      some (p + idx * 8 + dispWord d) := by
  simp only [Addr.eval, hb, hi, X86.Scale.word, bind, Option.bind, Functor.map, Option.map]

/-! ## The ends of a call -/

/-- From the entry to the dispatch of the argument, with no suspended parent. -/
theorem decArr_entry {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    (mem : Memory) (context word : Word) (rest : List Frame) :
    ∃ e, e[1]? = some word ∧ e[2]? = some 0 ∧
      Sem.Star (semStep P)
        (State.mk mem context ({ fn, label := 0, pos := 0, env := decArrEnv word } :: rest)) 0
        (State.mk mem context ({ fn, label := 1, pos := 0, env := e } :: rest)) := by
  refine ⟨?e, ?h1, ?h2, ?hs⟩
  case hs =>
    unfold decArrEnv
    refine star_jump_fwd hfn rfl rfl rfl rfl (evalArgs2 (by arg_eval) (by arg_eval)) rfl rfl ?_
    exact .refl _
  case h1 => env_lookup
  case h2 => exact env_get_insert_self'

/-- From block 10, `decArr` returns to a caller that awaits no result. -/
theorem decArr_ret {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    (mem : Memory) (context : Word) (e : Env) {caller : Frame} (callers : List Frame)
    (hd : caller.dsts = []) :
    Sem.Star (semStep P)
      (State.mk mem context ({ fn, label := 10, pos := 0, env := e } :: caller :: callers)) 0
      (State.mk mem context (caller :: callers)) :=
  star_ret_zero hfn rfl rfl rfl hd

/-- From block 10 as the last frame, `decArr` ends the run. -/
theorem decArr_done {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    (mem : Memory) (context : Word) (e : Env) (k : Nat) :
    Sem.Reaches (semStep P)
      (State.mk mem context [{ fn, label := 10, pos := 0, env := e }]) k (.ok ([], mem)) :=
  reaches_ret_zero hfn rfl rfl rfl

/-! ## Steps from the dispatch (block 1) -/

/-- An immediate: nothing is read. -/
theorem decArr_step_immediate {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    {mem : Memory} {context cur parent : Word} {e : Env}
    (he1 : e[1]? = some cur) (he2 : e[2]? = some parent) (htag : cur &&& 1 = 1)
    (rest : List Frame) :
    ∃ e', e'[8]? = some parent ∧
      Sem.Star (semStep P)
        (State.mk mem context ({ fn, label := 1, pos := 0, env := e } :: rest)) 0
        (State.mk mem context ({ fn, label := 6, pos := 0, env := e' } :: rest)) := by
  have htnz : Cond.holds .tnz .w64 cur (UInt64.ofNat 1) = true := by simp [Cond.holds, htag]
  refine ⟨?e, ?h8, ?hs⟩
  case hs =>
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) htnz
      (evalArgs1 (by arg_eval)) rfl rfl ?_
    exact .refl _
  case h8 => env_lookup

/-- A static cell (negative count word): one read, no write. -/
theorem decArr_step_static {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    {mem : Memory} {context cur parent count : Word} {e : Env}
    (he1 : e[1]? = some cur) (he2 : e[2]? = some parent)
    (hptr : Cond.holds .tnz .w64 cur 1 = false)
    (hcount : loadWord mem .w32 .zero (cur + 4) = some count)
    (hneg : Cond.holds .slt .w32 count 0 = true) (rest : List Frame) :
    ∃ e', e'[8]? = some parent ∧
      Sem.Star (semStep P)
        (State.mk mem context ({ fn, label := 1, pos := 0, env := e } :: rest)) 0
        (State.mk mem context ({ fn, label := 6, pos := 0, env := e' } :: rest)) := by
  refine ⟨?e, ?h8, ?hs⟩
  case hs =>
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hptr
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_4 (by env_lookup)) hcount) ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hneg
      (evalArgs1 (by arg_eval)) rfl rfl ?_
    exact .refl _
  case h8 => env_lookup

/-- A shared cell: its count word is decremented. -/
theorem decArr_step_shared {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    {mem mem' : Memory} {context cur parent count count' : Word} {e : Env}
    (he1 : e[1]? = some cur) (he2 : e[2]? = some parent)
    (hptr : Cond.holds .tnz .w64 cur 1 = false)
    (hcount : loadWord mem .w32 .zero (cur + 4) = some count)
    (hpos : Cond.holds .slt .w32 count 0 = false)
    (hne : Cond.holds .eq .w32 count 0 = false)
    (hsub : BinOp.eval .sub .w32 count 1 = some count')
    (hwr : mem.write? .w32 (cur + 4) count' = .ok mem') (rest : List Frame) :
    ∃ e', e'[8]? = some parent ∧
      Sem.Star (semStep P)
        (State.mk mem context ({ fn, label := 1, pos := 0, env := e } :: rest)) 0
        (State.mk mem' context ({ fn, label := 6, pos := 0, env := e' } :: rest)) := by
  refine ⟨?e, ?h8, ?hs⟩
  case hs =>
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hptr
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_4 (by env_lookup)) hcount) ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hpos
      (evalArgs_nil _) rfl rfl ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hne
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_bin_eval (by arg_eval) (by arg_eval) hsub) ?_
    refine star_store hfn rfl (by decide) rfl (cellAddr_eval_4 (by env_lookup)) (by arg_eval)
      hwr ?_
    refine star_jump_fwd hfn rfl rfl rfl rfl (evalArgs1 (by arg_eval)) rfl rfl ?_
    exact .refl _
  case h8 => env_lookup

/-- The last reference of a cell with nothing to scan (scan byte `0`): the cell is pushed on its
class's free list. -/
theorem decArr_step_leaf {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    {mem m1 m2 : Memory} {context cur parent count scan cls head : Word} {e : Env}
    (he1 : e[1]? = some cur) (he2 : e[2]? = some parent)
    (hptr : Cond.holds .tnz .w64 cur 1 = false)
    (hcount : loadWord mem .w32 .zero (cur + 4) = some count)
    (hpos : Cond.holds .slt .w32 count 0 = false)
    (hzero : Cond.holds .eq .w32 count 0 = true)
    (hscan : loadWord mem .w8 .zero cur = some scan)
    (hleaf : Cond.holds .eq .w64 scan 0 = true)
    (hcls : loadWord mem .w8 .zero (cur + 1) = some cls)
    (hhead : loadWord mem .w64 .zero (freeHeadAddress context cls) = some head)
    (hw1 : mem.write? .w64 cur head = .ok m1)
    (hw2 : m1.write? .w64 (freeHeadAddress context cls) cur = .ok m2) (rest : List Frame) :
    ∃ e', e'[8]? = some parent ∧
      Sem.Star (semStep P)
        (State.mk mem context ({ fn, label := 1, pos := 0, env := e } :: rest)) 1
        (State.mk m2 context ({ fn, label := 6, pos := 0, env := e' } :: rest)) := by
  refine ⟨?e, ?h8, ?hs⟩
  case hs =>
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hptr
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_4 (by env_lookup)) hcount) ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hpos
      (evalArgs_nil _) rfl rfl ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hzero
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr0_eval (by env_lookup)) hscan) ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hleaf
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_1 (by env_lookup)) hcls) ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (ctxHead_eval (by env_lookup)) hhead) ?_
    refine star_store hfn rfl (by decide) rfl (cellAddr0_eval (by env_lookup)) (by arg_eval)
      hw1 ?_
    refine star_store hfn rfl (by decide) rfl (ctxHead_eval (by env_lookup)) (by arg_eval)
      hw2 ?_
    refine star_jump_back hfn rfl rfl rfl rfl (evalArgs1 (by arg_eval)) rfl rfl ?_
    exact .refl _
  case h8 => env_lookup

/-- The last reference of an empty boxed array: recycled at once, like a cell with nothing to
scan. -/
theorem decArr_step_array_empty {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    {mem m1 m2 : Memory} {context cur parent count scan size cls head : Word} {e : Env}
    (he1 : e[1]? = some cur) (he2 : e[2]? = some parent)
    (hptr : Cond.holds .tnz .w64 cur 1 = false)
    (hcount : loadWord mem .w32 .zero (cur + 4) = some count)
    (hpos : Cond.holds .slt .w32 count 0 = false)
    (hzero : Cond.holds .eq .w32 count 0 = true)
    (hscan : loadWord mem .w8 .zero cur = some scan)
    (hnz : Cond.holds .eq .w64 scan 0 = false)
    (harr : Cond.holds .eq .w64 scan (UInt64.ofNat arrayScan) = true)
    (hsize : loadWord mem .w64 .zero (cur + 8) = some size)
    (hempty : Cond.holds .eq .w64 size 0 = true)
    (hcls : loadWord mem .w8 .zero (cur + 1) = some cls)
    (hhead : loadWord mem .w64 .zero (freeHeadAddress context cls) = some head)
    (hw1 : mem.write? .w64 cur head = .ok m1)
    (hw2 : m1.write? .w64 (freeHeadAddress context cls) cur = .ok m2) (rest : List Frame) :
    ∃ e', e'[8]? = some parent ∧
      Sem.Star (semStep P)
        (State.mk mem context ({ fn, label := 1, pos := 0, env := e } :: rest)) 2
        (State.mk m2 context ({ fn, label := 6, pos := 0, env := e' } :: rest)) := by
  refine ⟨?e, ?h8, ?hs⟩
  case hs =>
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hptr
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_4 (by env_lookup)) hcount) ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hpos
      (evalArgs_nil _) rfl rfl ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hzero
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr0_eval (by env_lookup)) hscan) ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hnz
      (evalArgs_nil _) rfl rfl ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) harr
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_8 (by env_lookup)) hsize) ?_
    refine star_br_true_back hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hempty
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_1 (by env_lookup)) hcls) ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (ctxHead_eval (by env_lookup)) hhead) ?_
    refine star_store hfn rfl (by decide) rfl (cellAddr0_eval (by env_lookup)) (by arg_eval)
      hw1 ?_
    refine star_store hfn rfl (by decide) rfl (ctxHead_eval (by env_lookup)) (by arg_eval)
      hw2 ?_
    refine star_jump_back hfn rfl rfl rfl rfl (evalArgs1 (by arg_eval)) rfl rfl ?_
    exact .refl _
  case h8 => env_lookup

/-- The last reference of a boxed array of `n + 1` elements: its last element becomes the current
value and the array the suspended parent; the parent link goes in the size word and `n`, the
elements still to visit, in the count word. -/
theorem decArr_step_array_detach {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    {mem m1 m2 : Memory} {context cur parent count scan x : Word} {n : Nat} {e : Env}
    (he1 : e[1]? = some cur) (he2 : e[2]? = some parent)
    (hptr : Cond.holds .tnz .w64 cur 1 = false)
    (hcount : loadWord mem .w32 .zero (cur + 4) = some count)
    (hpos : Cond.holds .slt .w32 count 0 = false)
    (hzero : Cond.holds .eq .w32 count 0 = true)
    (hscan : loadWord mem .w8 .zero cur = some scan)
    (hnz : Cond.holds .eq .w64 scan 0 = false)
    (harr : Cond.holds .eq .w64 scan (UInt64.ofNat arrayScan) = true)
    (hsize : loadWord mem .w64 .zero (cur + 8) = some (UInt64.ofNat (n + 1)))
    (hn : n + 1 < 2 ^ 60)
    (helem : loadWord mem .w64 .zero (cur + UInt64.ofNat (arrayPayloadOffset + 8 * n)) = some x)
    (hw1 : mem.write? .w64 (cur + 8) parent = .ok m1)
    (hw2 : m1.write? .w32 (cur + 4) (UInt64.ofNat n) = .ok m2) (rest : List Frame) :
    ∃ e', e'[1]? = some x ∧ e'[2]? = some cur ∧
      Sem.Star (semStep P)
        (State.mk mem context ({ fn, label := 1, pos := 0, env := e } :: rest)) 1
        (State.mk m2 context ({ fn, label := 1, pos := 0, env := e' } :: rest)) := by
  have hsz_ne : Cond.holds .eq .w64 (UInt64.ofNat (n + 1)) (UInt64.ofNat 0) = false := by
    rw [cond_eq_w64]
    exact beq_false_of_ne (fun h => by
      have := congrArg UInt64.toNat h
      rw [u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)] at this; omega)
  have hsub : BinOp.eval .sub .w64 (UInt64.ofNat (n + 1)) (UInt64.ofNat 1) =
      some (UInt64.ofNat n) := by
    simpa using binOp_sub64 (n + 1) 1 (by omega) (by omega)
  refine ⟨?e, ?h1, ?h2, ?hs⟩
  case hs =>
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hptr
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_4 (by env_lookup)) hcount) ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hpos
      (evalArgs_nil _) rfl rfl ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hzero
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr0_eval (by env_lookup)) hscan) ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hnz
      (evalArgs_nil _) rfl rfl ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) harr
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_8 (by env_lookup)) hsize) ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hsz_ne
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_bin_eval (by arg_eval) (by arg_eval) hsub) ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (wordElemAddr_eval (by env_lookup) (by env_lookup) (by omega)) helem) ?_
    refine star_store hfn rfl (by decide) rfl (cellAddr_eval_8 (by env_lookup)) (by arg_eval)
      hw1 ?_
    refine star_store hfn rfl (by decide) rfl (cellAddr_eval_4 (by env_lookup)) (by arg_eval)
      hw2 ?_
    refine star_jump_back hfn rfl rfl rfl rfl (evalArgs2 (by arg_eval) (by arg_eval)) rfl rfl ?_
    exact .refl _
  case h1 => env_lookup
  case h2 => env_lookup

/-- The last reference of a constructor cell (scan byte neither `0` nor `arrayScan`): its first
field becomes the current value and the cell the suspended parent; the parent link goes in the
first field and `scan − 1` in the count word. -/
theorem decArr_step_ctor_detach {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    {mem m1 m2 : Memory} {context cur parent count scan scan' first : Word} {e : Env}
    (he1 : e[1]? = some cur) (he2 : e[2]? = some parent)
    (hptr : Cond.holds .tnz .w64 cur 1 = false)
    (hcount : loadWord mem .w32 .zero (cur + 4) = some count)
    (hpos : Cond.holds .slt .w32 count 0 = false)
    (hzero : Cond.holds .eq .w32 count 0 = true)
    (hscan : loadWord mem .w8 .zero cur = some scan)
    (hnz : Cond.holds .eq .w64 scan 0 = false)
    (hctor : Cond.holds .eq .w64 scan (UInt64.ofNat arrayScan) = false)
    (hfirst : loadWord mem .w64 .zero (cur + 8) = some first)
    (hsub : BinOp.eval .sub .w64 scan 1 = some scan')
    (hw1 : mem.write? .w64 (cur + 8) parent = .ok m1)
    (hw2 : m1.write? .w32 (cur + 4) scan' = .ok m2) (rest : List Frame) :
    ∃ e', e'[1]? = some first ∧ e'[2]? = some cur ∧
      Sem.Star (semStep P)
        (State.mk mem context ({ fn, label := 1, pos := 0, env := e } :: rest)) 1
        (State.mk m2 context ({ fn, label := 1, pos := 0, env := e' } :: rest)) := by
  refine ⟨?e, ?h1, ?h2, ?hs⟩
  case hs =>
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hptr
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_4 (by env_lookup)) hcount) ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hpos
      (evalArgs_nil _) rfl rfl ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hzero
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr0_eval (by env_lookup)) hscan) ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hnz
      (evalArgs_nil _) rfl rfl ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hctor
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_8 (by env_lookup)) hfirst) ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_bin_eval (by arg_eval) (by arg_eval) hsub) ?_
    refine star_store hfn rfl (by decide) rfl (cellAddr_eval_8 (by env_lookup)) (by arg_eval)
      hw1 ?_
    refine star_store hfn rfl (by decide) rfl (cellAddr_eval_4 (by env_lookup)) (by arg_eval)
      hw2 ?_
    refine star_jump_back hfn rfl rfl rfl rfl (evalArgs2 (by arg_eval) (by arg_eval)) rfl rfl ?_
    exact .refl _
  case h1 => env_lookup
  case h2 => env_lookup

/-! ## Steps from the continuation (block 6) -/

/-- No suspended parent: the procedure is at its `ret`. -/
theorem decArr_step_finish {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    {mem : Memory} {context : Word} {e : Env} (he8 : e[8]? = some 0) (rest : List Frame) :
    Sem.Star (semStep P)
      (State.mk mem context ({ fn, label := 6, pos := 0, env := e } :: rest)) 0
      (State.mk mem context ({ fn, label := 10, pos := 0, env := e } :: rest)) := by
  refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) (by decide)
    (evalArgs_nil _) rfl rfl ?_
  exact .refl _

/-- A finished parent (count word `0`), array or constructor: it is pushed on its class's free
list and its predecessor, read from the word at offset 8, is resumed. -/
theorem decArr_step_recycle {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    {mem m1 m2 : Memory} {context p scan cls pred head : Word} {e : Env}
    (he8 : e[8]? = some p) (hp : p ≠ 0)
    (hrem : loadWord mem .w32 .zero (p + 4) = some 0)
    (hscan : loadWord mem .w8 .zero p = some scan)
    (hcls : loadWord mem .w8 .zero (p + 1) = some cls)
    (hpred : loadWord mem .w64 .zero (p + 8) = some pred)
    (hhead : loadWord mem .w64 .zero (freeHeadAddress context cls) = some head)
    (hw1 : mem.write? .w64 p head = .ok m1)
    (hw2 : m1.write? .w64 (freeHeadAddress context cls) p = .ok m2) (rest : List Frame) :
    ∃ e', e'[8]? = some pred ∧
      Sem.Star (semStep P)
        (State.mk mem context ({ fn, label := 6, pos := 0, env := e } :: rest)) 1
        (State.mk m2 context ({ fn, label := 6, pos := 0, env := e' } :: rest)) := by
  have hne0 : Cond.holds .eq .w64 p (UInt64.ofNat 0) = false := by
    rw [cond_eq_w64]; exact beq_false_of_ne hp
  refine ⟨?e, ?h8, ?hs⟩
  case hs =>
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hne0
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_4 (by env_lookup)) hrem) ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr0_eval (by env_lookup)) hscan) ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) (by decide)
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_1 (by env_lookup)) hcls) ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_8 (by env_lookup)) hpred) ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (ctxHead_eval (by env_lookup)) hhead) ?_
    refine star_store hfn rfl (by decide) rfl (cellAddr0_eval (by env_lookup)) (by arg_eval)
      hw1 ?_
    refine star_store hfn rfl (by decide) rfl (ctxHead_eval (by env_lookup)) (by arg_eval)
      hw2 ?_
    refine star_jump_back hfn rfl rfl rfl rfl (evalArgs1 (by arg_eval)) rfl rfl ?_
    exact .refl _
  case h8 => env_lookup

/-- A suspended boxed array with `r + 1` elements left: element `r` becomes the current value and
`r` the count word. -/
theorem decArr_step_array_next {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    {mem m1 : Memory} {context p x : Word} {r : Nat} {e : Env}
    (he8 : e[8]? = some p) (hp : p ≠ 0)
    (hrem : loadWord mem .w32 .zero (p + 4) = some (UInt64.ofNat (r + 1)))
    (hr : r + 1 < 2 ^ 60)
    (hscan : loadWord mem .w8 .zero p = some (UInt64.ofNat arrayScan))
    (helem : loadWord mem .w64 .zero (p + UInt64.ofNat (arrayPayloadOffset + 8 * r)) = some x)
    (hw : mem.write? .w32 (p + 4) (UInt64.ofNat r) = .ok m1) (rest : List Frame) :
    ∃ e', e'[1]? = some x ∧ e'[2]? = some p ∧
      Sem.Star (semStep P)
        (State.mk mem context ({ fn, label := 6, pos := 0, env := e } :: rest)) 1
        (State.mk m1 context ({ fn, label := 1, pos := 0, env := e' } :: rest)) := by
  have hne0 : Cond.holds .eq .w64 p (UInt64.ofNat 0) = false := by
    rw [cond_eq_w64]; exact beq_false_of_ne hp
  have hrem_ne : Cond.holds .eq .w64 (UInt64.ofNat (r + 1)) (UInt64.ofNat 0) = false := by
    rw [cond_eq_w64]
    exact beq_false_of_ne (fun h => by
      have := congrArg UInt64.toNat h
      rw [u64_toNat_ofNat_lt (by omega), u64_toNat_ofNat_lt (by decide)] at this; omega)
  have hsub : BinOp.eval .sub .w64 (UInt64.ofNat (r + 1)) (UInt64.ofNat 1) =
      some (UInt64.ofNat r) := by
    simpa using binOp_sub64 (r + 1) 1 (by omega) (by omega)
  refine ⟨?e, ?h1, ?h2, ?hs⟩
  case hs =>
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hne0
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_4 (by env_lookup)) hrem) ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr0_eval (by env_lookup)) hscan) ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hrem_ne
      (evalArgs_nil _) rfl rfl ?_
    refine star_br_true_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) (by decide)
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_bin_eval (by arg_eval) (by arg_eval) hsub) ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (wordElemAddr_eval (by env_lookup) (by env_lookup) (by omega)) helem) ?_
    refine star_store hfn rfl (by decide) rfl (cellAddr_eval_4 (by env_lookup)) (by arg_eval)
      hw ?_
    refine star_jump_back hfn rfl rfl rfl rfl (evalArgs2 (by arg_eval) (by arg_eval)) rfl rfl ?_
    exact .refl _
  case h1 => env_lookup
  case h2 => env_lookup

/-- A suspended constructor with `rem ≠ 0` fields left: field `scan − rem` becomes the current
value and `rem − 1` the count word. -/
theorem decArr_step_ctor_next {P : Program} {fn : FunId} (hfn : P.funcs[fn]? = some decArr)
    {mem m1 : Memory} {context p rem scan idx x rem' : Word} {e : Env}
    (he8 : e[8]? = some p) (hp : p ≠ 0)
    (hrem : loadWord mem .w32 .zero (p + 4) = some rem)
    (hscan : loadWord mem .w8 .zero p = some scan)
    (hmore : Cond.holds .eq .w64 rem 0 = false)
    (hctor : Cond.holds .eq .w64 scan (UInt64.ofNat arrayScan) = false)
    (hidx : BinOp.eval .sub .w64 scan rem = some idx)
    (hfield : loadWord mem .w64 .zero (p + idx * 8 + dispWord 8) = some x)
    (hsub : BinOp.eval .sub .w64 rem 1 = some rem')
    (hw : mem.write? .w32 (p + 4) rem' = .ok m1) (rest : List Frame) :
    ∃ e', e'[1]? = some x ∧ e'[2]? = some p ∧
      Sem.Star (semStep P)
        (State.mk mem context ({ fn, label := 6, pos := 0, env := e } :: rest)) 1
        (State.mk m1 context ({ fn, label := 1, pos := 0, env := e' } :: rest)) := by
  have hne0 : Cond.holds .eq .w64 p (UInt64.ofNat 0) = false := by
    rw [cond_eq_w64]; exact beq_false_of_ne hp
  refine ⟨?e, ?h1, ?h2, ?hs⟩
  case hs =>
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hne0
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_4 (by env_lookup)) hrem) ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (cellAddr0_eval (by env_lookup)) hscan) ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hmore
      (evalArgs_nil _) rfl rfl ?_
    refine star_br_false_fwd hfn rfl rfl rfl rfl (by arg_eval) (by arg_eval) hctor
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_bin_eval (by arg_eval) (by arg_eval) hidx) ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_load_eval (scaledAddr_eval (by env_lookup) (by env_lookup)) hfield) ?_
    refine star_assign hfn rfl (by decide) rfl
      (rhs_bin_eval (by arg_eval) (by arg_eval) hsub) ?_
    refine star_store hfn rfl (by decide) rfl (cellAddr_eval_4 (by env_lookup)) (by arg_eval)
      hw ?_
    refine star_jump_back hfn rfl rfl rfl rfl (evalArgs2 (by arg_eval) (by arg_eval)) rfl rfl ?_
    exact .refl _
  case h1 => env_lookup
  case h2 => env_lookup

end IxCC.Rt.Rc.Array
