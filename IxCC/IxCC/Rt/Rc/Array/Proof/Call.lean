import IxCC.Rt.Rc.Array.Proof.Exec
import IxCC.Rt.Rc.Array.Proof.Classes
import IxCC.Rt.Rc.Array.Cell

/-! # Calls, as specifications

A procedure's specification is a *return*: `Returns0 P fn env mem ctx c mem'` says that `P`'s
function `fn`, entered with registers `env` above any suspended caller that awaits no result,
returns to that caller after `c` charges with memory `mem'`; `Returns1` is the same for one
result, which the caller's destination register receives. Nothing in either names a function
table: a specification holds in every program that has the procedure at `fn` (and its callees at
theirs).

A call statement in a caller then steps over the whole callee (`star_call0`, `star_call1`), so a
path through a procedure that calls others is one `refine` per statement, as for any other.

Here also: the specification of the increment `Rt.Rc.Procs.inc` on any value (`IncStep`: the
three cases it returns from), of a run of increments over a list (`IncAll`), and of the two size
class procedures as returns. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Rc (maxClass classWords maxCellWords maxCount)
open IxCC.Rt.Rc.Procs (v i to cellAddr)
open IxCC.X86 (Memory)

/-- `fn` returns to a caller that awaits no result, after `c` charges, with memory `mem'`. -/
def Returns0 (P : Program) (fn : FunId) (env : Env) (mem : Memory) (ctx : Word) (c : Nat)
    (mem' : Memory) : Prop :=
  ∀ (caller : Frame) (callers : List Frame), caller.dsts = [] →
    Sem.Star (semStep P) (State.mk mem ctx ({ fn, label := 0, pos := 0, env } :: caller :: callers)) c
      (State.mk mem' ctx (caller :: callers))

/-- `fn` returns `res` to a caller that awaits one result, after `c` charges, with memory `mem'`. -/
def Returns1 (P : Program) (fn : FunId) (env : Env) (mem : Memory) (ctx : Word) (c : Nat)
    (res : Word) (mem' : Memory) : Prop :=
  ∀ (caller : Frame) (callers : List Frame) (dst : VReg), caller.dsts = [dst] →
    Sem.Star (semStep P) (State.mk mem ctx ({ fn, label := 0, pos := 0, env } :: caller :: callers)) c
      (State.mk mem' ctx ({ caller with env := caller.env.insert dst res, dsts := [] } :: callers))

/-- A call of a procedure that returns nothing steps over it. -/
theorem star_call0 {p : Program} {fn lbl pos : Nat} {f gFunc : Func} {blk : Block}
    {g : FunId} {args : List Arg} {vals : List Word} {env calleeEnv : Env} {mem mem' : Memory}
    {context : Word} {rest : List Frame} {c c' : Nat} {s : State}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos < blk.body.size) (hst : blk.body[pos]'hpos = .call [] g args)
    (hargs : evalArgs env args = some vals)
    (hg : p.funcs[g]? = some gFunc)
    (hbind : bindParams {} gFunc.params vals = some calleeEnv)
    (hcall : Returns0 p g calleeEnv mem context c mem')
    (hk : Sem.Star (semStep p)
      (State.mk mem' context ({ fn, label := lbl, pos := pos + 1, env } :: rest)) c' s) :
    Sem.Star (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest))
      (c + c' + 1) s :=
  star_call hf hb hpos hst hargs hg hbind ((hcall { fn, label := lbl, pos := pos + 1, env } rest rfl).trans hk)

/-- A call of a procedure that returns one result steps over it, binding the result. -/
theorem star_call1 {p : Program} {fn lbl pos : Nat} {f gFunc : Func} {blk : Block}
    {dst : VReg} {g : FunId} {args : List Arg} {vals : List Word} {env calleeEnv : Env}
    {mem mem' : Memory} {context res : Word} {rest : List Frame} {c c' : Nat} {s : State}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos < blk.body.size) (hst : blk.body[pos]'hpos = .call [dst] g args)
    (hargs : evalArgs env args = some vals)
    (hg : p.funcs[g]? = some gFunc)
    (hbind : bindParams {} gFunc.params vals = some calleeEnv)
    (hcall : Returns1 p g calleeEnv mem context c res mem')
    (hk : Sem.Star (semStep p)
      (State.mk mem' context ({ fn, label := lbl, pos := pos + 1, env := env.insert dst res } :: rest))
        c' s) :
    Sem.Star (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest))
      (c + c' + 1) s :=
  star_call hf hb hpos hst hargs hg hbind
    ((hcall { fn, label := lbl, pos := pos + 1, env, dsts := [dst] } rest dst rfl).trans hk)

/-- A `ret []` is a return. -/
theorem returns0_of_star {P : Program} {fn : FunId} {f : Func} {blk : Block} {lbl : Nat}
    {env env' : Env} {mem mem' : Memory} {ctx : Word} {c : Nat}
    (hf : P.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk) (ht : blk.term = .ret [])
    (hrun : ∀ rest : List Frame, Sem.Star (semStep P)
      (State.mk mem ctx ({ fn, label := 0, pos := 0, env } :: rest)) c
      (State.mk mem' ctx ({ fn, label := lbl, pos := blk.body.size, env := env' } :: rest))) :
    Returns0 P fn env mem ctx c mem' := by
  intro caller callers hd
  have h := (hrun (caller :: callers)).trans (star_ret_zero (env := env') (mem := mem') (context := ctx)
    (callers := callers) hf hb rfl ht hd)
  simpa using h

/-- A `ret [a]` is a return. -/
theorem returns1_of_star {P : Program} {fn : FunId} {f : Func} {blk : Block} {lbl : Nat}
    {a : Arg} {env env' : Env} {mem mem' : Memory} {ctx res : Word} {c : Nat}
    (hf : P.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk) (ht : blk.term = .ret [a])
    (ha : a.eval env' = some res)
    (hrun : ∀ rest : List Frame, Sem.Star (semStep P)
      (State.mk mem ctx ({ fn, label := 0, pos := 0, env } :: rest)) c
      (State.mk mem' ctx ({ fn, label := lbl, pos := blk.body.size, env := env' } :: rest))) :
    Returns1 P fn env mem ctx c res mem' := by
  intro caller callers dst hd
  have h := (hrun (caller :: callers)).trans (star_ret_one (env := env') (mem := mem')
    (context := ctx) (callers := callers) hf hb rfl ht ha hd)
  simpa using h

theorem Returns0.cast {P : Program} {fn : FunId} {env : Env} {mem mem' : Memory} {ctx : Word}
    {c c' : Nat} (h : Returns0 P fn env mem ctx c mem') (hc : c = c') :
    Returns0 P fn env mem ctx c' mem' := hc ▸ h

theorem Returns1.cast {P : Program} {fn : FunId} {env : Env} {mem mem' : Memory} {ctx res : Word}
    {c c' : Nat} (h : Returns1 P fn env mem ctx c res mem') (hc : c = c') :
    Returns1 P fn env mem ctx c' res mem' := hc ▸ h

/-! ## The size-class procedures -/

theorem classFor_returns {P : Program} {fn : FunId} (hf : P.funcs[fn]? = some arrClassFor)
    (mem : Memory) (ctx : Word) {w : Nat} (h1 : 1 ≤ w) (h2 : w ≤ maxCellWords) :
    Returns1 P fn (({} : Env).insert 0 (UInt64.ofNat w)) mem ctx 0
      (UInt64.ofNat (classForFast w)) mem :=
  fun caller callers _dst hd => arrClassFor_call_star hf (mem := mem) (context := ctx)
    (caller := caller) (tail := callers) hd h1 h2

theorem classWords_returns {P : Program} {fn : FunId} (hf : P.funcs[fn]? = some arrClassWords)
    (mem : Memory) (ctx : Word) {c : Nat} (h1 : 1 ≤ c) (h2 : c ≤ maxClass) :
    Returns1 P fn (({} : Env).insert 0 (UInt64.ofNat c)) mem ctx 0
      (UInt64.ofNat (classWords c)) mem :=
  fun caller callers _dst hd => arrClassWords_call_star hf (mem := mem) (context := ctx)
    (caller := caller) (tail := callers) hd h1 h2

/-! ## The increment -/

/-- The registers of `rt_rc_inc` at its entry. -/
def incEnv (x : Word) : Env := ({} : Env).insert 0 x

/-- What the increment does to memory when it returns: an immediate or a static cell (negative
count word) is left alone; a dynamic cell whose count is not saturated has it raised by one. (On a
saturated count it fails with a resource error instead.) -/
def IncStep (mem : Memory) (x : Word) (mem' : Memory) : Prop :=
  (Cond.holds .tnz .w64 x 1 = true ∧ mem' = mem) ∨
  (∃ cnt, Cond.holds .tnz .w64 x 1 = false ∧ loadWord mem .w32 .zero (x + 4) = some cnt ∧
    Cond.holds .slt .w32 cnt 0 = true ∧ mem' = mem) ∨
  (∃ cnt cnt', Cond.holds .tnz .w64 x 1 = false ∧ loadWord mem .w32 .zero (x + 4) = some cnt ∧
    Cond.holds .slt .w32 cnt 0 = false ∧
    Cond.holds .eq .w32 cnt (UInt64.ofNat (maxCount - 1)) = false ∧
    BinOp.eval .add .w32 cnt 1 = some cnt' ∧ mem.write? .w32 (x + 4) cnt' = .ok mem')

/-- `rt_rc_inc` returns as `IncStep` says, in zero charges. -/
theorem inc_returns {P : Program} {fn : FunId} (hf : P.funcs[fn]? = some IxCC.Rt.Rc.Procs.inc)
    {mem mem' : Memory} {ctx x : Word} (h : IncStep mem x mem') :
    Returns0 P fn (incEnv x) mem ctx 0 mem' := by
  intro caller callers hd
  unfold incEnv
  rcases h with ⟨himm, rfl⟩ | ⟨cnt, hptr, hcnt, hneg, rfl⟩ | ⟨cnt, cnt', hptr, hcnt, hpos, hne, hadd, hwr⟩
  · refine star_br_true_fwd hf rfl rfl rfl rfl (by arg_eval) (by arg_eval) himm
      (evalArgs_nil _) rfl rfl ?_
    exact star_ret_zero hf rfl rfl rfl hd
  · refine star_br_false_fwd hf rfl rfl rfl rfl (by arg_eval) (by arg_eval) hptr
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hf rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_4 (by env_lookup)) hcnt) ?_
    refine star_br_true_fwd hf rfl rfl rfl rfl (by arg_eval) (by arg_eval) hneg
      (evalArgs_nil _) rfl rfl ?_
    exact star_ret_zero hf rfl rfl rfl hd
  · refine star_br_false_fwd hf rfl rfl rfl rfl (by arg_eval) (by arg_eval) hptr
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hf rfl (by decide) rfl
      (rhs_load_eval (cellAddr_eval_4 (by env_lookup)) hcnt) ?_
    refine star_br_false_fwd hf rfl rfl rfl rfl (by arg_eval) (by arg_eval) hpos
      (evalArgs_nil _) rfl rfl ?_
    refine star_br_false_fwd hf rfl rfl rfl rfl (by arg_eval) (by arg_eval) hne
      (evalArgs_nil _) rfl rfl ?_
    refine star_assign hf rfl (by decide) rfl (rhs_bin_eval (by arg_eval) (by arg_eval) hadd) ?_
    refine star_store hf rfl (by decide) rfl (cellAddr_eval_4 (by env_lookup)) (by arg_eval)
      hwr ?_
    refine star_jump_fwd hf rfl rfl rfl rfl (evalArgs_nil _) rfl rfl ?_
    exact star_ret_zero hf rfl rfl rfl hd

/-- A store that succeeds is the plain write. -/
theorem write?_eq {m m' : Memory} {w : X86.Width} {a v : Word} (h : m.write? w a v = .ok m') :
    m' = m.write w a v := by
  unfold Memory.write? at h
  split at h
  · cases h; rfl
  · cases h

/-- A run of increments, one per element of the list, in order. -/
inductive IncAll : Memory → List Word → Memory → Prop
  | nil (mem : Memory) : IncAll mem [] mem
  | cons {mem mem1 mem2 : Memory} {x : Word} {xs : List Word} :
      IncStep mem x mem1 → IncAll mem1 xs mem2 → IncAll mem (x :: xs) mem2

theorem IncAll.append {m1 m2 m3 : Memory} {xs ys : List Word} (h1 : IncAll m1 xs m2)
    (h2 : IncAll m2 ys m3) : IncAll m1 (xs ++ ys) m3 := by
  induction h1 with
  | nil => exact h2
  | cons hs _ ih => exact .cons hs (ih h2)

/-- A list of immediates needs no increment. -/
theorem IncAll.immediates (mem : Memory) {xs : List Word}
    (h : ∀ x ∈ xs, Cond.holds .tnz .w64 x 1 = true) : IncAll mem xs mem := by
  induction xs with
  | nil => exact .nil mem
  | cons x xs ih =>
    exact .cons (Or.inl ⟨h x (by simp), rfl⟩) (ih (fun y hy => h y (by simp [hy])))

/-- The bytes an increment of a dynamic cell writes: its count word. -/
def CountWords (xs : List Word) : Nat → Prop :=
  fun a => ∃ x ∈ xs, Cond.holds .tnz .w64 x 1 = false ∧ x.toNat + 4 ≤ a ∧ a < x.toNat + 8

/-- A run of increments touches only the count words of the pointers among the elements. -/
theorem IncAll.frame {mem mem' : Memory} {xs : List Word} (h : IncAll mem xs mem')
    (hfit : ∀ x ∈ xs, Cond.holds .tnz .w64 x 1 = false → x.toNat + 8 ≤ 2 ^ 64) :
    MemFrame mem mem' (CountWords xs) := by
  induction h with
  | nil m => exact MemFrame.refl m _
  | @cons m m1 m2 x xs hs _ ih =>
    have ih' := ih (fun y hy hp => hfit y (by simp [hy]) hp)
    have hmono : ∀ k, CountWords xs k → CountWords (x :: xs) k := by
      intro k ⟨y, hy, hp, h1, h2⟩; exact ⟨y, by simp [hy], hp, h1, h2⟩
    have hstep : MemFrame m m1 (CountWords (x :: xs)) := by
      rcases hs with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨cnt, cnt', hptr, _, _, _, _, hwr⟩
      · exact MemFrame.refl _ _
      · exact MemFrame.refl _ _
      · have hx := hfit x (by simp) hptr
        have h4 : (x + 4).toNat = x.toNat + 4 := IxCC.Rt.Rc.Procs.countAddress hx
        rw [write?_eq hwr]
        exact (MemFrame.write m .w32 (x + 4) cnt' (by rw [h4]; simp [X86.Width.bytes]; omega)).mono
          (fun k hk => ⟨x, by simp, hptr, by unfold Span at hk; rw [h4] at hk; omega,
            by unfold Span at hk; rw [h4] at hk; simp [X86.Width.bytes] at hk; omega⟩)
    exact hstep.trans (ih'.mono hmono)

end IxCC.Rt.Rc.Array
