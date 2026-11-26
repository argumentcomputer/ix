import IxCC.Rt.Rc.Array.Proof.StepLemmas

/-! # Goal-directed Lir stepping for runtime-procedure proofs

`StepLemmas` gives one equation `semStep p s = .next s' c` per statement form. This module turns
each into a rule on a goal `Sem.Star (semStep p) s c final`: the rule consumes the step at the head
of `s` and leaves the run from the next state, whose registers and memory are found by unification.
A path through a procedure is then one `refine` per statement, in any ambient program `p` and
above any suspended stack `rest`: nothing here mentions a particular function table.

A forward edge is free and a backward edge costs one charge (`Lir.Semantics`), so each edge rule
has a `_fwd` and a `_back` form; the `_back` forms and `star_call` leave a goal at charge `c` for a
goal at `c + 1`.

Side goals are discharged by three small tactics: `env_lookup` (a register in a chain of inserts),
`arg_eval` (an argument) and `eval_args` (an edge's or a call's argument list). -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open Lir
open IxCC.Rt.Rc.Procs (v i to cellAddr)
open IxCC.X86 (Memory)

/-! ## Registers and arguments -/

/-- A statement position inside a block whose body is a literal array (possibly with free
variables in its statements): the size computes. -/
macro "body_pos" : tactic => `(tactic| exact Nat.le_of_ble_eq_true rfl)

theorem env_get_insert_ne' {ρ : Env} {k k' : VReg} {val : Word} {r : Option Word}
    (hne : (k == k') = false) (h : ρ[k']? = r) : (ρ.insert k val)[k']? = r := by
  rw [← h]
  simp [Std.HashMap.getElem?_insert, hne]

theorem env_get_insert_self' {ρ : Env} {k : VReg} {val : Word} :
    (ρ.insert k val)[k]? = some val := by
  simp

/-- Look a register up in a chain of `insert`s ending in a hypothesis or in the newest binding. -/
syntax "env_lookup" : tactic
macro_rules
  | `(tactic| env_lookup) =>
    `(tactic| first
        | with_reducible exact env_get_insert_self'
        | with_reducible assumption
        | (with_reducible refine env_get_insert_ne' ?hne ?_
           case hne => decide
           env_lookup))

/-- A register argument. The result is a variable `r` (not `some w`) so that a goal whose value is
still a metavariable assigns nothing new on our side. -/
theorem arg_v {ρ : Env} {x : VReg} {r : Option Word} (h : ρ[x]? = r) : (v x).eval ρ = r := h

theorem arg_i {ρ : Env} {n : Nat} {r : Option Word} (h : some (UInt64.ofNat n) = r) :
    (i n).eval ρ = r := h

theorem arg_imm {ρ : Env} {w : Word} {r : Option Word} (h : some w = r) :
    (Arg.imm w).eval ρ = r := h

theorem arg_var {ρ : Env} {x : VReg} {r : Option Word} (h : ρ[x]? = r) : (Arg.v x).eval ρ = r := h

/-- Evaluate one argument: a register or an immediate. The argument's form is matched
syntactically (so a failed lookup never unfolds the register map); an immediate's value is then
compared up to unfolding (`UInt64.ofNat 1` against `1`). -/
syntax "arg_eval" : tactic
macro_rules
  | `(tactic| arg_eval) =>
    `(tactic| first
        | ((with_reducible refine arg_v ?_); env_lookup)
        | ((with_reducible refine arg_var ?_); env_lookup)
        | ((with_reducible refine arg_i ?_); exact rfl)
        | ((with_reducible refine arg_imm ?_); exact rfl))

theorem evalArgs_nil (ρ : Env) : evalArgs ρ [] = some [] := rfl

theorem evalArgs_cons {ρ : Env} {a : Arg} {as : List Arg} {va : Word} {vs : List Word}
    (ha : a.eval ρ = some va) (hr : evalArgs ρ as = some vs) :
    evalArgs ρ (a :: as) = some (va :: vs) := by
  simp only [evalArgs] at hr ⊢
  simp [List.mapM_cons, ha, hr]

theorem evalArgs1 {ρ : Env} {a : Arg} {va : Word} (ha : a.eval ρ = some va) :
    evalArgs ρ [a] = some [va] :=
  evalArgs_cons ha (evalArgs_nil _)

theorem evalArgs2 {ρ : Env} {a b : Arg} {va vb : Word}
    (ha : a.eval ρ = some va) (hb : b.eval ρ = some vb) :
    evalArgs ρ [a, b] = some [va, vb] :=
  evalArgs_cons ha (evalArgs1 hb)

theorem evalArgs3 {ρ : Env} {a b c : Arg} {va vb vc : Word}
    (ha : a.eval ρ = some va) (hb : b.eval ρ = some vb) (hc : c.eval ρ = some vc) :
    evalArgs ρ [a, b, c] = some [va, vb, vc] :=
  evalArgs_cons ha (evalArgs2 hb hc)

theorem evalArgs5 {ρ : Env} {a b c d e : Arg} {va vb vc vd ve : Word}
    (ha : a.eval ρ = some va) (hb : b.eval ρ = some vb) (hc : c.eval ρ = some vc)
    (hd : d.eval ρ = some vd) (he : e.eval ρ = some ve) :
    evalArgs ρ [a, b, c, d, e] = some [va, vb, vc, vd, ve] :=
  evalArgs_cons ha (evalArgs_cons hb (evalArgs3 hc hd he))

/-- Evaluate an argument list. -/
syntax "eval_args" : tactic
macro_rules
  | `(tactic| eval_args) =>
    `(tactic| first
        | exact evalArgs_nil _
        | (refine evalArgs_cons (by arg_eval) ?_; eval_args))

theorem rhs_arg_eval {env : Env} {mem : Memory} {ctx val : Word} {a : Arg}
    (ha : a.eval env = some val) : Rhs.eval env mem ctx (.arg a) = some val := by
  simp only [Rhs.eval, ha]

theorem rhs_select_eval {env : Env} {mem : Memory} {ctx va vb vt vf : Word} {c : Cond} {w : Width}
    {a b t f : Arg} (ha : a.eval env = some va) (hb : b.eval env = some vb)
    (ht : t.eval env = some vt) (hf : f.eval env = some vf) :
    Rhs.eval env mem ctx (.select c w a b t f) = some (if c.holds w va vb then vt else vf) := by
  simp only [Rhs.eval, ha, hb, ht, hf, bind, Option.bind]

/-! ## Charges -/

theorem star_cast {p : Program} {s s' : State} {c c' : Nat}
    (h : Sem.Star (semStep p) s c s') (hc : c = c') : Sem.Star (semStep p) s c' s' := hc ▸ h

/-! ## Statements -/

theorem star_assign {p : Program} {fn lbl pos : Nat} {f : Func} {blk : Block}
    {dst : VReg} {rhs : Rhs} {val : Word} {env : Env} {mem : Memory} {context : Word}
    {rest : List Frame} {c : Nat} {s : State}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos < blk.body.size) (hst : blk.body[pos]'hpos = .assign dst rhs)
    (hrhs : rhs.eval env mem context = some val)
    (hk : Sem.Star (semStep p)
      (State.mk mem context ({ fn, label := lbl, pos := pos + 1, env := env.insert dst val } :: rest))
      c s) :
    Sem.Star (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) c s :=
  .free (step_assign hf hb hpos hst hrhs) hk

theorem star_store {p : Program} {fn lbl pos : Nat} {f : Func} {blk : Block}
    {w : Width} {m : Addr} {a : Arg} {addr val : Word} {env : Env} {mem mem' : Memory}
    {context : Word} {rest : List Frame} {c : Nat} {s : State}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos < blk.body.size) (hst : blk.body[pos]'hpos = .store w m a)
    (hm : m.eval env context = some addr) (ha : a.eval env = some val)
    (hwr : mem.write? w addr val = .ok mem')
    (hk : Sem.Star (semStep p)
      (State.mk mem' context ({ fn, label := lbl, pos := pos + 1, env } :: rest)) c s) :
    Sem.Star (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) c s :=
  .free (step_store hf hb hpos hst hm ha hwr) hk

/-- A call: the callee's activation runs above the suspended caller, whose `dsts` await its
results. One charge. -/
theorem star_call {p : Program} {fn lbl pos : Nat} {f gFunc : Func} {blk : Block}
    {dsts : List VReg} {g : FunId} {args : List Arg} {vals : List Word}
    {env calleeEnv : Env} {mem : Memory} {context : Word} {rest : List Frame} {c : Nat} {s : State}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos < blk.body.size) (hst : blk.body[pos]'hpos = .call dsts g args)
    (hargs : evalArgs env args = some vals)
    (hg : p.funcs[g]? = some gFunc)
    (hbind : bindParams {} gFunc.params vals = some calleeEnv)
    (hk : Sem.Star (semStep p)
      (State.mk mem context
        ({ fn := g, label := 0, pos := 0, env := calleeEnv } ::
          { fn, label := lbl, pos := pos + 1, env, dsts } :: rest)) c s) :
    Sem.Star (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) (c + 1) s :=
  .charge (step_call hf hb hpos hst hargs hg hbind) hk

/-! ## Edges -/

theorem star_jump_fwd {p : Program} {fn lbl pos : Nat} {f : Func} {blk target : Block}
    {edge : Edge} {vals : List Word} {env env' : Env} {mem : Memory} {context : Word}
    {rest : List Frame} {c : Nat} {s : State}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .jump edge)
    (hdir : decide (edge.target ≤ lbl) = false)
    (hargs : evalArgs env edge.args = some vals)
    (htgt : f.blocks[edge.target]? = some target)
    (hbind : bindParams env target.params vals = some env')
    (hk : Sem.Star (semStep p)
      (State.mk mem context ({ fn, label := edge.target, pos := 0, env := env' } :: rest)) c s) :
    Sem.Star (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) c s := by
  subst hpos
  have h := step_jump (rest := rest) (mem := mem) (context := context) hf hb ht hargs htgt hbind
  rw [hdir] at h
  exact .free h hk

theorem star_jump_back {p : Program} {fn lbl pos : Nat} {f : Func} {blk target : Block}
    {edge : Edge} {vals : List Word} {env env' : Env} {mem : Memory} {context : Word}
    {rest : List Frame} {c : Nat} {s : State}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .jump edge)
    (hdir : decide (edge.target ≤ lbl) = true)
    (hargs : evalArgs env edge.args = some vals)
    (htgt : f.blocks[edge.target]? = some target)
    (hbind : bindParams env target.params vals = some env')
    (hk : Sem.Star (semStep p)
      (State.mk mem context ({ fn, label := edge.target, pos := 0, env := env' } :: rest)) c s) :
    Sem.Star (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) (c + 1) s := by
  subst hpos
  have h := step_jump (rest := rest) (mem := mem) (context := context) hf hb ht hargs htgt hbind
  rw [hdir] at h
  exact .charge h hk

theorem star_br_true_fwd {p : Program} {fn lbl pos : Nat} {f : Func} {blk target : Block}
    {cnd : Cond} {w : Width} {a b : Arg} {t e : Edge} {va vb : Word} {vals : List Word}
    {env env' : Env} {mem : Memory} {context : Word} {rest : List Frame} {c : Nat} {s : State}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .br cnd w a b t e)
    (hdir : decide (t.target ≤ lbl) = false)
    (ha : a.eval env = some va) (hbv : b.eval env = some vb)
    (hc : cnd.holds w va vb = true)
    (hargs : evalArgs env t.args = some vals)
    (htgt : f.blocks[t.target]? = some target)
    (hbind : bindParams env target.params vals = some env')
    (hk : Sem.Star (semStep p)
      (State.mk mem context ({ fn, label := t.target, pos := 0, env := env' } :: rest)) c s) :
    Sem.Star (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) c s := by
  subst hpos
  have h := step_br_true (rest := rest) (mem := mem) (context := context) hf hb ht ha hbv hc hargs
    htgt hbind
  rw [hdir] at h
  exact .free h hk

theorem star_br_true_back {p : Program} {fn lbl pos : Nat} {f : Func} {blk target : Block}
    {cnd : Cond} {w : Width} {a b : Arg} {t e : Edge} {va vb : Word} {vals : List Word}
    {env env' : Env} {mem : Memory} {context : Word} {rest : List Frame} {c : Nat} {s : State}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .br cnd w a b t e)
    (hdir : decide (t.target ≤ lbl) = true)
    (ha : a.eval env = some va) (hbv : b.eval env = some vb)
    (hc : cnd.holds w va vb = true)
    (hargs : evalArgs env t.args = some vals)
    (htgt : f.blocks[t.target]? = some target)
    (hbind : bindParams env target.params vals = some env')
    (hk : Sem.Star (semStep p)
      (State.mk mem context ({ fn, label := t.target, pos := 0, env := env' } :: rest)) c s) :
    Sem.Star (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) (c + 1) s := by
  subst hpos
  have h := step_br_true (rest := rest) (mem := mem) (context := context) hf hb ht ha hbv hc hargs
    htgt hbind
  rw [hdir] at h
  exact .charge h hk

theorem star_br_false_fwd {p : Program} {fn lbl pos : Nat} {f : Func} {blk target : Block}
    {cnd : Cond} {w : Width} {a b : Arg} {t e : Edge} {va vb : Word} {vals : List Word}
    {env env' : Env} {mem : Memory} {context : Word} {rest : List Frame} {c : Nat} {s : State}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .br cnd w a b t e)
    (hdir : decide (e.target ≤ lbl) = false)
    (ha : a.eval env = some va) (hbv : b.eval env = some vb)
    (hc : cnd.holds w va vb = false)
    (hargs : evalArgs env e.args = some vals)
    (htgt : f.blocks[e.target]? = some target)
    (hbind : bindParams env target.params vals = some env')
    (hk : Sem.Star (semStep p)
      (State.mk mem context ({ fn, label := e.target, pos := 0, env := env' } :: rest)) c s) :
    Sem.Star (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) c s := by
  subst hpos
  have h := step_br_false (rest := rest) (mem := mem) (context := context) hf hb ht ha hbv hc hargs
    htgt hbind
  rw [hdir] at h
  exact .free h hk

theorem star_br_false_back {p : Program} {fn lbl pos : Nat} {f : Func} {blk target : Block}
    {cnd : Cond} {w : Width} {a b : Arg} {t e : Edge} {va vb : Word} {vals : List Word}
    {env env' : Env} {mem : Memory} {context : Word} {rest : List Frame} {c : Nat} {s : State}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .br cnd w a b t e)
    (hdir : decide (e.target ≤ lbl) = true)
    (ha : a.eval env = some va) (hbv : b.eval env = some vb)
    (hc : cnd.holds w va vb = false)
    (hargs : evalArgs env e.args = some vals)
    (htgt : f.blocks[e.target]? = some target)
    (hbind : bindParams env target.params vals = some env')
    (hk : Sem.Star (semStep p)
      (State.mk mem context ({ fn, label := e.target, pos := 0, env := env' } :: rest)) c s) :
    Sem.Star (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) (c + 1) s := by
  subst hpos
  have h := step_br_false (rest := rest) (mem := mem) (context := context) hf hb ht ha hbv hc hargs
    htgt hbind
  rw [hdir] at h
  exact .charge h hk

/-- The no-overflow edge of an overflow test (forward). -/
theorem star_brOvf_ok_fwd {p : Program} {fn lbl pos : Nat} {f : Func} {blk target : Block}
    {o : Ovf} {x : VReg} {a b : Arg} {ok ovf : Edge} {va vb res : Word} {vals : List Word}
    {env env' : Env} {mem : Memory} {context : Word} {rest : List Frame} {c : Nat} {s : State}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .brOvf o x a b ok ovf)
    (hdir : decide (ok.target ≤ lbl) = false)
    (ha : a.eval env = some va) (hbv : b.eval env = some vb)
    (ho : o.eval va vb = (res, false))
    (hargs : evalArgs (env.insert x res) ok.args = some vals)
    (htgt : f.blocks[ok.target]? = some target)
    (hbind : bindParams (env.insert x res) target.params vals = some env')
    (hk : Sem.Star (semStep p)
      (State.mk mem context ({ fn, label := ok.target, pos := 0, env := env' } :: rest)) c s) :
    Sem.Star (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) c s := by
  subst hpos
  have h := step_brOvf_ok (rest := rest) (mem := mem) (context := context) hf hb ht ha hbv ho hargs
    htgt hbind
  rw [hdir] at h
  exact .free h hk

/-- The overflow edge of an overflow test (forward). -/
theorem star_brOvf_ovf_fwd {p : Program} {fn lbl pos : Nat} {f : Func} {blk target : Block}
    {o : Ovf} {x : VReg} {a b : Arg} {ok ovf : Edge} {va vb res : Word} {vals : List Word}
    {env env' : Env} {mem : Memory} {context : Word} {rest : List Frame} {c : Nat} {s : State}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .brOvf o x a b ok ovf)
    (hdir : decide (ovf.target ≤ lbl) = false)
    (ha : a.eval env = some va) (hbv : b.eval env = some vb)
    (ho : o.eval va vb = (res, true))
    (hargs : evalArgs (env.insert x res) ovf.args = some vals)
    (htgt : f.blocks[ovf.target]? = some target)
    (hbind : bindParams (env.insert x res) target.params vals = some env')
    (hk : Sem.Star (semStep p)
      (State.mk mem context ({ fn, label := ovf.target, pos := 0, env := env' } :: rest)) c s) :
    Sem.Star (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) c s := by
  subst hpos
  have h := step_brOvf_ovf (rest := rest) (mem := mem) (context := context) hf hb ht ha hbv ho hargs
    htgt hbind
  rw [hdir] at h
  exact .free h hk

/-- A tail call: the callee's activation replaces the running one. One charge. -/
theorem star_tail {p : Program} {fn lbl pos : Nat} {f gFunc : Func} {blk : Block}
    {g : FunId} {args : List Arg} {vals : List Word} {env calleeEnv : Env}
    {mem : Memory} {context : Word} {rest : List Frame} {c : Nat} {s : State}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .tail g args)
    (hargs : evalArgs env args = some vals)
    (hg : p.funcs[g]? = some gFunc)
    (hbind : bindParams {} gFunc.params vals = some calleeEnv)
    (hk : Sem.Star (semStep p)
      (State.mk mem context ({ fn := g, label := 0, pos := 0, env := calleeEnv } :: rest)) c s) :
    Sem.Star (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) (c + 1) s := by
  subst hpos
  exact .charge (step_tail hf hb ht hargs hg hbind) hk

/-! ## Returns

A return to a suspended caller is a free step; a return from the last frame ends the run. -/

/-- `ret []` to a caller that awaits no result. -/
theorem star_ret_zero {p : Program} {fn lbl pos : Nat} {f : Func} {blk : Block}
    {env : Env} {mem : Memory} {context : Word} {caller : Frame} {callers : List Frame}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .ret []) (hd : caller.dsts = []) :
    Sem.Star (semStep p)
      (State.mk mem context ({ fn, label := lbl, pos, env } :: caller :: callers)) 0
      (State.mk mem context (caller :: callers)) := by
  subst hpos
  refine .free ?_ (.refl _)
  apply semStep_next.mpr
  cases caller with
  | mk cfn clabel cpos cenv cdsts =>
    cases hd
    simp [step, hf, hb, ht, evalArgs, bindParams]

/-- `ret [a]` to a caller that awaits one result in `dst`. -/
theorem star_ret_one {p : Program} {fn lbl pos : Nat} {f : Func} {blk : Block}
    {arg : Arg} {env : Env} {mem : Memory} {context res : Word} {caller : Frame}
    {callers : List Frame} {dst : VReg}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .ret [arg]) (ha : arg.eval env = some res)
    (hd : caller.dsts = [dst]) :
    Sem.Star (semStep p)
      (State.mk mem context ({ fn, label := lbl, pos, env } :: caller :: callers)) 0
      (State.mk mem context
        ({ caller with env := caller.env.insert dst res, dsts := [] } :: callers)) := by
  subst hpos
  exact .free (step_ret_one (rest := caller :: callers) hf hb ht ha dst hd) (.refl _)

/-- `ret [a, b]` to a caller that awaits two results. -/
theorem star_ret_two {p : Program} {fn lbl pos : Nat} {f : Func} {blk : Block}
    {a b : Arg} {env : Env} {mem : Memory} {context ra rb : Word} {caller : Frame}
    {callers : List Frame} {d₁ d₂ : VReg}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .ret [a, b])
    (ha : a.eval env = some ra) (hbv : b.eval env = some rb)
    (hd : caller.dsts = [d₁, d₂]) :
    Sem.Star (semStep p)
      (State.mk mem context ({ fn, label := lbl, pos, env } :: caller :: callers)) 0
      (State.mk mem context
        ({ caller with env := (caller.env.insert d₁ ra).insert d₂ rb, dsts := [] } :: callers)) := by
  subst hpos
  refine .free ?_ (.refl _)
  apply semStep_next.mpr
  simp [step, hf, hb, ht, evalArgs, ha, hbv, hd, bindParams]

/-- A resource failure ends the run. -/
theorem reaches_fail {p : Program} {fn lbl pos : Nat} {f : Func} {blk : Block}
    {r : Sem.Resource} {env : Env} {mem : Memory} {context : Word} {rest : List Frame} {k : Nat}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .fail r) :
    Sem.Reaches (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) k
      (.resource r) := by
  subst hpos
  exact .final (final_fail hf hb ht)

/-- A trap ends the run. -/
theorem reaches_trap {p : Program} {fn lbl pos : Nat} {f : Func} {blk : Block}
    {env : Env} {mem : Memory} {context : Word} {rest : List Frame} {k : Nat}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .trap) :
    Sem.Reaches (semStep p) (State.mk mem context ({ fn, label := lbl, pos, env } :: rest)) k
      .trap := by
  subst hpos
  exact .final (final_trap hf hb ht)

/-- `ret []` from the last frame. -/
theorem reaches_ret_zero {p : Program} {fn lbl pos : Nat} {f : Func} {blk : Block}
    {env : Env} {mem : Memory} {context : Word} {k : Nat}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .ret []) :
    Sem.Reaches (semStep p) (State.mk mem context [{ fn, label := lbl, pos, env }]) k
      (.ok ([], mem)) := by
  subst hpos
  exact .final (final_ret_zero hf hb ht)

/-- `ret [a]` from the last frame. -/
theorem reaches_ret_one {p : Program} {fn lbl pos : Nat} {f : Func} {blk : Block}
    {arg : Arg} {env : Env} {mem : Memory} {context res : Word} {k : Nat}
    (hf : p.funcs[fn]? = some f) (hb : f.blocks[lbl]? = some blk)
    (hpos : pos = blk.body.size) (ht : blk.term = .ret [arg]) (ha : arg.eval env = some res) :
    Sem.Reaches (semStep p) (State.mk mem context [{ fn, label := lbl, pos, env }]) k
      (.ok ([res], mem)) := by
  subst hpos
  exact .final (final_ret_one hf hb ht ha)

end IxCC.Rt.Rc.Array
