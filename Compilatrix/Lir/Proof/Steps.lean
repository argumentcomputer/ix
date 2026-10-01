import Compilatrix.Lir.Proof.Run
import Std.Data.HashMap.Lemmas

/-!
# Lir step lemmas

One equation per shape of `Lir.step` (a statement, a call, each
terminator, an edge), stated on a state whose running frame is explicit,
plus `Lir.star_stmts`: a run of local statements in one block is a
`Sem.Star` with no charge. Simulation proofs into Lir (`Rt.lower_correct`)
reason through these, never through `step`'s `match`.
-/

set_option autoImplicit false

namespace Compilatrix.Lir

variable {p : Program} {mem : X86.Memory} {ctx : Word} {fr : Frame} {rest : List Frame}
  {F : Func} {B : Block}

/-! ## Environments -/

@[simp] theorem env_insert_self (ρ : Env) (x : VReg) (v : Word) : (ρ.insert x v)[x]? = some v :=
  Std.HashMap.getElem?_insert_self

theorem env_insert_ne (ρ : Env) {x y : Nat} (v : Word) (h : x ≠ y) : (ρ.insert x v)[y]? = ρ[y]? := by
  rw [Std.HashMap.getElem?_insert]
  simp [h]

@[simp] theorem env_empty (x : VReg) : ({} : Env)[x]? = none := Std.HashMap.getElem?_empty

/-- A lookup after an insert, as an `if` on the registers (for `simp only`). -/
theorem env_insert_get (ρ : Env) (x y : Nat) (v : Word) :
    (ρ.insert x v)[y]? = if x = y then some v else ρ[y]? := by
  rw [Std.HashMap.getElem?_insert]
  simp

/-! ## Statements -/

/-- Whether a statement is a call (`step` runs calls, `Stmt.exec` the rest). -/
def Stmt.isCall : Stmt → Bool
  | .call .. => true
  | _ => false

/-- A list of local statements, run in order. -/
def execList (ρ : Env) (mem : X86.Memory) (ctx : Word) : List Stmt → Option (Env × X86.Memory)
  | [] => some (ρ, mem)
  | s :: ss =>
    match s.exec ρ mem ctx with
    | some (ρ', mem') => execList ρ' mem' ctx ss
    | none => none

theorem step_stmt {s : Stmt} {ρ' : Env} {mem' : X86.Memory}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B) (hpos : fr.pos < B.body.size)
    (hs : B.body[fr.pos] = s) (hnc : s.isCall = false) (hx : s.exec fr.env mem ctx = some (ρ', mem')) :
    step p { mem, ctx, stack := fr :: rest } =
      .next { mem := mem', ctx, stack := { fr with pos := fr.pos + 1, env := ρ' } :: rest } false := by
  unfold step
  simp only [hf, hb, hpos, ↓reduceDIte, hs]
  cases s with
  | call => simp [Stmt.isCall] at hnc
  | assign x r => simp only [hx]
  | store w m a => simp only [hx]

theorem step_call {rs : List VReg} {g : FunId} {as : List Arg} {vs : List Word} {callee : Frame}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B) (hpos : fr.pos < B.body.size)
    (hs : B.body[fr.pos] = .call rs g as) (ha : evalArgs fr.env as = some vs)
    (he : enter p g vs = some callee) :
    step p { mem, ctx, stack := fr :: rest } =
      .next { mem, ctx, stack := callee :: { fr with pos := fr.pos + 1, dsts := rs } :: rest } true := by
  unfold step
  simp only [hf, hb, hpos, ↓reduceDIte, hs, ha, Option.bind_eq_bind, Option.bind_some, he]

/-- A run of local statements at positions `pre.length …` of one block. -/
theorem star_stmts {fn L : Nat} {dsts : List VReg} (hf : p.funcs[fn]? = some F) (hb : F.blocks[L]? = some B) :
    ∀ {pre ss post : List Stmt} {ρ ρ' : Env} {mem mem' : X86.Memory},
      B.body.toList = pre ++ ss ++ post → (∀ s ∈ ss, s.isCall = false) →
      execList ρ mem ctx ss = some (ρ', mem') →
      Sem.Star (semStep p) { mem, ctx, stack := { fn, label := L, pos := pre.length, env := ρ, dsts } :: rest } 0
        { mem := mem', ctx, stack := { fn, label := L, pos := pre.length + ss.length, env := ρ', dsts } :: rest }
  | pre, [], post, ρ, ρ', mem, mem', _, _, hx => by
    simp only [execList, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact .refl _
  | pre, s :: ss, post, ρ, ρ', mem, mem', hbody, hnc, hx => by
    simp only [execList] at hx
    split at hx
    · rename_i ρ₁ mem₁ hs
      have hpos : pre.length < B.body.size := by
        have := congrArg List.length hbody
        simp only [List.length_append, List.length_cons, Array.length_toList] at this
        omega
      have hget : B.body[pre.length] = s := by
        have : B.body.toList[pre.length]? = some s := by rw [hbody]; simp
        simp only [Array.getElem?_toList, Array.getElem?_eq_some_iff] at this
        exact this.2
      have h1 := step_stmt (fr := { fn, label := L, pos := pre.length, env := ρ, dsts }) (rest := rest)
        (mem := mem) (ctx := ctx) hf hb hpos hget (hnc s (by simp)) hs
      have h2 := star_stmts (dsts := dsts) (pre := pre ++ [s]) (ss := ss) (post := post) hf hb
        (by rw [hbody]; simp) (fun s' hs' => hnc s' (by simp [hs'])) hx
      simp only at h1
      have h2' : Sem.Star (semStep p)
          { mem := mem₁, ctx, stack := { fn, label := L, pos := pre.length + 1, env := ρ₁, dsts } :: rest } 0
          { mem := mem', ctx, stack := { fn, label := L, pos := pre.length + 1 + ss.length, env := ρ', dsts } :: rest } := by
        simpa using h2
      have := Sem.Star.free (step := semStep p) (semStep_next.2 h1) h2'
      simpa [Nat.add_assoc, Nat.add_comm 1] using this
    · simp at hx

/-! ## Terminators and edges -/

theorem takeEdge_ok {s : State} {ρ ρ' : Env} {e : Edge} {vals : List Word} {target : Block}
    (ha : evalArgs ρ e.args = some vals) (ht : F.blocks[e.target]? = some target)
    (hp : bindParams ρ target.params vals = some ρ') :
    takeEdge F s fr rest ρ e =
      .next { s with stack := { fr with label := e.target, pos := 0, env := ρ' } :: rest }
        (decide (e.target ≤ fr.label)) := by
  unfold takeEdge
  simp only [ha, ht, hp]

theorem step_term (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hpos : fr.pos = B.body.size) :
    step p { mem, ctx, stack := fr :: rest } =
      match B.term with
      | .jump e => takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env e
      | .br c w a b' t e =>
          match a.eval fr.env, b'.eval fr.env with
          | some va, some vb =>
            takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env (if c.holds w va vb then t else e)
          | _, _ => .stuck
      | .brOvf o x a b' ok ovf =>
          match a.eval fr.env, b'.eval fr.env with
          | some va, some vb =>
              let (r, carry) := o.eval va vb
              takeEdge F { mem, ctx, stack := fr :: rest } fr rest (fr.env.insert x r) (if carry then ovf else ok)
          | _, _ => .stuck
      | .ret as =>
          match evalArgs fr.env as with
          | none => .stuck
          | some vals =>
              match rest with
              | [] => .done vals mem
              | caller :: rest' =>
                  match bindParams caller.env caller.dsts vals with
                  | some ρ => .next { mem, ctx, stack := { caller with env := ρ, dsts := [] } :: rest' } false
                  | none => .stuck
      | .tail g as =>
          match evalArgs fr.env as >>= enter p g with
          | some callee => .next { mem, ctx, stack := callee :: rest } true
          | none => .stuck
      | .fail r => .fail r
      | .trap => .trap := by
  unfold step
  simp only [hf, hb, hpos, Nat.lt_irrefl, ↓reduceDIte]
  rfl

theorem step_jump {e : Edge} (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hpos : fr.pos = B.body.size) (ht : B.term = .jump e) :
    step p { mem, ctx, stack := fr :: rest } = takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env e := by
  rw [step_term hf hb hpos, ht]

theorem step_br {c : Cond} {w : Width} {a b : Arg} {t e : Edge} {va vb : Word}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hpos : fr.pos = B.body.size) (ht : B.term = .br c w a b t e)
    (ha : a.eval fr.env = some va) (hb' : b.eval fr.env = some vb) :
    step p { mem, ctx, stack := fr :: rest } =
      takeEdge F { mem, ctx, stack := fr :: rest } fr rest fr.env (if c.holds w va vb then t else e) := by
  rw [step_term hf hb hpos, ht]
  simp only [ha, hb']

theorem step_brOvf {o : Ovf} {x : VReg} {a b : Arg} {ok ovf : Edge} {va vb : Word}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hpos : fr.pos = B.body.size) (ht : B.term = .brOvf o x a b ok ovf)
    (ha : a.eval fr.env = some va) (hb' : b.eval fr.env = some vb) :
    step p { mem, ctx, stack := fr :: rest } =
      takeEdge F { mem, ctx, stack := fr :: rest } fr rest (fr.env.insert x (o.eval va vb).1)
        (if (o.eval va vb).2 then ovf else ok) := by
  rw [step_term hf hb hpos, ht]
  simp only [ha, hb']

theorem step_ret_done {as : List Arg} {vals : List Word}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hpos : fr.pos = B.body.size) (ht : B.term = .ret as) (ha : evalArgs fr.env as = some vals) :
    step p { mem, ctx, stack := [fr] } = .done vals mem := by
  rw [step_term hf hb hpos, ht]
  simp only [ha]

theorem step_ret_caller {as : List Arg} {vals : List Word} {caller : Frame} {rest' : List Frame} {ρ : Env}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hpos : fr.pos = B.body.size) (ht : B.term = .ret as) (ha : evalArgs fr.env as = some vals)
    (hp : bindParams caller.env caller.dsts vals = some ρ) :
    step p { mem, ctx, stack := fr :: caller :: rest' } =
      .next { mem, ctx, stack := { caller with env := ρ, dsts := [] } :: rest' } false := by
  rw [step_term hf hb hpos, ht]
  simp only [ha, hp]

theorem step_tail {g : FunId} {as : List Arg} {vs : List Word} {callee : Frame}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hpos : fr.pos = B.body.size) (ht : B.term = .tail g as) (ha : evalArgs fr.env as = some vs)
    (he : enter p g vs = some callee) :
    step p { mem, ctx, stack := fr :: rest } = .next { mem, ctx, stack := callee :: rest } true := by
  rw [step_term hf hb hpos, ht]
  simp only [ha, Option.bind_eq_bind, Option.bind_some, he]

theorem step_fail {r : Sem.Resource}
    (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hpos : fr.pos = B.body.size) (ht : B.term = .fail r) :
    step p { mem, ctx, stack := fr :: rest } = .fail r := by
  rw [step_term hf hb hpos, ht]

theorem step_trap (hf : p.funcs[fr.fn]? = some F) (hb : F.blocks[fr.label]? = some B)
    (hpos : fr.pos = B.body.size) (ht : B.term = .trap) :
    step p { mem, ctx, stack := fr :: rest } = .trap := by
  rw [step_term hf hb hpos, ht]

/-- A `fail` terminator reached by free steps: the run fails for that
resource. -/
theorem fails_of_star {s s' : State} {c : Nat} {r : Sem.Resource} (h : Sem.Star (semStep p) s c s')
    (hf : step p s' = .fail r) : Sem.Fails (semStep p) s :=
  ⟨c, s', r, h, by simp [semStep, hf, Step.toSem]⟩

/-! ## Steps of a frame with no pending results

The running frame of a simulated activation has no pending results
(`dsts = []`: `enter` starts one so, edges and statements keep it, and a
return clears it). `atState` names such states, and the lemmas below give
each step between them. -/

/-- The state whose running frame is at `(fn, L, pos)` with registers `ρ`,
over the frames `rest`. -/
abbrev atState (mem : X86.Memory) (ctx : Word) (fn L pos : Nat) (ρ : Env) (rest : List Frame) : State :=
  { mem, ctx, stack := { fn, label := L, pos, env := ρ } :: rest }

section atState

variable {fn L pos : Nat} {ρ ρ' : Env} {e e' : Edge} {vals : List Word} {tb : Block}

theorem jump_at (hf : p.funcs[fn]? = some F) (hb : F.blocks[L]? = some B) (hpos : pos = B.body.size)
    (ht : B.term = .jump e) (ha : evalArgs ρ e.args = some vals) (htb : F.blocks[e.target]? = some tb)
    (hp : bindParams ρ tb.params vals = some ρ') :
    step p (atState mem ctx fn L pos ρ rest) =
      .next (atState mem ctx fn e.target 0 ρ' rest) (decide (e.target ≤ L)) := by
  unfold step takeEdge
  simp only [hf, hb, hpos, Nat.lt_irrefl, ↓reduceDIte, ht, ha, htb, hp]

theorem br_at {c : Cond} {w : Width} {a b : Arg} {t f : Edge} {va vb : Word}
    (hf : p.funcs[fn]? = some F) (hb : F.blocks[L]? = some B) (hpos : pos = B.body.size)
    (ht : B.term = .br c w a b t f) (hva : a.eval ρ = some va) (hvb : b.eval ρ = some vb)
    (he : e = if c.holds w va vb then t else f)
    (ha : evalArgs ρ e.args = some vals) (htb : F.blocks[e.target]? = some tb)
    (hp : bindParams ρ tb.params vals = some ρ') :
    step p (atState mem ctx fn L pos ρ rest) =
      .next (atState mem ctx fn e.target 0 ρ' rest) (decide (e.target ≤ L)) := by
  unfold step
  simp only [hf, hb, hpos, Nat.lt_irrefl, ↓reduceDIte, ht, hva, hvb, ← he]
  unfold takeEdge
  simp only [ha, htb, hp]

theorem brOvf_at {o : Ovf} {x : VReg} {a b : Arg} {ok ovf : Edge} {va vb : Word}
    (hf : p.funcs[fn]? = some F) (hb : F.blocks[L]? = some B) (hpos : pos = B.body.size)
    (ht : B.term = .brOvf o x a b ok ovf) (hva : a.eval ρ = some va) (hvb : b.eval ρ = some vb)
    (he : e = if (o.eval va vb).2 then ovf else ok)
    (ha : evalArgs (ρ.insert x (o.eval va vb).1) e.args = some vals) (htb : F.blocks[e.target]? = some tb)
    (hp : bindParams (ρ.insert x (o.eval va vb).1) tb.params vals = some ρ') :
    step p (atState mem ctx fn L pos ρ rest) =
      .next (atState mem ctx fn e.target 0 ρ' rest) (decide (e.target ≤ L)) := by
  unfold step
  simp only [hf, hb, hpos, Nat.lt_irrefl, ↓reduceDIte, ht, hva, hvb, ← he]
  unfold takeEdge
  simp only [ha, htb, hp]

theorem fail_at {r : Sem.Resource} (hf : p.funcs[fn]? = some F) (hb : F.blocks[L]? = some B)
    (hpos : pos = B.body.size) (ht : B.term = .fail r) :
    step p (atState mem ctx fn L pos ρ rest) = .fail r := by
  unfold step
  simp only [hf, hb, hpos, Nat.lt_irrefl, ↓reduceDIte, ht]

theorem trap_at (hf : p.funcs[fn]? = some F) (hb : F.blocks[L]? = some B)
    (hpos : pos = B.body.size) (ht : B.term = .trap) :
    step p (atState mem ctx fn L pos ρ rest) = .trap := by
  unfold step
  simp only [hf, hb, hpos, Nat.lt_irrefl, ↓reduceDIte, ht]

/-- Local statements in one block, between frames with no pending
results. -/
theorem stmts_at {pre ss post : List Stmt} {mem' : X86.Memory}
    (hf : p.funcs[fn]? = some F) (hb : F.blocks[L]? = some B)
    (hbody : B.body.toList = pre ++ ss ++ post) (hnc : ∀ s ∈ ss, s.isCall = false)
    (hx : execList ρ mem ctx ss = some (ρ', mem')) :
    Sem.Star (semStep p) (atState mem ctx fn L pre.length ρ rest) 0
      (atState mem' ctx fn L (pre.length + ss.length) ρ' rest) :=
  star_stmts (dsts := []) hf hb hbody hnc hx

/-- A single step as a `Star`. -/
theorem star_of_step {s s' : State} {c : Bool} (h : step p s = .next s' c) :
    Sem.Star (semStep p) s c.toNat s' :=
  Sem.Star.single (semStep_next.2 h)

end atState

/-! ## Arguments and parameters -/

@[simp] theorem evalArgs_nil (ρ : Env) : evalArgs ρ [] = some [] := rfl

@[simp] theorem evalArgs_cons (ρ : Env) (a : Arg) (as : List Arg) :
    evalArgs ρ (a :: as) = (do let v ← a.eval ρ; let vs ← evalArgs ρ as; pure (v :: vs)) := by
  simp [evalArgs, List.mapM_cons]

@[simp] theorem Arg.eval_imm (ρ : Env) (w : Word) : Arg.eval ρ (.imm w) = some w := rfl
@[simp] theorem Arg.eval_v (ρ : Env) (x : VReg) : Arg.eval ρ (.v x) = ρ[x]? := rfl

end Compilatrix.Lir
