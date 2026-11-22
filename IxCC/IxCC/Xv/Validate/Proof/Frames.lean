import IxCC.Xv.Validate.Proof.Terms

/-!
# Steps of a matched frame

`Running` names the function and block of a matched running frame. The Xl
step at a call and at each terminator (`xl_step_call`, `xl_step_jmp`, …),
the Xv steps that end a run (`xv_step_final`), and an edge the validator
checked (`edge_sound`): Xl takes the same edge, with no parallel move left
to do, and the frames match at the target under its certificate.
-/

namespace IxCC.Xv.Validate

open IxCC.Lir (VReg Word Env Label FunId)
open IxCC.Xv.Alloc (Edit Output BlockOut)
open IxCC.Xv

section Running

variable (env : Xl.Env) (p : VProgram) (outs : List Output) (q : LProgram)

/-- A matched running frame (`RunMatch`) with its function, output, image,
blocks and abstract state named. -/
structure Running (fr : Lir.Frame) (fl : Xl.Frame) (regs : Xl.Regs) (f : Func VReg) (o : Output)
    (g : Func Loc) (b : Block VReg) (bo : BlockOut) (bl : Block Loc) (a : AState) : Prop where
  fn : fl.fn = fr.fn
  label : fl.label = fr.label
  hf : p.funcs[fr.fn]? = some f
  ho : outs[fr.fn]? = some o
  hg : q.funcs[fr.fn]? = some g
  hfunc : func env fr.fn f o = .ok ()
  happ : Alloc.apply f o = .ok g
  hb : f.blocks[fr.label]? = some b
  hbo : o.blocks[fr.label]? = some bo
  hbl : g.blocks[fr.label]? = some bl
  rest : BlockRest (funcCtx env f o) (funcInfo f o) b bo bl fr.pos fl.pos a
  agree : a.Agree fr.env (Xl.read regs fl)
  inArgs : fl.inArgs.size = (funcCtx env f o).stackParams

end Running

variable {env : Xl.Env} {p : VProgram} {outs : List Output} {q : LProgram}

theorem RunMatch.running {fr : Lir.Frame} {fl : Xl.Frame} {regs : Xl.Regs}
    (h : RunMatch env p outs q fr fl regs) :
    ∃ f o g b bo bl a, Running env p outs q fr fl regs f o g b bo bl a := by
  obtain ⟨hfn, hlab, f, o, g, b, bo, bl, a, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨f, o, g, b, bo, bl, a, hfn, hlab, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem Running.runMatch {fr : Lir.Frame} {fl : Xl.Frame} {regs : Xl.Regs} {f : Func VReg} {o : Output}
    {g : Func Loc} {b : Block VReg} {bo : BlockOut} {bl : Block Loc} {a : AState}
    (h : Running env p outs q fr fl regs f o g b bo bl a) : RunMatch env p outs q fr fl regs :=
  ⟨h.fn, h.label, f, o, g, b, bo, bl, a, h.hf, h.ho, h.hg, h.hfunc, h.happ, h.hb, h.hbo, h.hbl, h.rest, h.agree,
    h.inArgs⟩

/-! ## Xl steps -/

section XlStep

variable (q : LProgram) (env : Xl.Env)

theorem xl_step_call {t : Xl.State} {fl : Xl.Frame} {rest : List Xl.Frame} (ht : t.stack = fl :: rest)
    {g : Func Loc} (hg : q.funcs[fl.fn]? = some g) {bl : Block Loc} (hbl : g.blocks[fl.label]? = some bl)
    {g' : FunId} {args rets : List Loc} {more : List (Inst Loc)}
    (hd : bl.body.toList.drop fl.pos = .call g' args rets :: more)
    (hca : Xl.conventionArgs args = true) (hcr : Xl.conventionResults rets = true)
    {vals : List Word} (hr : Xl.readAll t.regs fl args = some vals)
    {callee : Xl.Frame} {regs : Xl.Regs} (he : Xl.enter q g' vals = some (callee, regs)) :
    Xl.step q env t = .next
      { t with
        regs
        stack := callee :: Xl.suspend fl t.regs (env.clobbers g') rets.length :: rest } true := by
  obtain ⟨hj, hx'⟩ := drop_getElem hd
  unfold Xl.step
  rw [ht]
  simp [hg, hbl, hj, hx', hca, hcr, hr, he]

variable {t : Xl.State} {fl : Xl.Frame} {g : Func Loc} {bl : Block Loc}

theorem xl_step_jmp {rest : List Xl.Frame} (ht : t.stack = fl :: rest)
    (hg : q.funcs[fl.fn]? = some g) (hbl : g.blocks[fl.label]? = some bl)
    (hd : bl.body.toList.drop fl.pos = []) {e : Edge Loc} (hterm : bl.term = .jmp e) :
    Xl.step q env t = Xl.takeEdge g t fl rest t.regs e := by
  have hn := drop_nil_size hd
  unfold Xl.step
  rw [ht]
  simp [hg, hbl, hn, hterm]

theorem xl_step_jcc {rest : List Xl.Frame} (ht : t.stack = fl :: rest)
    (hg : q.funcs[fl.fn]? = some g) (hbl : g.blocks[fl.label]? = some bl)
    (hd : bl.body.toList.drop fl.pos = []) {p' : X86.Op} {pargs : List (XArg Loc)} {defs : List Loc}
    {cond : X86.Condition} {e₁ e₂ : Edge Loc} (hterm : bl.term = .jcc p' pargs defs cond e₁ e₂)
    {bs : List (Bound Loc)} (hb : bindRow p' defs pargs = some bs)
    {regs' : Xl.Regs} {fr' : Xl.Frame} {mem' : X86.Memory} {flags : X86.ByteEval.Flags}
    (hx : Xl.execBound [(p', bs)] t.regs fl t.mem t.ctx = some (regs', fr', mem', flags))
    {taken : Bool} (htk : jccTaken cond flags = some taken) :
    Xl.step q env t = Xl.takeEdge g { t with mem := mem' } fr' rest regs' (if taken then e₁ else e₂) := by
  have hn := drop_nil_size hd
  unfold Xl.step
  rw [ht]
  simp [hg, hbl, hn, hterm, hb, hx, htk]

theorem xl_step_ret_done (ht : t.stack = [fl])
    (hg : q.funcs[fl.fn]? = some g) (hbl : g.blocks[fl.label]? = some bl)
    (hd : bl.body.toList.drop fl.pos = []) {vs : List Loc} (hterm : bl.term = .ret vs)
    (hcr : Xl.conventionResults vs = true) {vals : List Word} (hr : Xl.readAll t.regs fl vs = some vals) :
    Xl.step q env t = .done (vals, t.mem) := by
  have hn := drop_nil_size hd
  unfold Xl.step
  rw [ht]
  simp [hg, hbl, hn, hterm, hcr, hr]

theorem xl_step_ret {caller : Xl.Frame} {rest : List Xl.Frame} (ht : t.stack = fl :: caller :: rest)
    (hg : q.funcs[fl.fn]? = some g) (hbl : g.blocks[fl.label]? = some bl)
    (hd : bl.body.toList.drop fl.pos = []) {vs : List Loc} (hterm : bl.term = .ret vs)
    (hcr : Xl.conventionResults vs = true) {vals : List Word} (hr : Xl.readAll t.regs fl vs = some vals)
    (hres : caller.results = vals.length) :
    Xl.step q env t = .next
      { t with
        regs := Xl.returnRegs caller.saved caller.clobber vals
        stack := { caller with saved := Xl.Regs.empty, clobber := [], results := 0 } :: rest } false := by
  have hn := drop_nil_size hd
  unfold Xl.step
  rw [ht]
  simp [hg, hbl, hn, hterm, hcr, hr, hres]

theorem xl_step_tail {rest : List Xl.Frame} (ht : t.stack = fl :: rest)
    (hg : q.funcs[fl.fn]? = some g) (hbl : g.blocks[fl.label]? = some bl)
    (hd : bl.body.toList.drop fl.pos = []) {g' : FunId} {args : List Loc} (hterm : bl.term = .tail g' args)
    (hlen : args.length ≤ Xl.nArgRegs) (hca : Xl.conventionArgs args = true)
    {vals : List Word} (hr : Xl.readAll t.regs fl args = some vals)
    {callee : Xl.Frame} {regs : Xl.Regs} (he : Xl.enter q g' vals = some (callee, regs)) :
    Xl.step q env t = .next { t with regs, stack := callee :: rest } true := by
  have hn := drop_nil_size hd
  unfold Xl.step
  rw [ht]
  have : ¬ (Xl.nArgRegs < args.length) := by omega
  simp [hg, hbl, hn, hterm, hca, hr, he, this]

theorem xl_step_fail {rest : List Xl.Frame} (ht : t.stack = fl :: rest)
    (hg : q.funcs[fl.fn]? = some g) (hbl : g.blocks[fl.label]? = some bl)
    (hd : bl.body.toList.drop fl.pos = []) {r : Sem.Resource} (hterm : bl.term = .fail r) :
    Xl.step q env t = .fail r := by
  have hn := drop_nil_size hd
  unfold Xl.step
  rw [ht]
  simp [hg, hbl, hn, hterm]

theorem xl_step_trap {rest : List Xl.Frame} (ht : t.stack = fl :: rest)
    (hg : q.funcs[fl.fn]? = some g) (hbl : g.blocks[fl.label]? = some bl)
    (hd : bl.body.toList.drop fl.pos = []) (hterm : bl.term = .trap) :
    Xl.step q env t = .trap := by
  have hn := drop_nil_size hd
  unfold Xl.step
  rw [ht]
  simp [hg, hbl, hn, hterm]

end XlStep

/-! ## Edges -/

/-- An edge the validator checked, taken at Xv: Xl takes it with no
arguments, and the frames match at its target under the target's
certificate. -/
theorem edge_sound {f : Func VReg} {o : Output} {g : Func Loc}
    {a : AState} {ρ : Env} {regs : Xl.Regs} {fl : Xl.Frame} (hag : a.Agree ρ (Xl.read regs fl))
    {edges : List (Edge VReg)} (hce : checkEdges (funcInfo f o) a edges = none)
    {e : Edge VReg} (he : e ∈ edges)
    {s s' : Lir.State} {fr : Lir.Frame} {rest : List Lir.Frame} {c : Bool}
    (hx : Xv.takeEdge f s fr rest ρ e = .next s' c)
    (hf : p.funcs[fr.fn]? = some f) (ho : outs[fr.fn]? = some o) (hg : q.funcs[fr.fn]? = some g)
    (hv : func env fr.fn f o = .ok ()) (happ : Alloc.apply f o = .ok g)
    (hfn : fl.fn = fr.fn) (hlab : fl.label = fr.label)
    (hin : fl.inArgs.size = (funcCtx env f o).stackParams) (t : Xl.State) (rest' : List Xl.Frame) :
    Xl.takeEdge g t fl rest' regs ⟨e.target, []⟩ =
      .next { t with regs, stack := { fl with label := e.target, pos := 0 } :: rest' } c ∧
    ∃ fr', s' = { s with stack := fr' :: rest } ∧
      RunMatch env p outs q fr' { fl with label := e.target, pos := 0 } regs := by
  obtain ⟨vals, b', ρ', hr, hb', hρ, rfl, rfl⟩ := takeEdge_next hx
  have hfo := func_ok hv
  have hap := apply_ok happ
  have hlt : e.target < o.blocks.length := by
    rw [← hfo.len]
    exact (Array.getElem?_eq_some_iff.1 hb').1
  obtain ⟨bo', hbo'⟩ : ∃ bo', o.blocks[e.target]? = some bo' :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨bl', hbl', hab'⟩ := hap.blocks e.target b' bo' hb' hbo'
  have hcb := hfo.blocks e.target b' bo' hb' hbo'
  have hpar := (applyBlock_ok hab').params
  obtain ⟨params, cert, hfind, hle⟩ := checkEdges_mem hce he
  rw [funcInfo, blockInfo_find (by simpa using hfo.len) (by simpa using hb') hbo'] at hfind
  simp only [Option.some.injEq, Prod.mk.injEq] at hfind
  obtain ⟨rfl, rfl⟩ := hfind
  refine ⟨?_, _, rfl, ?_⟩
  · rw [xl_takeEdge hbl' hpar, hlab]
  · refine ⟨hfn, rfl, f, o, g, b', bo', bl', AState.ofList bo'.cert, hf, ho, hg, hv, happ, hb', hbo', hbl',
      BlockRest.start hcb hab', ?_, hin⟩
    rw [read_goto]
    exact AState.Agree.antitone hle (hag.bindParams (checkBlock_ok hcb).1 hr hρ)

/-! ## Final Xv steps -/

/-- A final Xv step other than a stuck one: a return from the last frame, a
resource failure or a trap, all at a terminator. -/
theorem xv_step_final {s : Lir.State} {fr : Lir.Frame} {rest : List Lir.Frame} (hss : s.stack = fr :: rest)
    {f : Func VReg} (hf : p.funcs[fr.fn]? = some f) {b : Block VReg} (hb : f.blocks[fr.label]? = some b)
    {r : Sem.Result (List Word × X86.Memory)} (h : Sem.Final (Xv.step p s) r) (hr : r ≠ .stuck) :
    ¬ fr.pos < b.body.size ∧
      ((∃ vs vals, b.term = .ret vs ∧ Xv.readAll fr.env vs = some vals ∧ rest = [] ∧
          r = .ok (vals, s.mem)) ∨
        (∃ failure, b.term = .fail failure ∧ r = .resource failure) ∨ (b.term = .trap ∧ r = .trap)) := by
  rw [Sem.Final.iff_outcome] at h
  unfold Xv.step at h
  rw [hss] at h
  simp only [hf, hb] at h
  by_cases hpos : fr.pos < b.body.size
  · exfalso
    simp only [hpos, ↓reduceDIte] at h
    split at h
    · split at h <;> simp_all [Sem.Final.outcome]
    · split at h <;> simp_all [Sem.Final.outcome]
  · refine ⟨hpos, ?_⟩
    simp only [hpos, ↓reduceDIte] at h
    cases hT : b.term with
    | jmp e =>
      exfalso
      simp only [hT, Xv.takeEdge] at h
      split at h
      · split at h <;> simp_all [Sem.Final.outcome]
      · simp_all [Sem.Final.outcome]
    | jcc p' pargs defs cond e₁ e₂ =>
      exfalso
      simp only [hT] at h
      split at h
      · simp only [Xv.takeEdge] at h
        split at h
        · split at h <;> simp_all [Sem.Final.outcome]
        · simp_all [Sem.Final.outcome]
      · simp_all [Sem.Final.outcome]
    | ret vs =>
      simp only [hT] at h
      split at h
      · simp_all [Sem.Final.outcome]
      · rename_i vals hvals
        split at h
        · simp only [Sem.Final.outcome, Option.some.injEq] at h
          exact .inl ⟨vs, vals, rfl, hvals, rfl, h.symm⟩
        · exfalso
          split at h <;> simp_all [Sem.Final.outcome]
    | tail g' args =>
      exfalso
      simp only [hT] at h
      split at h <;> simp_all [Sem.Final.outcome]
    | fail failure =>
      simp only [hT, Sem.Final.outcome, Option.some.injEq] at h
      exact .inr (.inl ⟨failure, rfl, h.symm⟩)
    | trap =>
      simp only [hT, Sem.Final.outcome, Option.some.injEq] at h
      exact .inr (.inr ⟨rfl, h.symm⟩)

end IxCC.Xv.Validate
