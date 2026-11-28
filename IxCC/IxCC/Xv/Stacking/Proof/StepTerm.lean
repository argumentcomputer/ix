import IxCC.Xv.Stacking.Proof.StepBody

/-!
# Jumps, branches, failures and traps

A jump and a branch (`step_jmp`, `step_jcc`) are one checked step each to
the target label's block, where the invariant holds at the target's first
instruction. A failure or a trap jumps to the exit group, which reaches
the export wrapper's exit with the failure's status (`step_fail`).
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

/-- No edge enters label 0. -/
theorem FnAt.noEntryEdge {S : Stk} {k : Lir.FunId} {f : Func Loc} {l : FrameLayout} {pl : Placed}
    (hf : FnAt S k f l pl) : ∀ b ∈ f.blocks.toList, 0 ∉ b.term.succs := by
  obtain ⟨pl', blks, -, -, -, -, -, hemit, -⟩ := func_at S.ok hf.func hf.layout
  exact (emitFunc_ok hemit).2.2.1

/-- Xl's position at the start of a label. -/
theorem xlPos_start {S : Stk} {fr : Xl.Frame} {f : Func Loc} {l : FrameLayout} {pl : Placed}
    (hf : FnAt S fr.fn f l pl) {L : Nat} {tb : Block Loc} (htb : f.blocks[L]? = some tb) :
    tb.params = [] ∧ ∃ codes post t, XlPos S { fr with label := L, pos := 0 } f l pl tb codes post t := by
  obtain ⟨pl', blk, hpl', -, -, -, -, hblock, hfound⟩ := block_at S hf.func hf.layout htb
  have e : pl' = pl := Option.some.inj (hpl'.symm.trans hf.placed)
  subst e
  obtain ⟨hparams, codes, post, t, hlen, hinsts, hterm, rfl⟩ := block_ok hblock
  exact ⟨hparams, codes, post, t, ⟨htb, hfound, hlen, hinsts, hterm, Nat.zero_le _⟩⟩

theorem After.refl {c : FnCtx} {regs : Xl.Regs} {fr : Xl.Frame} {mem : Memory} {ctx : Word} {core : Core}
    (ha : Agree c regs fr mem ctx core) : After c [] regs fr mem core regs fr mem ctx core :=
  ⟨ha, Xl.Frame.SameCtl.refl _, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem takeEdge_empty {f : Func Loc} {s : Xl.State} {fr : Xl.Frame} {rest : List Xl.Frame} {regs : Xl.Regs}
    {e : Edge Loc} (hargs : e.args = []) {tb : Block Loc} (htb : f.blocks[e.target]? = some tb)
    (hparams : tb.params = []) :
    Xl.takeEdge f s fr rest regs e =
      .next { s with regs, stack := { fr with label := e.target, pos := 0 } :: rest } (decide (e.target ≤ fr.label)) := by
  simp [Xl.takeEdge, hargs, htb, hparams, Xl.readAll, Xl.writeAll]

theorem edge_ok {c : FnCtx} {e : Edge Loc} {blk : X86.BlockId} (h : c.edge e = .ok blk) :
    e.args = [] ∧ e.target < c.labels ∧ blk = UInt32.ofNat (c.labelBase + e.target) := by
  unfold FnCtx.edge at h
  by_cases hargs : e.args.isEmpty = true
  · by_cases hl : e.target < c.labels
    · have hlab : c.label e.target = .ok (UInt32.ofNat (c.labelBase + e.target)) := by
        simp only [FnCtx.label, hl, ↓reduceIte]; rfl
      simp only [hargs, hlab] at h
      exact ⟨by simpa using hargs, hl, (Except.ok.inj h).symm⟩
    · have hlab : c.label e.target = .error s!"label {e.target} is not a block" := by
        simp only [FnCtx.label, hl, ↓reduceIte]; rfl
      simp only [hargs, hlab] at h
      cases h
  · simp [hargs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-- After the running activation's state changes as `After` says, a jump to
label `L ≠ 0`: the invariant at its first instruction. -/
theorem Match.jump {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {D : List Loc} (hwrites : ∀ r, Loc.reg r ∈ D → r ∈ f.facts.writes)
    {regs' : Xl.Regs} {fr'' : Xl.Frame} {mem' : Memory} {core' : Core} {holes' : Holes}
    (hafter : After (ctxOf S.placed pl) D s.regs fr s.mem m.core regs' fr'' mem' W.ctx core')
    (hholes : ∀ y, holes' y → holes y)
    (hdefined : ∀ y ∈ D, y.isCell = true → ∀ mm, (ctxOf S.placed pl).cell y = .ok mm →
      ReadableData holes' (mm.eval m.core) 8)
    {L : Nat} {tb : Block Loc} (htb : f.blocks[L]? = some tb) (hL : L ≠ 0) :
    Match S W { s with mem := mem', regs := regs', stack := { fr'' with label := L, pos := 0 } :: below.map (·.1) }
      (inFrame core' (UInt32.ofNat ((ctxOf S.placed pl).labelBase + L)) 0 m.returns) holes'
      { fr'' with label := L, pos := 0 } a ret below := by
  have hf'' : FnAt S fr''.fn f l pl := by rw [hafter.ctl.fn]; exact htop.fn
  obtain ⟨-, codes, post, t, hpos'⟩ := xlPos_start hf'' htb
  have := Match.update hm htop hwrites hafter hholes hdefined hpos'
  have hoff : offsetOf l L 0 codes = 0 := by simp [offsetOf, preOf, hL]
  rwa [machine_next hm.running, hoff] at this

/-- A jump: one checked step to the target label. -/
theorem step_jmp {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) (hpc : m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes))
    (hend : fr.pos = b.body.size) {e : Edge Loc} (hterm : b.term = .jmp e) {s' : Xl.State} {c : Bool}
    (hstep : Xl.takeEdge f s fr (below.map (·.1)) s.regs e = .next s' c) :
    ∃ m', SafeSteps Runtime.rejecting S.cs 1 holes m holes m' ∧ c.toNat ≤ 1 ∧
      Match S W s' m' holes { fr with label := e.target, pos := 0 } a ret below := by
  have hterm' := hpos.term
  rw [hterm] at hterm'
  simp only [FnCtx.term, bind, Except.bind, pure, Except.pure] at hterm'
  split at hterm'
  · simp at hterm'
  rename_i blk hedge
  simp only [Except.ok.injEq, Prod.mk.injEq] at hterm'
  obtain ⟨rfl, rfl⟩ := hterm'
  obtain ⟨hargs, hlt, rfl⟩ := edge_ok hedge
  have hlabels : (ctxOf S.placed pl).labels = f.blocks.size := by simp [ctxOf, htop.fn.pfunc]
  rw [hlabels] at hlt
  obtain ⟨tb, htb⟩ : ∃ tb, f.blocks[e.target]? = some tb := ⟨_, Array.getElem?_eq_getElem hlt⟩
  have hL : e.target ≠ 0 := by
    have := htop.fn.noEntryEdge b (List.mem_of_getElem? (by simpa using hpos.block))
    simpa [hterm, Term.succs, Term.edges, eq_comm] using this
  obtain ⟨hparams, -⟩ := xlPos_start htop.fn htb
  rw [takeEdge_empty hargs htb hparams] at hstep
  simp only [Sem.Step.next.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  -- The machine
  obtain ⟨hcode, -⟩ := hpos.blockCode
  have hlen : offsetOf l fr.label fr.pos codes = (preOf l fr.label ++ codes.flatten ++ []).length := by
    simp [offsetOf, hend, ← hpos.len, List.take_length]
  rw [hlen] at hpc
  have hvalid : S.cs.program.hasBlock (UInt32.ofNat ((ctxOf S.placed pl).labelBase + e.target)) = true := by
    obtain ⟨-, codes', post', t', hpos'⟩ := xlPos_start htop.fn htb
    exact (hpos'.blockCode.1).hasBlock
  have hstep := hcode.safe_jump hvalid Runtime.rejecting m.core m.returns holes
  rw [← machine_at hm.running hpc] at hstep
  refine ⟨_, hstep, by cases decide (e.target ≤ fr.label) <;> simp, ?_⟩
  have := Match.jump hm htop (D := []) (fun _ h => by cases h) (After.refl htop.agree) (fun _ h => h)
    (fun _ h => by cases h) htb hL
  exact this

/-- A branch: its producer and the jump, one checked step. -/
theorem step_jcc {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) (hpc : m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes))
    (hend : fr.pos = b.body.size) {p : Op} {pargs : List (XArg Loc)} {defs : List Loc} {cond : Condition}
    {e₁ e₂ : Edge Loc} (hterm : b.term = .jcc p pargs defs cond e₁ e₂) {bs : List (Bound Loc)}
    (hbs : bindRow p defs pargs = some bs) {regs' : Xl.Regs} {fr'' : Xl.Frame} {mem' : Memory}
    {flags : ByteEval.Flags} (hrun : Xl.execBound [(p, bs)] s.regs fr s.mem s.ctx = some (regs', fr'', mem', flags))
    {taken : Bool} (htk : jccTaken cond flags = some taken) {s' : Xl.State} {c : Bool}
    (hstep : Xl.takeEdge f { s with mem := mem' } fr'' (below.map (·.1)) regs' (if taken then e₁ else e₂) =
      .next s' c) :
    ∃ holes' m', SafeSteps Runtime.rejecting S.cs 1 holes m holes' m' ∧ c.toNat ≤ 1 ∧
      Match S W s' m' holes' { fr'' with label := (if taken then e₁ else e₂).target, pos := 0 } a ret below := by
  rw [hm.ctx] at hrun
  have hterm' := hpos.term
  rw [hterm] at hterm'
  simp only [FnCtx.term, FnCtx.bind, hbs, bind, Except.bind, pure, Except.pure] at hterm'
  have key : ∃ xs y n, (ctxOf S.placed pl).rowArgs bs = .ok xs ∧ rowShape p bs xs false = true ∧
      (ctxOf S.placed pl).edge e₁ = .ok y ∧ (ctxOf S.placed pl).edge e₂ = .ok n ∧
      post = [] ∧ t = .branch p xs cond y n := by
    split at hterm'
    · simp at hterm'
    rename_i xs hxs
    split at hterm'
    · rename_i hcond
      split at hterm'
      · simp at hterm'
      rename_i y hy
      split at hterm'
      · simp at hterm'
      rename_i n hn
      simp only [Except.ok.injEq, Prod.mk.injEq] at hterm'
      simp only [Bool.and_eq_true] at hcond
      exact ⟨xs, y, n, hxs, hcond.2, hy, hn, hterm'.1.symm, hterm'.2.symm⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at hterm'
  obtain ⟨xs, y, n, hxs, hshape, hy, hn, rfl, rfl⟩ := key
  obtain ⟨core', hex, hafter, hfoot, -⟩ := op_sim hbs hxs hshape htop.agree hrun
  rw [(bindRow_regs hbs).2] at hafter
  -- The target
  have hlabels : (ctxOf S.placed pl).labels = f.blocks.size := by simp [ctxOf, htop.fn.pfunc]
  obtain ⟨ha₁, hl₁, rfl⟩ := edge_ok hy
  obtain ⟨ha₂, hl₂, rfl⟩ := edge_ok hn
  rw [hlabels] at hl₁ hl₂
  have hsucc := htop.fn.noEntryEdge b (List.mem_of_getElem? (by simpa using hpos.block))
  rw [hterm] at hsucc
  simp only [Term.succs, Term.edges, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hsucc
  have hE : ∃ eT : Edge Loc, eT = (if taken then e₁ else e₂) ∧ eT.args = [] ∧ eT.target < f.blocks.size ∧
      eT.target ≠ 0 := by
    cases taken
    · exact ⟨e₂, rfl, ha₂, hl₂, fun h => hsucc.2 h.symm⟩
    · exact ⟨e₁, rfl, ha₁, hl₁, fun h => hsucc.1 h.symm⟩
  obtain ⟨eT, heT, hargs, hlt, hL⟩ := hE
  rw [← heT] at hstep ⊢
  obtain ⟨tb, htb⟩ : ∃ tb, f.blocks[eT.target]? = some tb := ⟨_, Array.getElem?_eq_getElem hlt⟩
  obtain ⟨hparams, -⟩ := xlPos_start htop.fn htb
  rw [takeEdge_empty hargs htb hparams] at hstep
  simp only [Sem.Step.next.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  -- The machine
  obtain ⟨hcode, -⟩ := hpos.blockCode
  have hlen : offsetOf l fr.label fr.pos codes = (preOf l fr.label ++ codes.flatten ++ []).length := by
    simp [offsetOf, hend, ← hpos.len, List.take_length]
  rw [hlen] at hpc
  have hsafe := hfoot.safe hm htop rfl fun u hu _ => by
    have h := hrun
    rw [Xl.execBound_eq] at h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Option.bind_eq_some_iff] at h
    obtain ⟨_, -, _, -, _, -, vs, hread, -⟩ := h
    exact readAll_some hread u hu
  have htested : flags.test cond = some taken := by rw [← jccTaken_eq]; exact htk
  have hvalid : S.cs.program.hasBlock
      (if taken then UInt32.ofNat ((ctxOf S.placed pl).labelBase + e₁.target)
        else UInt32.ofNat ((ctxOf S.placed pl).labelBase + e₂.target)) = true := by
    have : (if taken then UInt32.ofNat ((ctxOf S.placed pl).labelBase + e₁.target)
        else UInt32.ofNat ((ctxOf S.placed pl).labelBase + e₂.target)) =
        UInt32.ofNat ((ctxOf S.placed pl).labelBase + eT.target) := by
      rw [heT]; cases taken <;> rfl
    rw [this]
    obtain ⟨-, codes', post', t', hpos'⟩ := xlPos_start htop.fn htb
    exact (hpos'.blockCode.1).hasBlock
  have hstep := hcode.safe_branch Runtime.rejecting m.core m.returns holes hsafe hex htested hvalid
  rw [← machine_at hm.running hpc] at hstep
  have htarget : (if taken then UInt32.ofNat ((ctxOf S.placed pl).labelBase + e₁.target)
      else UInt32.ofNat ((ctxOf S.placed pl).labelBase + e₂.target)) =
      UInt32.ofNat ((ctxOf S.placed pl).labelBase + eT.target) := by
    rw [heT]; cases taken <;> rfl
  rw [htarget] at hstep
  refine ⟨_, _, hstep, by cases decide (eT.target ≤ fr''.label) <;> simp, ?_⟩
  exact Match.jump hm htop (D := defs)
    (fun r hr => facts_term (List.mem_of_getElem? (by simpa using hpos.block)) (by rw [hterm]; exact hr))
    hafter (fun y hy => nextHoles_op_sub y hy)
    (fun y hy hc mm hmm => nextHoles_op_clears (hfoot.defs y (by rw [(bindRow_regs hbs).2]; exact hy) hc mm hmm))
    htb hL

/-! ## Failures and traps -/

theorem EntryFrame.keep {ctx entrySp : Word} {core₀ : Core} {retAddr : Word} {s s' : Machine} {holes : Holes}
    (h : EntryFrame ctx entrySp core₀ retAddr s holes) (hc : s'.core = s.core) (hr : s'.returns = s.returns) :
    EntryFrame ctx entrySp core₀ retAddr s' holes :=
  ⟨by rw [hc]; exact h.cell, h.cellData, by rw [hr]; exact h.outer, fun i hi => by rw [hc]; exact h.saves i hi,
    h.savesData, by rw [hc]; exact h.r15, h.rsp0⟩

/-- A failure or a trap: a jump to the exit group's `fail_k`, which reaches
the wrapper's exit with status `k` and value 0. -/
theorem step_fail {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) (hpc : m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes))
    (hend : fr.pos = b.body.size) {k : Nat} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (ht : post = [] ∧ t = .jump ((ctxOf S.placed pl).failBlock k)) :
    ∃ n after, SafeSteps Runtime.rejecting S.cs n holes m holes after ∧
      Exit W.core₀ W.retAddr (UInt64.ofNat k) 0 after ∧ ReadableData holes (after.core.readReg .rsp) 8 := by
  obtain ⟨rfl, rfl⟩ := ht
  obtain ⟨hcode, -⟩ := hpos.blockCode
  have hlen : offsetOf l fr.label fr.pos codes = (preOf l fr.label ++ codes.flatten ++ []).length := by
    simp [offsetOf, hend, ← hpos.len, List.take_length]
  rw [hlen] at hpc
  have hexit : ExitGroupAt S.cs := fun j hj => exit_at S.ok hj
  have hfb : (ctxOf S.placed pl).failBlock k = UInt32.ofNat (k - 1) := by
    simp [FnCtx.failBlock, ctxOf]
  rw [hfb] at hcode
  have hvalid : S.cs.program.hasBlock (UInt32.ofNat (k - 1)) = true := (hexit.fail hk1 hk4).hasBlock
  have hjump := hcode.safe_jump hvalid Runtime.rejecting m.core m.returns holes
  rw [← machine_at hm.running hpc] at hjump
  have ef := hm.global.entry.keep (s' := inFrame m.core (UInt32.ofNat (k - 1)) 0 m.returns) rfl rfl
  obtain ⟨n, after, -, hrest, hexit'⟩ := Wrapper.fail_safe hexit Runtime.rejecting hk1 hk4 ef
    (by simp [inFrame]) rfl
  refine ⟨1 + n, after, hjump.append hrest, hexit', ?_⟩
  rw [hexit'.rsp, ef.rsp0]
  have := hm.global.entry.savesData 6 (by omega)
  simpa using this

end IxCC.Xv.Stacking.Proof
