import Compilatrix.Xv.Stacking.Proof.StepCall

/-!
# The invariant at a callee's first instruction

`call_match`: when Xl calls `g` from the running activation, and the
machine has called `g`'s first block, passed its stack check and run its
prologue (with the core, memory and holes that leaves, as hypotheses), the
invariant holds for the callee at its first instruction: its registers are
its arguments, its incoming cells are the caller's outgoing ones, its saves
and return slot are in place, and the caller is suspended and linked to it.
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86 Compilatrix.X86.Stream

/-- The callee at entry. -/
def calleeAct (S : Stk) (g : Lir.FunId) (gf : Func Loc) (gl : FrameLayout) (sp : Word) (C : Core) : Act :=
  ⟨sp - 8 - UInt64.ofNat gl.size, C.readReg, allowedChanges S.env g gf, C.readReg⟩

theorem call_match {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) {g : Lir.FunId} {args rets : List Loc}
    (hx : b.body[fr.pos]? = some (.call g args rets)) (hconvA : Xl.conventionArgs args = true)
    {entry : X86.BlockId} (hcode : codes[fr.pos]? = some [.call entry])
    {vals : List Word} (hread : Xl.readAll s.regs fr args = some vals) {callee : Xl.Frame} {regs' : Xl.Regs}
    (henter : Xl.enter S.p g vals = some (callee, regs'))
    {gf : Func Loc} {gl : FrameLayout} {gpl : Placed} (hfg : FnAt S g gf gl gpl)
    {b0 : Block Loc} {codes0 : List (List Instr)} {post0 : List Instr} {t0 : X86.Terminator}
    (hpos0 : XlPos S callee gf gl gpl b0 codes0 post0 t0)
    {core_f : Core} {holes_f : Holes}
    (hf_rsp : core_f.readReg .rsp = a.sp - 8 - UInt64.ofNat gl.size)
    (hf_regs : ∀ r, r ≠ .rsp → r ≠ .r11 → core_f.readReg r = m.core.readReg r)
    (hf_r11 : core_f.readReg .r11 ≠ m.core.readReg .r11 → GPR.r11 ∈ allowedChanges S.env g gf)
    (hf_r : core_f.memory.readable = m.core.memory.readable) (hf_w : core_f.memory.writable = m.core.memory.writable)
    (hf_bytes : ∀ x, ¬((a.sp - 8 - UInt64.ofNat gl.size).toNat ≤ x.toNat ∧ x.toNat < a.sp.toNat) →
      core_f.memory.bytes x = m.core.memory.bytes x)
    (hf_ret : core_f.memory.read64 (a.sp - 8) =
      (callFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
        (offsetOf l fr.label fr.pos codes)).continuation.encode)
    (hf_saves : ∀ r o, (r, o) ∈ gl.saveOff →
      core_f.memory.read64 (a.sp - 8 - UInt64.ofNat gl.size + UInt64.ofNat o) = m.core.readReg r)
    (hh : ∀ x, holes_f x → holes x ∨ ((a.sp - 8).toNat ≤ x.toNat ∧ x.toNat < a.sp.toNat))
    (hsd : ∀ r o, (r, o) ∈ gl.saveOff → ReadableData holes_f (a.sp - 8 - UInt64.ofNat gl.size + UInt64.ofNat o) 8)
    (hlow : W.limit.toNat ≤ (a.sp - 8 - UInt64.ofNat gl.size).toNat)
    (hroom : gf.facts.calls = true → W.limit.toNat + slack ≤ (a.sp - 8 - UInt64.ofNat gl.size).toNat) :
    Match S W { s with regs := regs', stack := (callee :: Xl.suspend fr s.regs (S.env.clobbers g) rets.length ::
        below.map (·.1)) }
      (inFrame core_f (UInt32.ofNat ((ctxOf S.placed gpl).labelBase + 0)) (offsetOf gl 0 0 codes0)
        (callFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
          (offsetOf l fr.label fr.pos codes) :: m.returns))
      holes_f callee (calleeAct S g gf gl a.sp m.core)
      (callFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label)) (offsetOf l fr.label fr.pos codes))
      ((Xl.suspend fr s.regs (S.env.clobbers g) rets.length, { a with regs := m.core.readReg }, ret) :: below) := by
  -- The callee
  simp only [Xl.enter, Option.bind_eq_bind, Option.bind_eq_some_iff] at henter
  obtain ⟨gf', hgf', u, hguard, he⟩ := henter
  have hgf : gf' = gf := Option.some.inj (hgf'.symm.trans hfg.func)
  subst hgf
  have hplen : gf'.params.length = vals.length := by
    by_cases hl : gf'.params.length = vals.length
    · exact hl
    · simp [guard, hl] at hguard
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  -- The caller's facts
  have hg := hm.global
  have hf := htop.fn
  have hs := hf.checks.1
  have gs := hfg.checks.1
  have hact := htop.act
  have span := hact.span hg.top
  have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (by simpa using hpos.block)
  have himem : Inst.call g args rets ∈ b.body.toList := List.mem_of_getElem? (by simpa using hx)
  have hcalls : f.facts.calls = true := facts_calls hbmem himem
  have hSc := hs.calls hcalls
  have hroomC := htop.room hcalls
  have hal16 := hs.aligned16 hSc
  have hgbd := gs.bounded
  have hbd := hs.bounded
  have hlo := hg.low
  have hhigh := span.high
  have hal := hact.align
  have hfit := hs.outArgsFit
  have htopE := hg.top
  have hRsp : m.core.readReg .rsp = a.sp := htop.rsp
  obtain ⟨hlenA, hgetA⟩ := readAll_get hread
  have hkle := call_inArgs_le hf hbmem himem hconvA
  have hkin : gf'.facts.inArgs = args.length - Xl.nArgRegs := by rw [facts_inArgs, hplen, hlenA]
  -- Numbers
  have hR8 : (a.sp - 8).toNat = a.sp.toNat - 8 := sub8_toNat (by simp only [maxFrame, slack] at hlo; omega)
  have hRc : (a.sp - 8 - UInt64.ofNat gl.size).toNat = a.sp.toNat - 8 - gl.size := by
    rw [sub_ofNat_toNat (by rw [hR8]; simp only [maxFrame, slack] at hlo hgbd; omega), hR8]
  have hRmod : a.sp.toNat % 16 = 0 := by omega
  -- The callee's frame on the stack
  have gspan : FrameSpan W (a.sp - 8 - UInt64.ofNat gl.size) gl gf'.facts.inArgs :=
    ⟨hlow, by rw [hRc]; simp only [maxFrame, slack] at hlo; omega, by rw [hkin]; omega, htopE⟩
  -- Bytes at or above the caller's stack pointer are kept
  have hkeepUp : ∀ x, a.sp.toNat ≤ x.toNat → core_f.memory.bytes x = m.core.memory.bytes x := fun x hx =>
    hf_bytes x fun ⟨_, h⟩ => by omega
  have hInStack : ∀ x, (a.sp - 8 - UInt64.ofNat gl.size).toNat ≤ x.toNat → x.toNat < a.sp.toNat → W.InStack x :=
    fun x h₁ h₂ => ⟨by omega, by omega⟩
  have hbytesG : ∀ x, (¬W.InStack x ∨ W.entrySp.toNat ≤ x.toNat) → core_f.memory.bytes x = m.core.memory.bytes x :=
    fun x hx => hf_bytes x fun ⟨h₁, h₂⟩ => by
      rcases hx with hx | hx
      · exact hx (hInStack x h₁ h₂)
      · omega
  have hholesG : ∀ x, holes_f x → holes x ∨ (W.InStack x ∧ x.toNat < W.entrySp.toNat) := fun x hx => by
    rcases hh x hx with h | ⟨h₁, h₂⟩
    · exact .inl h
    · exact .inr ⟨⟨by rw [hR8] at h₁; omega, by omega⟩, by omega⟩
  have hreg15 : core_f.readReg .r15 = W.ctx := by
    rw [hf_regs _ (by decide) (by decide)]; exact htop.agree.ctxReg
  -- The global facts
  have hglob : Global W s.mem (inFrame core_f (UInt32.ofNat ((ctxOf S.placed gpl).labelBase + 0))
      (offsetOf gl 0 0 codes0) (callFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
        (offsetOf l fr.label fr.pos codes) :: m.returns)) holes_f := by
    refine Global.mono hg hf_r hf_w hbytesG hholesG hreg15 ?_
    rcases hg.entry.outer with h | ⟨inner, f₁, h, h₁, h₂⟩
    · rw [hm.returns] at h; cases h
    · refine .inr ⟨callFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
        (offsetOf l fr.label fr.pos codes) :: inner, f₁, by simp only [inFrame, h, List.cons_append], h₁, fun g hg' => ?_⟩
      rcases List.mem_cons.1 hg' with rfl | hg'
      · intro e
        have := congrArg UInt64.toNat e
        simp only [callFrame, hRsp] at this
        rw [show a.sp - 8 + 8 = a.sp by simp] at this
        omega
      · exact h₂ g hg'
  -- The caller's outgoing cell `i` holds the callee's incoming argument `i`.
  have hout : ∀ i v, (vals.drop Xl.nArgRegs)[i]? = some v →
      i < gf'.facts.inArgs ∧ ∃ mm, (ctxOf S.placed pl).cell (.outArg i) = .ok mm ∧
        m.core.memory.read64 (mm.eval m.core) = v ∧ ReadableData holes (mm.eval m.core) 8 ∧
        mm.eval m.core = a.sp + UInt64.ofNat (8 * i) ∧ i < l.outArgs := by
    intro i v hv
    rw [List.getElem?_drop] at hv
    have hlt : Xl.nArgRegs + i < args.length := by rw [← hlenA]; exact (List.getElem?_eq_some_iff.1 hv).1
    have harg := conventionArgs_get hconvA hlt
    rw [argLoc_out (by omega), show Xl.nArgRegs + i - Xl.nArgRegs = i by omega] at harg
    obtain ⟨v', hv', hrd⟩ := hgetA _ _ harg
    have e : v' = v := Option.some.inj (hv'.symm.trans hv)
    subst e
    obtain ⟨mm, hmm, hmv⟩ := htop.agree.cells (.outArg i) rfl v' hrd
    obtain ⟨o, hco, rfl⟩ := cell_off hmm
    rw [hf.play] at hco
    cases hco with
    | outArg hi =>
      refine ⟨by rw [hkin]; omega, rspAt (8 * i), hmm, hmv, htop.cellsData _ rfl v' hrd _ hmm, ?_, hi⟩
      rw [rspAt_eval (by simp only [maxFrame, slack] at hbd; omega), hRsp]
  -- The callee's incoming cell `i`
  have hcellG : ∀ i, i < gf'.facts.inArgs →
      (ctxOf S.placed gpl).cell (.inArg i) = .ok (rspAt (gl.size + 8 + 8 * i)) := by
    intro i hi
    simp only [FnCtx.cell, ctxOf, hfg.pfacts, hfg.play, hi, ↓reduceIte]; rfl
  have hevalG : ∀ i, i < l.outArgs →
      (rspAt (gl.size + 8 + 8 * i)).eval core_f = a.sp + UInt64.ofNat (8 * i) := by
    intro i hi
    rw [rspAt_eval (by simp only [maxFrame, slack] at hgbd hbd; omega), hf_rsp]
    apply word_eq
    rw [addr_toNat (by rw [hRc]; omega), hRc, addr_toNat (by omega)]
    simp only [maxFrame, slack] at hlo hgbd
    omega
  have hupData : ∀ y, ReadableData holes y 8 → (∀ j < 8, a.sp.toNat ≤ (y + UInt64.ofNat j).toNat) →
      ReadableData holes_f y 8 := fun y hy hge j hj hx => by
    rcases hh _ hx with h | ⟨-, h₂⟩
    · exact hy j hj h
    · have := hge j hj; omega
  have hupTo : ∀ i, i < l.outArgs → ∀ j < 8, a.sp.toNat ≤ (a.sp + UInt64.ofNat (8 * i) + UInt64.ofNat j).toNat := by
    intro i hi j hj
    rw [addr_toNat (by rw [addr_toNat (by omega)]; omega), addr_toNat (by omega)]
    omega
  refine ⟨rfl, rfl, by simp [inFrame, hm.returns], hm.ctx, ⟨gf', gl, gpl, ?_⟩, ?_, hglob⟩
  · -- The callee's running activation
    refine ⟨hfg, ⟨b0, codes0, post0, t0, hpos0, rfl⟩, ⟨entryRegs_size vals, ?_, hreg15, ?_, ?_, ?_⟩, hf_rsp, ?_, ?_,
      ?_, hroom, ?_⟩
    · intro r hr v hv
      obtain ⟨i, hri, hvi⟩ := entryRegs_get hv
      have hrmem : r ∈ Lir.Conv.argRegs := List.mem_of_getElem? hri
      have hia : i < args.length := by rw [← hlenA]; exact (List.getElem?_eq_some_iff.1 hvi).1
      have harg := conventionArgs_get hconvA hia
      rw [argLoc_reg hri] at harg
      obtain ⟨v', hv', hrd⟩ := hgetA _ _ harg
      have e : v' = v := Option.some.inj (hv'.symm.trans hvi)
      subst e
      rw [Xl.read_reg hr] at hrd
      have hne1 : r ≠ .rsp := by intro e; subst e; simp [Lir.Conv.argRegs] at hrmem
      have hne2 : r ≠ .r11 := by intro e; subst e; simp [Lir.Conv.argRegs] at hrmem
      show core_f.readReg r = v'
      rw [hf_regs r hne1 hne2]
      exact htop.agree.regsRel r hr v' hrd
    · have hin := htop.agree.inside
      show Inside s.mem core_f.memory
      refine ⟨fun x hx => by rw [hf_r]; exact hin.readable x hx, fun x hx => by rw [hf_w]; exact hin.writable x hx,
        fun x hx => ?_⟩
      rw [hf_bytes x fun ⟨h₁, h₂⟩ => ?_]
      · exact hin.bytes x hx
      · have hst := hg.stack x (hInStack x h₁ h₂)
        rcases hx with hx | hx
        · rw [hst.1] at hx; cases hx
        · rw [hst.2.1] at hx; cases hx
    · intro x hx v hv
      cases x with
      | reg r => simp [Loc.isCell] at hx
      | slot i => simp [Xl.read] at hv
      | outArg i => simp [Xl.read] at hv
      | inArg i =>
        have hv' : (vals.drop Xl.nArgRegs)[i]? = some v := by simpa [Xl.read] using hv
        obtain ⟨hlt, mm, hmm, hmv, -, heval, hil⟩ := hout i v hv'
        refine ⟨_, hcellG i hlt, ?_⟩
        show core_f.memory.read64 ((rspAt (gl.size + 8 + 8 * i)).eval core_f) = v
        rw [hevalG i hil, ← heval, ← hmv]
        exact read64_keep fun j hj => hkeepUp _ (by rw [heval]; exact hupTo i hil j hj)
    · exact frameCells_of hglob gs gspan hfg.play hfg.pfacts hf_rsp
    · intro r hr hsp
      right
      by_cases h11 : r = .r11
      · subst h11
        show core_f.readReg .r11 = m.core.readReg .r11
        by_cases hne : core_f.readReg .r11 = m.core.readReg .r11
        · exact hne
        · exact absurd (hf_r11 hne) hr
      · exact hf_regs r hsp h11
    · refine ⟨fun r o hro => hf_saves r o hro, fun r o hro => hsd r o hro, fun r hr => hr, ?_, ?_, rfl,
        ?_, hlow, gspan.high, gspan.inBound⟩
      · simp only [callFrame, calleeAct, hRsp]
        exact (UInt64.sub_add_cancel _ _).symm
      · simp only [callFrame, hRsp]
        exact hf_ret
      · simp only [calleeAct]; rw [hRc]; omega
    · intro x hx v hv mm hmm
      cases x with
      | reg r => simp [Loc.isCell] at hx
      | slot i => simp [Xl.read] at hv
      | outArg i => simp [Xl.read] at hv
      | inArg i =>
        have hv' : (vals.drop Xl.nArgRegs)[i]? = some v := by simpa [Xl.read] using hv
        obtain ⟨hlt, mm', hmm', -, hdata, heval, hil⟩ := hout i v hv'
        rw [hcellG i hlt] at hmm
        cases hmm
        show ReadableData holes_f ((rspAt (gl.size + 8 + 8 * i)).eval core_f) 8
        rw [hevalG i hil]
        rw [heval] at hdata
        exact hupData _ hdata (hupTo i hil)
    · show ((vals.drop Xl.nArgRegs).toArray).size = gf'.facts.inArgs
      rw [hkin]; simp [hlenA]
  · -- The suspended caller
    refine ⟨⟨f, l, pl, hf⟩, fun f₀ l₀ pl₀ hf₀ f₁ l₁ pl₁ hf₁ => ?_, ?_⟩
    · obtain ⟨e₁, e₂, e₃⟩ := hfg.unique hf₀
      obtain ⟨e₄, e₅, e₆⟩ := hf.unique hf₁
      subst e₁ e₂ e₃ e₄ e₅ e₆
      have hpos1 : fr.pos < b.body.size := (List.getElem?_eq_some_iff.1 (by simpa using hx)).1
      refine ⟨⟨⟨b, codes, post, t, ⟨hpos.block, hpos.found, hpos.len, hpos.insts, hpos.term,
          by show fr.pos + 1 ≤ b.body.size; omega⟩, ?_⟩, ?_, fun r _ => rfl,
          ⟨b, g, args, rets, _, hpos.block, by simpa [Xl.suspend] using hx, hfg.func, rfl⟩, ?_⟩, ?_, ?_⟩
      · simp only [callFrame, pcOf, Xl.suspend, offsetOf_succ hcode, List.length_singleton]
      · simp only [calleeAct]; rw [hRc]; simp only [maxFrame, slack] at hlo hgbd; omega
      · simp only [calleeAct]; rw [hRc, hkin]; simp only [maxFrame, slack] at hlo hgbd; omega
      · have h := ActFacts.mono (fr' := Xl.suspend fr s.regs (S.env.clobbers g) rets.length) hact hf rfl htopE
          (B := a.sp.toNat) (by omega) (fun x h₁ _ => hkeepUp x h₁)
          (fun x hx => by rcases hh x hx with h | ⟨-, h⟩; exact .inl h; exact .inr h)
        exact ⟨h.saves, h.savesData, h.allowed, h.slot, h.retAddr, h.snapshot, h.align, h.low, h.high, h.inBound⟩
      · refine ⟨⟨b, g, args, rets, hpos.block, by simp [Xl.suspend], by simpa [Xl.suspend] using hx, rfl, rfl⟩,
          fun i => by simp [Xl.suspend], htop.agree.size, htop.agree.regsRel, htop.agree.ctxReg, hRsp,
          fun r hr hsp => htop.kept r hr hsp, fun x hx v hv => ?_, htop.inArgs⟩
        have hv' : Xl.read s.regs fr x = some v := by
          cases x with
          | reg r => simp [Loc.isCell] at hx
          | outArg i => simp [Xl.read, Xl.suspend] at hv
          | _ => simpa [Xl.read, Xl.suspend] using hv
        obtain ⟨mm, hmm, hmv⟩ := htop.agree.cells x hx v hv'
        have he : mm.eval (atSp a.sp) = mm.eval m.core := cell_rsp hmm (by rw [hRsp]; rfl)
        obtain ⟨o', -, -, -, hb'⟩ := span.cell hs hf.play hf.pfacts hmm hRsp
        refine ⟨mm, hmm, ?_, ?_⟩
        · rw [he, ← hmv]
          exact read64_keep fun j hj => hkeepUp _ (by rw [(hb' j hj).1]; omega)
        · rw [he]
          exact hupData _ (htop.cellsData x hx v hv' mm hmm) (fun j hj => by rw [(hb' j hj).1]; omega)
    · have hc := Chain.react (a := a) (a' := { a with regs := m.core.readReg }) rfl rfl rfl
        (Chain.retop (fr := fr) (fr' := Xl.suspend fr s.regs (S.env.clobbers g) rets.length) rfl hm.chain)
      refine Chain.mono (B := a.sp.toNat + l.size + 8 + 8 * f.facts.inArgs) htopE
        (fun x h₁ _ => hkeepUp x (by omega))
        (fun x hx => by rcases hh x hx with h | ⟨-, h⟩; exact .inl h; exact .inr (by omega)) hc ?_
      intro fr₁ a₁ ret₁ rest e f₁ l₁ pl₁ hf₁
      have hc0 := hm.chain
      rw [e] at hc0
      obtain ⟨-, hlink, -⟩ := hc0
      exact (hlink f l pl hf f₁ l₁ pl₁ hf₁).1.room

end Compilatrix.Xv.Stacking.Proof
