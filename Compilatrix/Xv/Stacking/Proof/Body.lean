import Compilatrix.Xv.Stacking.Proof.Writes

/-!
# A body instruction keeps the invariant

When the running activation runs a body instruction other than a call
(`Match.body`): its frame agrees again (`After`, from the row lemmas), the
machine is past the instruction's code, every byte outside the cells it
defines that Xl cannot write is kept, and the holes only shrink, so the
running activation's saves and return slot, the suspended activations
(`Chain.mono`) and the wrapper's frame are kept.
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86 Compilatrix.X86.Stream

theorem Chain.retop {S : Stk} {W : Wrap} {mem : Memory} {holes : Holes} {fr fr' : Xl.Frame} {a : Act}
    {ret : ReturnFrame} (hfn : fr'.fn = fr.fn) :
    ∀ {below : List (Xl.Frame × Act × ReturnFrame)}, Chain S W mem holes fr a ret below →
      Chain S W mem holes fr' a ret below
  | [], h => fun f l pl hf => h f l pl (by rwa [hfn] at hf)
  | (_, _, _) :: _, ⟨hex, hlink, hrest⟩ =>
      ⟨hex, fun f l pl hf => hlink f l pl (by rwa [hfn] at hf), hrest⟩

theorem read64?_keep {mem mem' : Memory} {a : Word} (hp : mem'.readable = mem.readable)
    (h : ∀ i < 8, mem'.bytes (a + UInt64.ofNat i) = mem.bytes (a + UInt64.ofNat i)) :
    mem'.read64? a = mem.read64? a := by
  simp only [Memory.read64?, Memory.read?, hp]
  split
  · rw [show mem'.read .w64 a = mem.read .w64 a from read64_congr h]
  · rfl

/-- The bytes of a defined cell of the running frame. -/
theorem defCell_bytes {S : Stk} {W : Wrap} {mem : Memory} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {f : Func Loc} {l : FrameLayout} {pl : Placed} (hf : FnAt S fr.fn f l pl)
    (hact : ActFacts S W mem holes fr a ret f l) (htop : W.entrySp.toNat + 64 ≤ 2 ^ 64) {core : Core}
    (hrsp : core.readReg .rsp = a.sp) {y : Loc} {mm : MemAddr} (hm : (ctxOf S.placed pl).cell y = .ok mm) :
    ∃ o, CellAt l f.facts.inArgs y o ∧ o + 8 ≤ l.size + 8 + 8 * f.facts.inArgs ∧
      ∀ i < 8, (mm.eval core + UInt64.ofNat i).toNat = a.sp.toNat + o + i ∧ W.InStack (mm.eval core + UInt64.ofNat i) := by
  obtain ⟨o, hc, -, hr, hb⟩ := (hact.span htop).cell hf.checks.1 hf.play hf.pfacts hm hrsp
  exact ⟨o, hc, hr, hb⟩

/-- A body instruction other than a call: the invariant again, one
instruction on, from the frame's agreement after it. -/
theorem Match.update {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {D : List Loc} (hwrites : ∀ r, Loc.reg r ∈ D → r ∈ f.facts.writes)
    {regs' : Xl.Regs} {fr'' : Xl.Frame} {mem' : Memory} {core' : Core} {holes' : Holes}
    (hafter : After (ctxOf S.placed pl) D s.regs fr s.mem m.core regs' fr'' mem' W.ctx core')
    (hholes : ∀ y, holes' y → holes y)
    (hdefined : ∀ y ∈ D, y.isCell = true → ∀ mm, (ctxOf S.placed pl).cell y = .ok mm →
      ReadableData holes' (mm.eval m.core) 8)
    {L p : Nat} {b' : Block Loc} {codes' : List (List Instr)} {post' : List Instr} {t' : X86.Terminator}
    (hpos' : XlPos S { fr'' with label := L, pos := p } f l pl b' codes' post' t') :
    Match S W { s with mem := mem', regs := regs', stack := { fr'' with label := L, pos := p } :: below.map (·.1) }
      { m with core := core', pc := pcOf S pl L (offsetOf l L p codes') } holes'
      { fr'' with label := L, pos := p } a ret below := by
  have hg := hm.global
  have hf := htop.fn
  have hs := hf.checks.1
  have hact := htop.act
  have span := hact.span hg.top
  have hctl := hafter.ctl
  have hrsp' : core'.readReg .rsp = a.sp := by rw [hafter.rsp, htop.rsp]
  -- The defined cells' bytes lie in the frame.
  have hcellB : ∀ y ∈ D, y.isCell = true → ∀ mm, (ctxOf S.placed pl).cell y = .ok mm → ∀ i < 8,
      ∃ o, CellAt l f.facts.inArgs y o ∧ (mm.eval m.core + UInt64.ofNat i).toNat = a.sp.toNat + o + i ∧
        o + 8 ≤ l.size + 8 + 8 * f.facts.inArgs ∧ W.InStack (mm.eval m.core + UInt64.ofNat i) := by
    intro y _ _ mm hmm i hi
    obtain ⟨o, hc, hr, hb⟩ := defCell_bytes hf hact hg.top htop.rsp hmm
    exact ⟨o, hc, (hb i hi).1, hr, (hb i hi).2⟩
  -- A stack byte at a frame offset apart from every cell, or outside the frame, is kept.
  have hkeepStack : ∀ z, W.InStack z → (∀ y ∈ D, y.isCell = true → ∀ o, CellAt l f.facts.inArgs y o →
      ∀ i < 8, z.toNat ≠ a.sp.toNat + o + i) → core'.memory.bytes z = m.core.memory.bytes z := by
    intro z hz hne
    refine hafter.bytes z (hg.stack z hz).2.1 fun y hy hc mm hmm i hi e => ?_
    obtain ⟨o, hco, hto, -, -⟩ := hcellB y hy hc mm hmm i hi
    exact hne y hy hc o hco i hi (by rw [e, hto])
  have hkeepCtx : ∀ i < 16, core'.memory.bytes (W.ctx - 64 + UInt64.ofNat i) =
      m.core.memory.bytes (W.ctx - 64 + UInt64.ofNat i) := by
    intro i hi
    refine hafter.bytes _ (hg.ctxCells i hi).2.1 fun y hy hc mm hmm j hj e => ?_
    obtain ⟨o, -, -, -, hin⟩ := hcellB y hy hc mm hmm j hj
    exact hg.apart i hi (e ▸ hin)
  -- Above the frame, everything is kept.
  have hkeepAbove : ∀ z, a.sp.toNat + l.size + 8 + 8 * f.facts.inArgs ≤ z.toNat → z.toNat < W.entrySp.toNat + 64 →
      core'.memory.bytes z = m.core.memory.bytes z := by
    intro z h₁ h₂
    refine hkeepStack z ⟨by have := span.low; omega, h₂⟩ fun y hy hc o hco i hi e => ?_
    obtain ⟨-, hr, -⟩ := hco.range hs
    omega
  -- A frame byte apart from the cells is kept.
  have hkeepOff : ∀ o' j, j < 8 → o' + j < l.size + 8 + 8 * f.facts.inArgs →
      (∀ y o, CellAt l f.facts.inArgs y o → o + 8 ≤ o' ∨ o' + 8 ≤ o) →
      core'.memory.bytes (a.sp + UInt64.ofNat o' + UInt64.ofNat j) =
        m.core.memory.bytes (a.sp + UInt64.ofNat o' + UInt64.ofNat j) := by
    intro o' j hj hlt hsep
    have e : a.sp + UInt64.ofNat o' + UInt64.ofNat j = a.sp + UInt64.ofNat (o' + j) := by
      rw [UInt64.add_assoc, ← UInt64.ofNat_add]
    rw [e]
    obtain ⟨hto, hin⟩ := span.byte (o := o' + j) hlt
    refine hkeepStack _ hin fun y _ _ o hco i hi he => ?_
    rw [hto] at he
    have := hsep y o hco
    omega
  have hperm₁ : mem'.readable = s.mem.readable := hafter.readable₁
  have hperm₂ : mem'.writable = s.mem.writable := hafter.writable₁
  have hperm₃ : core'.memory.readable = m.core.memory.readable := hafter.readable₂
  have hperm₄ : core'.memory.writable = m.core.memory.writable := hafter.writable₂
  refine ⟨hm.running, rfl, hm.returns, hm.ctx, ⟨f, l, pl, ?_⟩, ?_, ?_⟩
  · refine ⟨by simpa [hctl.fn] using hf, ⟨b', codes', post', t', hpos', rfl⟩, ?_, hrsp', ?_, ?_, ?_, htop.room, ?_⟩
    · have ha := hafter.agree
      exact ⟨ha.size, ha.regsRel, ha.ctxReg, ha.inside, fun y hy v hv => ha.cells y hy v hv, ha.frame⟩
    · intro r hr hrsp
      by_cases hd : Loc.reg r ∈ D
      · have hw := hwrites r hd
        rcases write_allowed hf hw with hsv | hal
        · exact .inl hsv
        · exact absurd (hact.allowed r hal) hr
      · rw [hafter.regsKept r hd]
        exact htop.kept r hr hrsp
    · refine ⟨fun r o hro => ?_, fun r o hro => ?_, by simpa [hctl.fn] using hact.allowed, hact.slot, ?_,
        hact.snapshot, hact.align, hact.low, hact.high, hact.inBound⟩
      · have hsr := save_range hs hro
        rw [← hact.saves r o hro]
        exact read64_keep fun j hj => hkeepOff o j hj (by omega) fun y o' hco => (hco.apart_save hs hro)
      · exact fun i hi hh => hact.savesData r o hro i hi (hholes _ hh)
      · rw [← hact.retAddr, hact.slot]
        exact read64_keep fun j hj => hkeepOff l.size j hj (by omega) fun y o' hco => by
          obtain ⟨-, -, h⟩ := hco.range hs; omega
    · intro y hy v hv mm hmm
      have he : mm.eval core' = mm.eval m.core := cell_rsp hmm (by rw [hrsp', htop.rsp])
      rw [he]
      by_cases hd : y ∈ D
      · exact hdefined y hd hy mm hmm
      · have hv' : Xl.read s.regs fr y = some v := by rw [← hafter.locs y hd]; exact hv
        exact fun i hi hh => htop.cellsData y hy v hv' mm hmm i hi (hholes _ hh)
    · rw [hctl.inArgs]; exact htop.inArgs
  · refine Chain.mono (B := a.sp.toNat + l.size + 8 + 8 * f.facts.inArgs) hg.top
      (fun z h₁ h₂ => hkeepAbove z h₁ (by omega)) (fun z hz => .inl (hholes z hz))
      (Chain.retop (by simp [hctl.fn]) hm.chain) ?_
    intro fr₁ a₁ ret₁ rest e f₁ l₁ pl₁ hf₁
    have hc := hm.chain
    rw [e] at hc
    obtain ⟨-, hlink, -⟩ := hc
    exact (hlink f l pl hf f₁ l₁ pl₁ hf₁).1.room
  · refine ⟨fun z hz => ?_, fun i hi => ?_, hg.apart, fun z hz => ?_, ?_, ?_, ?_, hg.top, hg.low⟩
    · rw [hperm₁, hperm₂, hperm₃, hperm₄]; exact hg.stack z hz
    · rw [hperm₁, hperm₂, hperm₃, hperm₄]; exact hg.ctxCells i hi
    · rw [hperm₁, hperm₂]; exact hg.holesFree z (hholes z hz)
    · have he := hg.entry
      have hctxKeep : ∀ i < 8, core'.memory.bytes (W.ctx - 64 + UInt64.ofNat i) =
          m.core.memory.bytes (W.ctx - 64 + UInt64.ofNat i) := fun i hi => hkeepCtx i (by omega)
      refine ⟨?_, fun i hi hh => he.cellData i hi (hholes _ hh), he.outer, fun i hi => ?_,
        fun i hi j hj hh => he.savesData i hi j hj (hholes _ hh), ?_, he.rsp0⟩
      · rw [← he.cell]
        exact read64?_keep hperm₃ (by simpa using hctxKeep)
      · rw [← he.saves i hi]
        refine read64?_keep hperm₃ fun j hj => ?_
        have hb : (W.entrySp + UInt64.ofNat (8 + 8 * i) + UInt64.ofNat j).toNat = W.entrySp.toNat + (8 + 8 * i) + j := by
          rw [addr_toNat (by rw [addr_toNat (by have := hg.top; omega)]; have := hg.top; omega),
            addr_toNat (by have := hg.top; omega)]
        refine hkeepAbove _ ?_ ?_
        · rw [hb]; have := span.high; omega
        · rw [hb]; omega
      · show core'.readReg .r15 = W.ctx
        exact hafter.agree.ctxReg
    · have h56 : W.ctx - 56 = W.ctx - 64 + UInt64.ofNat 8 := by
        rw [UInt64.sub_eq_add_neg, UInt64.sub_eq_add_neg, UInt64.add_assoc]
        congr 1
      rw [← hg.limit, h56]
      exact read64_keep fun j hj => by
        rw [UInt64.add_assoc, ← UInt64.ofNat_add, hkeepCtx (8 + j) (by omega)]
    · exact fun i hi hh => hg.limitData i hi (hholes _ hh)

/-- A body instruction other than a call: the invariant again, one
instruction on. -/
theorem Match.body {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) {x : Inst Loc} (hx : b.body[fr.pos]? = some x)
    {regs' : Xl.Regs} {fr'' : Xl.Frame} {mem' : Memory} {core' : Core} {holes' : Holes}
    (hafter : After (ctxOf S.placed pl) x.defs s.regs fr s.mem m.core regs' fr'' mem' W.ctx core')
    (hholes : ∀ y, holes' y → holes y)
    (hdefined : ∀ y ∈ x.defs, y.isCell = true → ∀ mm, (ctxOf S.placed pl).cell y = .ok mm →
      ReadableData holes' (mm.eval m.core) 8) :
    Match S W { s with mem := mem', regs := regs', stack := { fr'' with pos := fr.pos + 1 } :: below.map (·.1) }
      { m with core := core', pc := pcOf S pl fr.label (offsetOf l fr.label (fr.pos + 1) codes) } holes'
      { fr'' with pos := fr.pos + 1 } a ret below := by
  have hctl := hafter.ctl
  have hlt : fr.pos < b.body.size := (List.getElem?_eq_some_iff.1 (by simpa using hx)).1
  have e : { fr'' with label := fr.label, pos := fr.pos + 1 } = { fr'' with pos := fr.pos + 1 } := by
    rw [← hctl.label]
  have hpos' : XlPos S { fr'' with label := fr.label, pos := fr.pos + 1 } f l pl b codes post t :=
    ⟨hpos.block, hpos.found, hpos.len, hpos.insts, hpos.term, by show fr.pos + 1 ≤ b.body.size; omega⟩
  have := Match.update hm htop (D := x.defs)
    (fun r hd => facts_inst (List.mem_of_getElem? (by simpa using hpos.block))
      (List.mem_of_getElem? (by simpa using hx)) hd) hafter hholes hdefined hpos'
  rwa [e] at this

end Compilatrix.Xv.Stacking.Proof
