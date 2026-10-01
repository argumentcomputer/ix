import Compilatrix.Xv.Stacking.Proof.TailMatch

/-!
# A tail call, step by step

`tailCall_safe`: a tail call's jump is one checked step to the callee's
first block. `epilogue_at`: at the end of a block whose code ends with the
epilogue, the epilogue's checked steps restore the saved registers and free
the frame. `tail_prologue`: from the callee's first label with `rsp` at the
tail caller's return slot, the prologue reaches the invariant for the tail
callee (`tail_match`). `step_tail`: an Xl tail call is matched by the
epilogue, the jump, the callee's stack check (if it has one) and its
prologue; or the check fails and the program exits with status 2.
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86 Compilatrix.X86.Stream

/-- A tail call's jump: one checked step to its target's first instruction. -/
theorem tailCall_safe {checked : Checked} {block target : BlockId} {instructions : List Instr}
    (code : BlockCode checked block instructions (.tailCall target))
    (valid : checked.program.hasBlock target = true)
    (runtime : Runtime) (core : Core) (returns : List ReturnFrame) (holes : Holes) :
    SafeSteps runtime checked 1 holes (inFrame core block instructions.length returns)
      holes (inFrame core target 0 returns) := by
  have safe : SafeAt checked.program holes (inFrame core block instructions.length returns) := by
    simp [SafeAt, inFrame, UInt32.toNat_ofNat_of_lt' code.fits, code.found]
  have hstep : X86.step runtime checked (inFrame core block instructions.length returns) =
      inFrame core target 0 returns := by
    rw [code.terminator_inFrame]
    simp [executeTerminator, Machine.goto, valid, inFrame]
  have one := SafeSteps.single safe hstep
  simpa only [code.holeStep, terminatorHoles] using one

/-- The epilogue at the end of a block: the saved registers come back, the
frame is freed, and the registers the caller expects back hold their entry
values. -/
theorem epilogue_at {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) (hpc : m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes))
    (hend : fr.pos = b.body.size) (hpost : post = epilogue l) :
    ∃ core₁ : Core, SafeSteps Runtime.rejecting S.cs (epilogue l).length holes m holes
        (inFrame core₁ (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
          (preOf l fr.label ++ codes.flatten ++ post).length m.returns) ∧
      core₁.memory = m.core.memory ∧ core₁.readReg .rsp = ret.returnSlot ∧
      (∀ r, r ∉ a.allow → r ≠ .rsp → core₁.readReg r = a.entry r) ∧
      (∀ r, r ≠ .rsp → r ∉ l.saved → core₁.readReg r = m.core.readReg r) := by
  subst hpost
  have hg := hm.global
  have hf := htop.fn
  have hs := hf.checks.1
  have hact := htop.act
  have span := hact.span hg.top
  have hbd := hs.bounded
  obtain ⟨hcode, hseg⟩ := hpos.blockCode
  have hoffEnd : offsetOf l fr.label fr.pos codes = (preOf l fr.label ++ codes.flatten).length := by
    simp [offsetOf, hend, ← hpos.len, List.take_length]
  have hoffLen : offsetOf l fr.label codes.length codes = (preOf l fr.label ++ codes.flatten).length := by
    simp [offsetOf, List.take_length]
  rw [hoffEnd] at hpc
  rw [hoffLen] at hseg
  have hm₀ := machine_at hm.running hpc
  have hfits := hcode.fits
  have hrd : ∀ r o, (r, o) ∈ l.saveOff → ∀ i < 8,
      m.core.memory.readable (a.sp + UInt64.ofNat o + UInt64.ofNat i) = true := by
    intro r o hro i hi
    have hsr := save_range hs hro
    have e : a.sp + UInt64.ofNat o + UInt64.ofNat i = a.sp + UInt64.ofNat (o + i) := by
      rw [UInt64.add_assoc, ← UInt64.ofNat_add]
    rw [e]
    exact (hg.stack _ (span.byte (o := o + i) (by omega)).2).2.2.1
  obtain ⟨core₁, hepi, hm₁, hr₁, hv₁, hk₁⟩ := epilogue_steps (returns := m.returns) (holes := holes) hs hseg
    (by simp only [List.length_append, UInt32.size] at hfits ⊢; omega) htop.rsp hrd
    (fun r o hro => hact.savesData r o hro)
  rw [← hm₀] at hepi
  have hkeep : ∀ r, r ∉ a.allow → r ≠ .rsp → core₁.readReg r = a.entry r := by
    intro r hr hsp
    by_cases hsv : r ∈ l.saved
    · obtain ⟨⟨r', o⟩, hro, e⟩ := List.mem_map.1 hsv
      simp only at e
      subst e
      rw [hv₁ _ o hro, hact.saves _ o hro]
    · rw [hk₁ r hsp hsv]
      rcases htop.kept r hr hsp with h | h
      · exact absurd h hsv
      · exact h
  refine ⟨core₁, ?_, hm₁, by rw [hr₁, hact.slot], hkeep, fun r hr hns => hk₁ r hr hns⟩
  simpa [List.length_append, Nat.add_assoc] using hepi

/-- A saved register is not one the running activation may change. -/
theorem saved_not_allowed {S : Stk} {W : Wrap} {mem : Memory} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hc : Chain S W mem holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (hf : FnAt S fr.fn f l pl)
    {gl : FrameLayout} {ga : Facts} (gs : gl.Sound ga) {r : GPR} (hr : r ∈ gl.saved) : r ∉ a.allow := by
  intro ha
  obtain ⟨g₀, gf₀, hgf₀, hallow₀⟩ := hc.allow hf
  obtain ⟨_, _, hfg₀⟩ := fnAt_of S hgf₀
  rw [hallow₀] at ha
  have hcs : r ∈ SysV.calleeSaved.toList := by
    rcases saved_mem gs hr with rfl | rfl | rfl | rfl <;> decide
  exact calleeSaved_not_callerSaved hcs (allowed_callerSaved hfg₀ ha)

/-- From the tail callee's first label, with `rsp` at the tail caller's
return slot: the prologue, then the invariant at the callee's first
instruction. -/
theorem tail_prologue {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) {g : Lir.FunId} {args : List Loc}
    (hterm : b.term = .tail g args) (hnA : args.length ≤ Xl.nArgRegs) (hconvA : Xl.conventionArgs args = true)
    {vals : List Word} (hread : Xl.readAll s.regs fr args = some vals) {callee : Xl.Frame} {regs' : Xl.Regs}
    (henter : Xl.enter S.p g vals = some (callee, regs'))
    {gf : Func Loc} {gl : FrameLayout} {gpl : Placed} (hfg : FnAt S g gf gl gpl)
    {b0 : Block Loc} {codes0 : List (List Instr)} {post0 : List Instr} {t0 : X86.Terminator}
    (hpos0 : XlPos S callee gf gl gpl b0 codes0 post0 t0) (hcl : callee.label = 0)
    {core' : Core} (h_rsp : core'.readReg .rsp = ret.returnSlot)
    (h_regs : ∀ r, r ≠ .rsp → r ≠ .r11 → r ∉ l.saved → core'.readReg r = m.core.readReg r)
    (h_kept : ∀ r, r ∉ a.allow → r ≠ .rsp → core'.readReg r = a.entry r)
    (h_mem : core'.memory = m.core.memory)
    (hlow : W.limit.toNat ≤ (ret.returnSlot - UInt64.ofNat gl.size).toNat)
    (hroom : gf.facts.calls = true → W.limit.toNat + slack ≤ (ret.returnSlot - UInt64.ofNat gl.size).toNat) :
    ∃ holes' m', SafeSteps Runtime.rejecting S.cs (prologue gl).length holes
        (inFrame core' (UInt32.ofNat ((ctxOf S.placed gpl).labelBase + 0)) 0 m.returns) holes' m' ∧
      Match S W { s with regs := regs', stack := callee :: below.map (·.1) } m' holes' callee
        (tailAct a ret.returnSlot gl) ret below := by
  have hg := hm.global
  have hf := htop.fn
  have hs := hf.checks.1
  have gs := hfg.checks.1
  have hact := htop.act
  have span := hact.span hg.top
  have hgbd := gs.bounded
  have hlo := hg.low
  have hlow₀ := span.low
  have hhigh := span.high
  have htopE := hg.top
  have hrs : ret.returnSlot.toNat = a.sp.toNat + l.size := by
    rw [hact.slot]; exact addr_toNat (by omega)
  have hgle : gl.size ≤ ret.returnSlot.toNat := by rw [hrs]; simp only [maxFrame, slack] at hlo hgbd; omega
  have hRc : (ret.returnSlot - UInt64.ofNat gl.size).toNat = ret.returnSlot.toNat - gl.size :=
    sub_ofNat_toNat hgle
  -- The prologue's code
  have hfound := hpos0.found
  rw [hcl] at hfound
  have hlist : ({ instructions := (preOf gl 0 ++ codes0.flatten ++ post0).toArray, terminator := t0 } :
      X86.Block).instructions.toList = [] ++ prologue gl ++ (codes0.flatten ++ post0) := by simp [preOf]
  obtain ⟨hk, hsz⟩ := block_fits (cs := S.cs) hfound
  have hfound' : S.cs.program.blocks[(UInt32.ofNat ((ctxOf S.placed gpl).labelBase + 0)).toNat]? =
      some { instructions := (preOf gl 0 ++ codes0.flatten ++ post0).toArray, terminator := t0 } := by
    rw [UInt32.toNat_ofNat_of_lt' hk]; exact hfound
  have hseg := Straight.Segment.of_block hfound' hlist
  simp only [List.length_nil] at hseg
  have hfits : (prologue gl).length < UInt32.size := by
    simp only [List.size_toArray, List.length_append, preOf, ↓reduceIte] at hsz
    simp only [UInt32.size]; omega
  have hw : ∀ x, (ret.returnSlot - UInt64.ofNat gl.size).toNat ≤ x.toNat → x.toNat < ret.returnSlot.toNat →
      core'.memory.writable x = true := fun x h₁ h₂ => by
    rw [h_mem]
    exact (hg.stack x ⟨by omega, by omega⟩).2.2.2
  have hdis : ∀ frame ∈ m.returns, ∀ i < 8, ret.returnSlot.toNat ≤ (frame.returnSlot + UInt64.ofNat i).toNat := by
    intro frame hfr i hi
    obtain ⟨-, h⟩ := hm.slot htop hfr hi
    rw [hrs]; omega
  obtain ⟨mem', holes', hst, hr', hw', hb', hv', hh', hd'⟩ :=
    prologue_steps (returns := m.returns) (holes := holes) gs hseg hfits h_rsp hgle hw hdis
  refine ⟨holes', _, hst, ?_⟩
  have hoff : offsetOf gl 0 0 codes0 = (prologue gl).length := by simp [offsetOf, preOf]
  have := tail_match hm htop hpos hterm hnA hconvA hread henter hfg hpos0
    (core_f := { core'.setReg .rsp (ret.returnSlot - UInt64.ofNat gl.size) with memory := mem' }) (holes_f := holes')
    (by simp [Core.readReg, Core.setReg, Registers.set])
    (fun r h1 h2 h3 => by
      show (core'.setReg .rsp _).readReg r = _
      rw [Validate.readReg_setReg, if_neg h1, h_regs r h1 h2 h3])
    (fun r h1 h2 => by
      show (core'.setReg .rsp _).readReg r = _
      rw [Validate.readReg_setReg, if_neg h2, h_kept r h1 h2])
    (by show mem'.readable = _; rw [hr', h_mem]) (by show mem'.writable = _; rw [hw', h_mem])
    (fun x hx => by
      show mem'.bytes x = _
      rw [hb' x hx, h_mem])
    (fun r o hro => by
      show mem'.read64 _ = _
      rw [hv' r o hro]
      exact h_kept r (saved_not_allowed hm.chain htop.fn gs (saveOff_mem hro)) (saved_ne_rsp gs (saveOff_mem hro)))
    hh' (fun r o hro => hd' r o hro) hlow hroom
  rwa [hoff] at this

/-- An Xl tail call: the epilogue, the jump to the callee, its stack check
and its prologue, after which the invariant holds for the callee in the
tail caller's place; or the check fails and the program exits with status
2. -/
theorem step_tail {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) (hpc : m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes))
    (hend : fr.pos = b.body.size) {g : Lir.FunId} {args : List Loc}
    (hterm : b.term = .tail g args) (hnA : args.length ≤ Xl.nArgRegs) (hconvA : Xl.conventionArgs args = true)
    {vals : List Word} (hread : Xl.readAll s.regs fr args = some vals) {callee : Xl.Frame} {regs' : Xl.Regs}
    (henter : Xl.enter S.p g vals = some (callee, regs')) :
    (∃ n holes' after, SafeSteps Runtime.rejecting S.cs n holes m holes' after ∧
      Exit W.core₀ W.retAddr 2 0 after ∧ ReadableData holes' (after.core.readReg .rsp) 8) ∨
    (∃ n holes' m' a', 1 ≤ n ∧ SafeSteps Runtime.rejecting S.cs n holes m holes' m' ∧
      Match S W { s with regs := regs', stack := callee :: below.map (·.1) } m' holes' callee a' ret below) := by
  -- The callee
  have henter' := henter
  simp only [Xl.enter, Option.bind_eq_bind, Option.bind_eq_some_iff] at henter'
  obtain ⟨gf, hgf, u, -, he⟩ := henter'
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨hcallee, -⟩ := he
  obtain ⟨gl, gpl, hfg⟩ := fnAt_of S hgf
  have hfn : callee.fn = g := by rw [← hcallee]
  have hcl : callee.label = 0 := by rw [← hcallee]
  obtain ⟨b0, hb0⟩ := first_block hfg
  have hfg' : FnAt S callee.fn gf gl gpl := by rw [hfn]; exact hfg
  obtain ⟨-, codes0, post0, t0, hpos0⟩ := xlPos_start hfg' hb0
  have hcalleeEq : { callee with label := 0, pos := 0 } = callee := by rw [← hcallee]
  rw [hcalleeEq] at hpos0
  -- The terminator's code
  have hterm' := hpos.term
  rw [hterm] at hterm'
  obtain ⟨entry, arity, hget, hpost, rfl⟩ := term_tail hterm'
  have hlay : (ctxOf S.placed pl).layout = l := by simp [ctxOf, htop.fn.play]
  rw [hlay] at hpost
  have hentry : entry = gpl.start := by
    have h1 := entry_of S g
    have h2 : (ctxOf S.placed pl).funcs = entriesOf S.placed := rfl
    rw [← h2, hget, hfg.placed] at h1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    exact h1.1
  subst hentry
  -- The tail caller
  have hg := hm.global
  have hf := htop.fn
  have hs := hf.checks.1
  have gs := hfg.checks.1
  have hact := htop.act
  have span := hact.span hg.top
  have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (by simpa using hpos.block)
  have hgbd := gs.bounded
  have hlo := hg.low
  have hlow₀ := span.low
  have hhigh := span.high
  have htopE := hg.top
  have hrs : ret.returnSlot.toNat = a.sp.toNat + l.size := by
    rw [hact.slot]; exact addr_toNat (by omega)
  have hgle : gl.size ≤ ret.returnSlot.toNat := by rw [hrs]; simp only [maxFrame, slack] at hlo hgbd; omega
  have hRc : (ret.returnSlot - UInt64.ofNat gl.size).toNat = ret.returnSlot.toNat - gl.size :=
    sub_ofNat_toNat hgle
  have hroomC := hm.chain.room hg hf
  -- The epilogue and the jump
  obtain ⟨core₁, hepi, hm₁, hr₁, hkeep, hk₁⟩ := epilogue_at hm htop hpos hpc hend hpost
  obtain ⟨hcode, -⟩ := hpos.blockCode
  have hfound0 := hpos0.found
  rw [hcl] at hfound0
  have hvalid : S.cs.program.hasBlock (UInt32.ofNat gpl.start) = true := by
    by_cases hc : FrameLayout.checked gf.facts gl = true
    · obtain ⟨pl', hpl', -, -, -, hblk⟩ := check_at S hfg.func hfg.layout hc
      have e : pl' = gpl := Option.some.inj (hpl'.symm.trans hfg.placed)
      subst e
      exact hasBlock_of hblk
    · have hsh : (ctxOf S.placed gpl).labelBase + 0 = gpl.start := by
        simp [ctxOf, shiftOf, hfg.play, hfg.pfacts, hc]
      rw [hsh] at hfound0
      exact hasBlock_of hfound0
  have hjmp := tailCall_safe hcode hvalid Runtime.rejecting core₁ m.returns holes
  have h15 : core₁.readReg .r15 = W.ctx := by
    rw [hk₁ _ (by decide) (fun h => by rcases saved_mem hs h with h | h | h | h <;> cases h)]
    exact htop.agree.ctxReg
  have hr11 : GPR.r11 ∈ allowedChanges S.env g gf → GPR.r11 ∈ a.allow := fun h =>
    hact.allowed _ (tail_allowed hf hbmem hterm hfg.func h)
  by_cases hc : FrameLayout.checked gf.facts gl = true
  · -- The stack check
    obtain ⟨pl', hpl', -, -, -, hblk⟩ := check_at S hfg.func hfg.layout hc
    have e : pl' = gpl := Option.some.inj (hpl'.symm.trans hfg.placed)
    subst e
    obtain ⟨hk, -⟩ := block_fits (cs := S.cs) hblk
    have hbc : BlockCode S.cs (UInt32.ofNat pl'.start) [Instr.lea .r11 (rspBelow (gl.size + slack))]
        (.branch cmpRM [.reg .r11, .mem stackLimitCell] .unsignedLt 1 (UInt32.ofNat (pl'.start + 1))) :=
      ⟨by rw [UInt32.toNat_ofNat_of_lt' (by simpa [UInt32.size] using hk)]; exact hblk, by simp [UInt32.size]⟩
    have hexit : ExitGroupAt S.cs := fun j hj => exit_at S.ok hj
    have h2 : S.cs.program.hasBlock 1 = true := (hexit.fail (k := 2) (by decide) (by decide)).hasBlock
    have hsh : (ctxOf S.placed pl').labelBase + 0 = pl'.start + 1 := by
      simp [ctxOf, shiftOf, hfg.play, hfg.pfacts, hc]
    have hn : S.cs.program.hasBlock (UInt32.ofNat (pl'.start + 1)) = true := by
      have := hfound0; rw [hsh] at this; exact hasBlock_of this
    have hlimOk : core₁.memory.read64? (core₁.readReg .r15 - 56) = .ok W.limit := by
      rw [h15, hm₁]
      simp only [Memory.read64?, Memory.read?]
      rw [if_pos ((rangeAllowed_iff _ _ _).2 fun j hj => by
        have hj8 : j < 8 := hj
        rw [ctx_56, UInt64.add_assoc, ← UInt64.ofNat_add]
        exact (hg.ctxCells (8 + j) (by omega)).2.2.1)]
      congr 1
      exact hg.limit
    have hdata : ReadableData holes (core₁.readReg .r15 - 56) 8 := by rw [h15]; exact hg.limitData
    have hchk := check_steps (returns := m.returns) hbc (by simp only [maxFrame, slack] at hgbd ⊢; omega) h2 hn
      hlimOk hdata
    rw [hr₁] at hchk
    by_cases hX : (ret.returnSlot - UInt64.ofNat (gl.size + slack)).toNat < W.limit.toNat
    · -- The check fails: the exit group, status 2
      left
      rw [if_pos hX] at hchk
      have hG₂ : Global W s.mem (inFrame (core₁.setReg .r11 (ret.returnSlot - UInt64.ofNat (gl.size + slack))) 1 0
          m.returns) holes := by
        refine Global.mono hg (by show core₁.memory.readable = _; rw [hm₁])
          (by show core₁.memory.writable = _; rw [hm₁]) (fun x _ => by show core₁.memory.bytes x = _; rw [hm₁])
          (fun x hx => .inl hx) ?_ hg.entry.outer
        show (core₁.setReg .r11 _).readReg .r15 = W.ctx
        rw [Validate.readReg_setReg, if_neg (by decide), h15]
      obtain ⟨n, after, -, hsafe, hexitE⟩ := Wrapper.fail_safe hexit Runtime.rejecting (k := 2) (by decide)
        (by decide) hG₂.entry rfl rfl
      refine ⟨(epilogue l).length + 1 + 2 + n, holes, after, ((hepi.append hjmp).append hchk).append hsafe,
        hexitE, ?_⟩
      rw [hexitE.rsp, hG₂.entry.rsp0]
      have := hG₂.entry.savesData 6 (by decide)
      simpa using this
    · -- The check passes: the prologue
      right
      rw [if_neg hX] at hchk
      have hXn : (ret.returnSlot - UInt64.ofNat (gl.size + slack)).toNat = ret.returnSlot.toNat - (gl.size + slack) :=
        sub_ofNat_toNat (by rw [hrs]; simp only [maxFrame, slack] at hlo hgbd ⊢; omega)
      obtain ⟨holes', m', hpro, hmatch⟩ := tail_prologue hm htop hpos hterm hnA hconvA hread henter hfg hpos0 hcl
        (core' := core₁.setReg .r11 (ret.returnSlot - UInt64.ofNat (gl.size + slack)))
        (by rw [Validate.readReg_setReg, if_neg (by decide), hr₁])
        (fun r h1 h2 h3 => by rw [Validate.readReg_setReg, if_neg h2, hk₁ r h1 h3])
        (fun r h1 h2 => by
          rw [Validate.readReg_setReg]
          split
          · rename_i e; subst e; exact absurd (hr11 (r11_allowed hfg hc)) h1
          · exact hkeep r h1 h2)
        (by show core₁.memory = _; exact hm₁) (by rw [hRc]; omega) (fun _ => by rw [hRc]; omega)
      rw [hsh] at hpro
      exact ⟨(epilogue l).length + 1 + 2 + (prologue gl).length, holes', m', _, by omega,
        ((hepi.append hjmp).append hchk).append hpro, hmatch⟩
  · -- No stack check: the prologue
    right
    have hsh : (ctxOf S.placed gpl).labelBase + 0 = gpl.start := by
      simp [ctxOf, shiftOf, hfg.play, hfg.pfacts, hc]
    obtain ⟨hsl, hnc⟩ := unchecked_slack gs hc
    obtain ⟨holes', m', hpro, hmatch⟩ := tail_prologue hm htop hpos hterm hnA hconvA hread henter hfg hpos0 hcl
      (core' := core₁) hr₁ (fun r h1 _ h3 => hk₁ r h1 h3) hkeep hm₁
      (by rw [hRc, hrs]; rw [hrs] at hgle; simp only [slack] at hsl hroomC ⊢; omega)
      (fun h => by rw [hnc] at h; cases h)
    rw [hsh] at hpro
    exact ⟨(epilogue l).length + 1 + (prologue gl).length, holes', m', _, by omega, (hepi.append hjmp).append hpro,
      hmatch⟩

end Compilatrix.Xv.Stacking.Proof
