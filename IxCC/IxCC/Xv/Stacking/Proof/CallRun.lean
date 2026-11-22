import IxCC.Xv.Stacking.Proof.CallMatch

/-!
# A call, step by step

`prologue_match`: from the callee's first block with the return address
pushed, the prologue's checked steps reach the invariant at the callee's
first instruction. `step_call`: an Xl call is matched by the stacked call,
the callee's stack check and its prologue, or the check fails and the
program exits with status 2.
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

/-- Every function has a layout and a placement. -/
theorem fnAt_of (S : Stk) {k : Lir.FunId} {f : Func Loc} (hf : S.p.funcs[k]? = some f) :
    ∃ l pl, FnAt S k f l pl := by
  obtain ⟨hlen, -⟩ := run_ok S.ok
  have hk : k < S.layouts.length := by rw [hlen]; exact (Array.getElem?_eq_some_iff.1 hf).1
  obtain ⟨l, hl⟩ : ∃ l, S.layouts[k]? = some l := ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨pl, blks, hpl, h1, -, h3, h4, -⟩ := func_at S.ok hf hl
  exact ⟨l, pl, ⟨hf, hl, hpl, h1, h3, h4⟩⟩

theorem hasBlock_of {cs : Checked} {k : Nat} {blk : X86.Block} (h : cs.program.blocks[k]? = some blk) :
    cs.program.hasBlock (UInt32.ofNat k) = true := by
  obtain ⟨hk, -⟩ := block_fits h
  simp only [Program.hasBlock, decide_eq_true_eq, UInt32.toNat_ofNat_of_lt' (by simpa [UInt32.size] using hk)]
  exact (Array.getElem?_eq_some_iff.1 h).1

theorem write64_bytes_off {mem : Memory} {Q v x : Word} (hQ : Q.toNat + 8 ≤ 2 ^ 64)
    (hx : ¬(Q.toNat ≤ x.toNat ∧ x.toNat < Q.toNat + 8)) : (mem.write64 Q v).bytes x = mem.bytes x :=
  Memory.write64_bytes_outside _ _ _ _ fun i hi e => hx (by
    subst e; rw [addr_toNat (by omega)]; omega)

/-- From the callee's first block, after the call: the prologue, then the
invariant at the callee's first instruction. -/
theorem prologue_match {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
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
    (hpos0 : XlPos S callee gf gl gpl b0 codes0 post0 t0) (hcl : callee.label = 0)
    {core' : Core} {holes₁ : Holes}
    (h_rsp : core'.readReg .rsp = a.sp - 8)
    (h_regs : ∀ r, r ≠ .rsp → r ≠ .r11 → core'.readReg r = m.core.readReg r)
    (h_r11 : core'.readReg .r11 ≠ m.core.readReg .r11 → GPR.r11 ∈ allowedChanges S.env g gf)
    (h_mem : core'.memory = m.core.memory.write64 (a.sp - 8)
      (callFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
        (offsetOf l fr.label fr.pos codes)).continuation.encode)
    (hh₁ : ∀ x, holes₁ x → holes x ∨ ((a.sp - 8).toNat ≤ x.toNat ∧ x.toNat < a.sp.toNat))
    (hlow : W.limit.toNat ≤ (a.sp - 8 - UInt64.ofNat gl.size).toNat)
    (hroom : gf.facts.calls = true → W.limit.toNat + slack ≤ (a.sp - 8 - UInt64.ofNat gl.size).toNat) :
    ∃ holes' m', SafeSteps Runtime.rejecting S.cs (prologue gl).length holes₁
        (inFrame core' (UInt32.ofNat ((ctxOf S.placed gpl).labelBase + 0)) 0
          (callFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
            (offsetOf l fr.label fr.pos codes) :: m.returns)) holes' m' ∧
      Match S W { s with regs := regs', stack := (callee :: Xl.suspend fr s.regs (S.env.clobbers g) rets.length ::
          below.map (·.1)) } m' holes' callee (calleeAct S g gf gl a.sp m.core)
        (callFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label)) (offsetOf l fr.label fr.pos codes))
        ((Xl.suspend fr s.regs (S.env.clobbers g) rets.length, { a with regs := m.core.readReg }, ret) :: below) := by
  have hg := hm.global
  have hf := htop.fn
  have hs := hf.checks.1
  have gs := hfg.checks.1
  have hact := htop.act
  have span := hact.span hg.top
  have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (by simpa using hpos.block)
  have himem : Inst.call g args rets ∈ b.body.toList := List.mem_of_getElem? (by simpa using hx)
  have hcalls : f.facts.calls = true := facts_calls hbmem himem
  have hroomC := htop.room hcalls
  have hgbd := gs.bounded
  have hlo := hg.low
  have hhigh := span.high
  have htopE := hg.top
  have hR8 : (a.sp - 8).toNat = a.sp.toNat - 8 := sub8_toNat (by simp only [maxFrame, slack] at hlo; omega)
  have hRc : (a.sp - 8 - UInt64.ofNat gl.size).toNat = a.sp.toNat - 8 - gl.size := by
    rw [sub_ofNat_toNat (by rw [hR8]; simp only [maxFrame, slack] at hlo hgbd; omega), hR8]
  -- The prologue's code
  have hfound := hpos0.found
  rw [hcl] at hfound
  have hlist : ({ instructions := (preOf gl 0 ++ codes0.flatten ++ post0).toArray, terminator := t0 } : X86.Block).instructions.toList =
      [] ++ prologue gl ++ (codes0.flatten ++ post0) := by simp [preOf]
  obtain ⟨hk, hsz⟩ := block_fits (cs := S.cs) hfound
  have hfound' : S.cs.program.blocks[(UInt32.ofNat ((ctxOf S.placed gpl).labelBase + 0)).toNat]? =
      some { instructions := (preOf gl 0 ++ codes0.flatten ++ post0).toArray, terminator := t0 } := by
    rw [UInt32.toNat_ofNat_of_lt' hk]; exact hfound
  have hseg := Straight.Segment.of_block hfound' hlist
  simp only [List.length_nil] at hseg
  have hfits : (prologue gl).length < UInt32.size := by
    simp only [List.size_toArray, List.length_append, preOf, ↓reduceIte] at hsz
    simp only [UInt32.size]; omega
  -- Writable stack below the return slot, and the live return slots above it
  have hw : ∀ x, (a.sp - 8 - UInt64.ofNat gl.size).toNat ≤ x.toNat → x.toNat < (a.sp - 8).toNat →
      core'.memory.writable x = true := fun x h₁ h₂ => by
    rw [h_mem]
    exact (hg.stack x ⟨by omega, by omega⟩).2.2.2
  have hdis : ∀ frame ∈ callFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
        (offsetOf l fr.label fr.pos codes) :: m.returns, ∀ i < 8,
      (a.sp - 8).toNat ≤ (frame.returnSlot + UInt64.ofNat i).toNat := by
    intro frame hfr i hi
    rcases List.mem_cons.1 hfr with rfl | hfr
    · simp only [callFrame, htop.rsp]
      rw [addr_toNat (by rw [hR8]; omega), hR8]; omega
    · obtain ⟨-, h⟩ := hm.slot htop hfr hi
      rw [hR8]; omega
  obtain ⟨mem', holes', hst, hr', hw', hb', hv', hh', hd'⟩ :=
    prologue_steps (returns := callFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
        (offsetOf l fr.label fr.pos codes) :: m.returns) (holes := holes₁) gs hseg hfits h_rsp
      (by rw [hR8]; simp only [maxFrame, slack] at hlo hgbd; omega) hw hdis
  refine ⟨holes', _, hst, ?_⟩
  have hoff : offsetOf gl 0 0 codes0 = (prologue gl).length := by simp [offsetOf, preOf]
  have hpos0' : XlPos S callee gf gl gpl b0 codes0 post0 t0 := hpos0
  have := call_match hm htop hpos hx hconvA hcode hread henter hfg hpos0'
    (core_f := { core'.setReg .rsp (a.sp - 8 - UInt64.ofNat gl.size) with memory := mem' }) (holes_f := holes')
    (by simp [Core.readReg, Core.setReg, Registers.set])
    (fun r h1 h2 => by
      show (core'.setReg .rsp _).readReg r = _
      rw [Validate.readReg_setReg, if_neg h1, h_regs r h1 h2])
    (fun h => h_r11 fun e => h (by
      show (core'.setReg .rsp (a.sp - 8 - UInt64.ofNat gl.size)).readReg .r11 = m.core.readReg .r11
      rw [Validate.readReg_setReg, if_neg (by decide)]; exact e))
    (by show mem'.readable = _; rw [hr', h_mem]; rfl) (by show mem'.writable = _; rw [hw', h_mem]; rfl)
    (fun x hx => by
      show mem'.bytes x = _
      rw [hb' x (fun ⟨h1, h2⟩ => hx ⟨h1, by rw [hR8] at h2; omega⟩), h_mem]
      exact write64_bytes_off (by rw [hR8]; omega) (fun ⟨h1, h2⟩ => hx ⟨by rw [hRc]; rw [hR8] at h1; simp only [maxFrame, slack] at hlo hgbd; omega,
        by rw [hR8] at h2; simp only [maxFrame, slack] at hlo; omega⟩))
    (by
      show mem'.read64 (a.sp - 8) = _
      rw [read64_congr (m := core'.memory) (m' := mem') fun i hi => hb' _ fun ⟨_, h2⟩ => by
        rw [addr_toNat (by rw [hR8]; omega)] at h2; omega, h_mem]
      exact Memory.read64_write64 _ _ _)
    (fun r o hro => by
      show mem'.read64 _ = _
      rw [hv' r o hro, h_regs r (saved_ne_rsp gs (saveOff_mem hro)) (by
        intro e; subst e
        have := (gs.savesExact _).1 (saveOff_mem hro)
        simp [saves, calleeSaved] at this)])
    (fun x hx => by rcases hh₁ x (hh' x hx) with h | h; exact .inl h; exact .inr h)
    (fun r o hro => hd' r o hro) hlow hroom
  rwa [hoff] at this

end IxCC.Xv.Stacking.Proof
