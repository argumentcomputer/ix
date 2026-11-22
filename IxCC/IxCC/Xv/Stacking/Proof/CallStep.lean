import IxCC.Xv.Stacking.Proof.CallRun

/-!
# An Xl call as machine steps

`step_call`: the stacked call, the callee's stack check (if it has one) and
its prologue match an Xl call, after which the invariant holds for the
callee; or the stack check fails and the program exits with status 2.
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

/-- A checked function may change `r11`, which its stack check writes. -/
theorem r11_allowed {S : Stk} {g : Lir.FunId} {gf : Func Loc} {gl : FrameLayout} {gpl : Placed}
    (hfg : FnAt S g gf gl gpl) (hc : FrameLayout.checked gf.facts gl = true) :
    GPR.r11 ∈ allowedChanges S.env g gf := by
  have hx := hfg.checks.2.1
  simp only [extraChanges, List.append_eq_nil_iff, List.filter_eq_nil_iff] at hx
  have := hx.1 .r11 (List.mem_append_left _ (by simp [mayChange, hc]))
  simpa using this

/-- An unchecked function's frame and return address fit in the slack, and
it makes no call. -/
theorem unchecked_slack {gf : Func Loc} {gl : FrameLayout} (gs : gl.Sound gf.facts)
    (hc : ¬FrameLayout.checked gf.facts gl = true) : gl.size + 8 ≤ slack ∧ gf.facts.calls = false := by
  simp only [FrameLayout.checked, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq,
    not_and, not_or, Nat.not_lt] at hc
  by_cases hz : gl.size = 0
  · exact ⟨by simp [hz, slack], (gs.frameless hz).2.2.2.2⟩
  · obtain ⟨hcalls, hs⟩ := hc hz
    exact ⟨hs, by simpa using hcalls⟩

/-- A function's first label has a block. -/
theorem first_block {S : Stk} {k : Lir.FunId} {f : Func Loc} {l : FrameLayout} {pl : Placed} (hf : FnAt S k f l pl) :
    ∃ b0, f.blocks[0]? = some b0 := by
  obtain ⟨pl', blks, -, -, -, -, -, hemit, -⟩ := func_at S.ok hf.func hf.layout
  obtain ⟨hne, -⟩ := emitFunc_ok hemit
  exact ⟨_, Array.getElem?_eq_getElem (by omega)⟩

/-- An Xl call: the stacked call, the callee's stack check and its prologue,
after which the invariant holds for the callee; or the check fails and the
program exits with status 2. -/
theorem step_call {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) (hpc : m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes))
    {g : Lir.FunId} {args rets : List Loc}
    (hx : b.body[fr.pos]? = some (.call g args rets)) (hconvA : Xl.conventionArgs args = true)
    {vals : List Word} (hread : Xl.readAll s.regs fr args = some vals) {callee : Xl.Frame} {regs' : Xl.Regs}
    (henter : Xl.enter S.p g vals = some (callee, regs')) :
    (∃ n holes' after, SafeSteps Runtime.rejecting S.cs n holes m holes' after ∧
      Exit W.core₀ W.retAddr 2 0 after ∧ ReadableData holes' (after.core.readReg .rsp) 8) ∨
    (∃ n holes' m' a' ret', 1 ≤ n ∧ SafeSteps Runtime.rejecting S.cs n holes m holes' m' ∧
      Match S W { s with regs := regs', stack := (callee :: Xl.suspend fr s.regs (S.env.clobbers g) rets.length ::
          below.map (·.1)) } m' holes' callee a' ret'
        ((Xl.suspend fr s.regs (S.env.clobbers g) rets.length, { a with regs := m.core.readReg }, ret) :: below)) := by
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
  -- The call's code
  obtain ⟨code, hcode, hinst⟩ := hpos.insts fr.pos _ hx
  obtain ⟨entry, arity, hget, -, rfl⟩ := inst_call hinst
  have hentry : entry = gpl.start := by
    have h1 := entry_of S g
    have h2 : (ctxOf S.placed pl).funcs = entriesOf S.placed := rfl
    rw [← h2, hget, hfg.placed] at h1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    exact h1.1
  subst hentry
  -- The caller
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
  have htopE := hg.top
  have hRsp : m.core.readReg .rsp = a.sp := htop.rsp
  have hR8 : (a.sp - 8).toNat = a.sp.toNat - 8 := sub8_toNat (by simp only [maxFrame, slack] at hlo; omega)
  have hRc : (a.sp - 8 - UInt64.ofNat gl.size).toNat = a.sp.toNat - 8 - gl.size := by
    rw [sub_ofNat_toNat (by rw [hR8]; simp only [maxFrame, slack] at hlo hgbd; omega), hR8]
  have hRmod : a.sp.toNat % 16 = 0 := by omega
  obtain ⟨hseg, hfits⟩ := hpos.segment hcode
  have hexit : ExitGroupAt S.cs := fun j hj => exit_at S.ok hj
  -- The callee's first label
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
  -- The call
  have hInStack : ∀ x, a.sp.toNat - 8 ≤ x.toNat → x.toNat < a.sp.toNat → W.InStack x :=
    fun x h₁ h₂ => ⟨by simp only [maxFrame, slack] at hlo hgbd hroomC ⊢; omega, by omega⟩
  have hbyte8 : ∀ i < 8, (a.sp - 8 + UInt64.ofNat i).toNat = a.sp.toNat - 8 + i := fun i hi => by
    rw [addr_toNat (by rw [hR8]; omega), hR8]
  have haligned : SysV.callSiteAligned (m.core.readReg .rsp) = true := by
    simp only [SysV.callSiteAligned, hRsp, beq_iff_eq]
    apply word_eq
    rw [UInt64.toNat_mod]
    simpa using hRmod
  have hwritable : Memory.rangeAllowed m.core.memory.writable (m.core.readReg .rsp - 8) 8 = true := by
    rw [hRsp]
    refine (rangeAllowed_iff _ _ _).2 fun i hi => ?_
    exact (hg.stack _ (hInStack _ (by rw [hbyte8 i hi]; omega) (by rw [hbyte8 i hi]; omega))).2.2.2
  have hdisjoint : FramesDisjoint m.returns (m.core.readReg .rsp - 8) 8 := by
    rw [hRsp]
    refine disjoint_below (B := a.sp.toNat) (fun frm hfrm i hi => ?_) (fun j hj => by rw [hbyte8 j hj]; omega)
    obtain ⟨-, h⟩ := hm.slot htop hfrm hi
    rcases h with h | h <;> omega
  have hcall := Straight.Segment.safe_call hseg (by simpa [UInt32.size] using hfits) hvalid Runtime.rejecting (holes := holes)
    haligned hwritable hdisjoint
  rw [← machine_at hm.running hpc] at hcall
  -- After the call
  have h1rsp : (callCore m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
      (offsetOf l fr.label fr.pos codes)).readReg .rsp = a.sp - 8 := by
    show (m.core.setReg .rsp (m.core.readReg .rsp - 8)).readReg .rsp = _
    rw [Validate.readReg_setReg, if_pos rfl, hRsp]
  have h1regs : ∀ r, r ≠ .rsp → (callCore m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
      (offsetOf l fr.label fr.pos codes)).readReg r = m.core.readReg r := fun r hr => by
    show (m.core.setReg .rsp (m.core.readReg .rsp - 8)).readReg r = _
    rw [Validate.readReg_setReg, if_neg hr]
  have h1mem : (callCore m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
      (offsetOf l fr.label fr.pos codes)).memory = m.core.memory.write64 (a.sp - 8)
        (callFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
          (offsetOf l fr.label fr.pos codes)).continuation.encode := by
    show m.core.memory.write64 (m.core.readReg .rsp - 8) _ = _
    rw [hRsp]
  have hh₁ : ∀ x, addRange holes (m.core.readReg .rsp - 8) 8 x →
      holes x ∨ ((a.sp - 8).toNat ≤ x.toNat ∧ x.toNat < a.sp.toNat) := by
    intro x hx
    rcases hx with h | ⟨i, hi, rfl⟩
    · exact .inl h
    · right; rw [hRsp, hbyte8 i hi, hR8]; omega
  by_cases hc : FrameLayout.checked gf.facts gl = true
  · -- The stack check
    obtain ⟨pl', hpl', -, -, -, hblk⟩ := check_at S hfg.func hfg.layout hc
    have e : pl' = gpl := Option.some.inj (hpl'.symm.trans hfg.placed)
    subst e
    obtain ⟨hk, -⟩ := block_fits (cs := S.cs) hblk
    have hbc : BlockCode S.cs (UInt32.ofNat pl'.start) [Instr.lea .r11 (rspBelow (gl.size + slack))]
        (.branch cmpRM [.reg .r11, .mem stackLimitCell] .unsignedLt 1 (UInt32.ofNat (pl'.start + 1))) :=
      ⟨by rw [UInt32.toNat_ofNat_of_lt' (by simpa [UInt32.size] using hk)]; exact hblk, by simp [UInt32.size]⟩
    have h2 : S.cs.program.hasBlock 1 = true := (hexit.fail (k := 2) (by decide) (by decide)).hasBlock
    have hsh : (ctxOf S.placed pl').labelBase + 0 = pl'.start + 1 := by
      simp [ctxOf, shiftOf, hfg.play, hfg.pfacts, hc]
    have hn : S.cs.program.hasBlock (UInt32.ofNat (pl'.start + 1)) = true := by
      have := hfound0; rw [hsh] at this; exact hasBlock_of this
    have hr15 : (callCore m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
        (offsetOf l fr.label fr.pos codes)).readReg .r15 = W.ctx := by
      rw [h1regs _ (by decide)]; exact htop.agree.ctxReg
    have hctxB : ∀ j < 8, W.ctx - 56 + UInt64.ofNat j = W.ctx - 64 + UInt64.ofNat (8 + j) := by
      intro j _; rw [ctx_56, UInt64.add_assoc, ← UInt64.ofNat_add]
    have hnotQ : ∀ j < 8, ¬((a.sp - 8).toNat ≤ (W.ctx - 56 + UInt64.ofNat j).toNat ∧
        (W.ctx - 56 + UInt64.ofNat j).toNat < (a.sp - 8).toNat + 8) := by
      intro j hj ⟨h₁, h₂⟩
      rw [hctxB j hj] at h₁ h₂
      exact hg.apart (8 + j) (by omega) (hInStack _ (by rw [hR8] at h₁; omega) (by rw [hR8] at h₂; omega))
    have hlimOk : (callCore m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
        (offsetOf l fr.label fr.pos codes)).memory.read64?
          ((callCore m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
            (offsetOf l fr.label fr.pos codes)).readReg .r15 - 56) = .ok W.limit := by
      rw [hr15, h1mem]
      simp only [Memory.read64?, Memory.read?]
      rw [if_pos ((rangeAllowed_iff _ _ _).2 fun j hj => by
        have hj8 : j < 8 := hj
        rw [Memory.write64_readable, hctxB j hj8]
        exact (hg.ctxCells (8 + j) (by omega)).2.2.1)]
      congr 1
      rw [← hg.limit]
      exact read64_congr fun j hj => write64_bytes_off (by rw [hR8]; omega) (hnotQ j hj)
    have hdata : ReadableData (addRange holes (m.core.readReg .rsp - 8) 8)
        ((callCore m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
          (offsetOf l fr.label fr.pos codes)).readReg .r15 - 56) 8 := by
      rw [hr15]
      intro j hj hh
      rcases hh with h | ⟨i, hi, e⟩
      · exact hg.limitData j hj h
      · apply hnotQ j hj
        rw [e, hRsp, hbyte8 i hi, hR8]; omega
    have hchk := check_steps (returns := callFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
      (offsetOf l fr.label fr.pos codes) :: m.returns) hbc (by simp only [maxFrame, slack] at hgbd ⊢; omega) h2 hn
      hlimOk hdata
    rw [h1rsp] at hchk
    have hXn : (a.sp - 8 - UInt64.ofNat (gl.size + slack)).toNat = a.sp.toNat - 8 - (gl.size + slack) := by
      rw [sub_ofNat_toNat (by rw [hR8]; simp only [maxFrame, slack] at hlo hgbd ⊢; omega), hR8]
    by_cases hX : (a.sp - 8 - UInt64.ofNat (gl.size + slack)).toNat < W.limit.toNat
    · -- The check fails: the exit group, status 2
      left
      rw [if_pos hX] at hchk
      have hG₂ : Global W s.mem (inFrame ((callCore m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
          (offsetOf l fr.label fr.pos codes)).setReg .r11 (a.sp - 8 - UInt64.ofNat (gl.size + slack))) 1 0
          (callFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
            (offsetOf l fr.label fr.pos codes) :: m.returns)) (addRange holes (m.core.readReg .rsp - 8) 8) := by
        refine Global.mono hg (by show (m.core.memory.write64 _ _).readable = _; simp)
          (by show (m.core.memory.write64 _ _).writable = _; simp) (fun x hx => ?_) (fun x hx => ?_) ?_ ?_
        · show (m.core.memory.write64 (m.core.readReg .rsp - 8) _).bytes x = _
          rw [hRsp]
          refine write64_bytes_off (by rw [hR8]; omega) fun ⟨h₁, h₂⟩ => ?_
          rcases hx with hx | hx
          · exact hx (hInStack x (by rw [hR8] at h₁; omega) (by rw [hR8] at h₂; omega))
          · rw [hR8] at h₂; omega
        · rcases hh₁ x hx with h | ⟨h₁, h₂⟩
          · exact .inl h
          · exact .inr ⟨hInStack x (by rw [hR8] at h₁; omega) h₂, by omega⟩
        · show ((callCore m.core _ _).setReg .r11 _).readReg .r15 = W.ctx
          rw [Validate.readReg_setReg, if_neg (by decide), hr15]
        · rcases hg.entry.outer with h | ⟨inner, f₁, h, h₁, h₂⟩
          · rw [hm.returns] at h; cases h
          · refine .inr ⟨callFrame m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
              (offsetOf l fr.label fr.pos codes) :: inner, f₁, by simp only [inFrame, h, List.cons_append], h₁,
              fun g hg' => ?_⟩
            rcases List.mem_cons.1 hg' with rfl | hg'
            · intro e
              have := congrArg UInt64.toNat e
              simp only [callFrame, hRsp] at this
              rw [show a.sp - 8 + 8 = a.sp by simp] at this
              omega
            · exact h₂ g hg'
      obtain ⟨n, after, -, hsafe, hexitE⟩ := Wrapper.fail_safe hexit Runtime.rejecting (k := 2) (by decide)
        (by decide) hG₂.entry rfl rfl
      refine ⟨1 + 2 + n, _, after, (hcall.append hchk).append hsafe, hexitE, ?_⟩
      rw [hexitE.rsp, hG₂.entry.rsp0]
      have := hG₂.entry.savesData 6 (by decide)
      simpa using this
    · -- The check passes: the prologue
      right
      rw [if_neg hX] at hchk
      obtain ⟨holes', m', hpro, hmatch⟩ := prologue_match hm htop hpos hx hconvA hcode hread henter hfg hpos0 hcl
        (core' := (callCore m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
          (offsetOf l fr.label fr.pos codes)).setReg .r11 (a.sp - 8 - UInt64.ofNat (gl.size + slack)))
        (holes₁ := addRange holes (m.core.readReg .rsp - 8) 8)
        (by rw [Validate.readReg_setReg, if_neg (by decide), h1rsp])
        (fun r h1 h2 => by rw [Validate.readReg_setReg, if_neg h2, h1regs r h1])
        (fun _ => r11_allowed hfg hc) (by show (callCore _ _ _).memory = _; exact h1mem) hh₁
        (by rw [hRc]; omega) (fun _ => by rw [hRc]; omega)
      rw [hsh] at hpro
      exact ⟨1 + 2 + (prologue gl).length, holes', m', _, _, by omega, (hcall.append hchk).append hpro, hmatch⟩
  · -- No stack check: the prologue
    right
    have hsh : (ctxOf S.placed gpl).labelBase + 0 = gpl.start := by
      simp [ctxOf, shiftOf, hfg.play, hfg.pfacts, hc]
    obtain ⟨hsl, hnc⟩ := unchecked_slack gs hc
    obtain ⟨holes', m', hpro, hmatch⟩ := prologue_match hm htop hpos hx hconvA hcode hread henter hfg hpos0 hcl
      (core' := callCore m.core (UInt32.ofNat ((ctxOf S.placed pl).labelBase + fr.label))
        (offsetOf l fr.label fr.pos codes))
      (holes₁ := addRange holes (m.core.readReg .rsp - 8) 8) h1rsp (fun r h1 _ => h1regs r h1)
      (fun h => absurd (h1regs .r11 (by decide)) h) h1mem hh₁
      (by rw [hRc]; simp only [slack] at hsl hroomC ⊢; omega) (fun h => by rw [hnc] at h; cases h)
    rw [hsh] at hpro
    exact ⟨1 + (prologue gl).length, holes', m', _, _, by omega, hcall.append hpro, hmatch⟩

end IxCC.Xv.Stacking.Proof
