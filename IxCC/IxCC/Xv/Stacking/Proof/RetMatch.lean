import IxCC.Xv.Stacking.Proof.RetFacts

/-!
# A return to a caller keeps the invariant

`step_ret`: when the running activation returns to its suspended caller,
the epilogue and `ret` (`ret_steps`) leave the machine at the caller's
continuation, where the invariant holds for the caller: its registers are
Xl's `returnRegs` (the results, the caller's own values outside the
callee's clobbers), and its frame, saves and links are as it left them.
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

/-- A stacked call's results are in the convention's registers. -/
theorem inst_call_conv {c : FnCtx} {g : Lir.FunId} {args rets : List Loc} {code : List Instr}
    (h : c.inst (.call g args rets) = .ok code) : Xl.conventionResults rets = true := by
  by_cases hc : (Xl.conventionArgs args && Xl.conventionResults rets) = true
  · simp only [Bool.and_eq_true] at hc; exact hc.2
  · simp [FnCtx.inst, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-- A caller as Xl resumes it after a return. -/
def resumed (fr : Xl.Frame) : Xl.Frame := { fr with saved := Xl.Regs.empty, clobber := [], results := 0 }

theorem step_ret {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {fr₁ : Xl.Frame} {a₁ : Act} {ret₁ : ReturnFrame} {rest : List (Xl.Frame × Act × ReturnFrame)}
    (hm : Match S W s m holes fr a ret ((fr₁, a₁, ret₁) :: rest))
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) (hpc : m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes))
    (hend : fr.pos = b.body.size) {vs : List Loc} (hterm : b.term = .ret vs) (hcr : Xl.conventionResults vs = true)
    {vals : List Word} (hread : Xl.readAll s.regs fr vs = some vals) (hres : fr₁.results = vals.length) :
    ∃ n m', SafeSteps Runtime.rejecting S.cs n holes m holes m' ∧
      Match S W { s with regs := Xl.returnRegs fr₁.saved fr₁.clobber vals, stack := resumed fr₁ :: rest.map (·.1) }
        m' holes (resumed fr₁) a₁ ret₁ rest := by
  obtain ⟨core₁, hst, hm₁, hslot, hkeep, hk⟩ := ret_steps hm htop hpos hpc hend hterm
  have hg := hm.global
  have hf := htop.fn
  have hs := hf.checks.1
  have hact := htop.act
  have span := hact.span hg.top
  obtain ⟨⟨f₁, l₁, pl₁, hf₁⟩, hlink, hrest⟩ := hm.chain
  obtain ⟨⟨⟨b₁, codes₁, post₁, t₁, hpos₁, hcont⟩, hsp, hentry, ⟨b₁', g, args, rets, gf, hb₁', hcall, hgf, hallow⟩,
    -⟩, hact₁, hsusp⟩ := hlink f l pl hf f₁ l₁ pl₁ hf₁
  obtain ⟨⟨b₁'', g', args', rets', hb₁'', hpos0, hcall', hclob, hres'⟩, -, hsize₁, hregs₁, h15₁, -, hkept₁,
    hcells₁, hin₁, hroom₁⟩ := hsusp
  have e₁ : b₁'' = b₁' := Option.some.inj (hb₁''.symm.trans hb₁')
  subst e₁
  rw [hcall'] at hcall
  simp only [Option.some.injEq, Inst.call.injEq] at hcall
  obtain ⟨e₁, e₂, e₃⟩ := hcall
  subst g' args' rets'
  have hs₁ := hf₁.checks.1
  have hbmem₁ : b₁'' ∈ f₁.blocks.toList := List.mem_of_getElem? (by simpa using hb₁'')
  have himem₁ : Inst.call g args rets ∈ b₁''.body.toList := List.mem_of_getElem? (by simpa using hcall')
  have harity := call_arity hf₁ hbmem₁ himem₁ hgf
  obtain ⟨hlenV, hgetV⟩ := readAll_get hread
  -- The new core
  have hspNew : (core₁.setReg .rsp (ret.returnSlot + 8)).readReg .rsp = a₁.sp := by
    rw [Validate.readReg_setReg, if_pos rfl, hact.slot]
    apply word_eq
    have h₁ := span.high
    have h₂ := span.top
    have e₁ : (a.sp + UInt64.ofNat l.size).toNat = a.sp.toNat + l.size := addr_toNat (by omega)
    have e₂ : (a.sp + UInt64.ofNat l.size + UInt64.ofNat 8).toNat = a.sp.toNat + l.size + 8 := by
      rw [addr_toNat (by omega), e₁]
    rw [show (8 : Word) = UInt64.ofNat 8 from rfl, e₂, hsp]
  have hregNew : ∀ r, r ≠ .rsp → (core₁.setReg .rsp (ret.returnSlot + 8)).readReg r = core₁.readReg r :=
    fun r hr => by rw [Validate.readReg_setReg, if_neg hr]
  -- Registers outside the callee's allowed changes are the caller's at the call.
  have hcallerReg : ∀ r, r ∉ a.allow → r ≠ .rsp → (core₁.setReg .rsp (ret.returnSlot + 8)).readReg r = a₁.regs r :=
    fun r hr hsp' => by rw [hregNew r hsp', hkeep r hr hsp', hentry r hsp']
  have hallowSub : ∀ r, r ∉ a₁.allow → r ∉ a.allow := by
    intro r hr ha
    rw [hallow] at ha
    simp only [allowedChanges, List.mem_append] at ha
    rcases ha with ha | ha
    · exact hr (hact₁.allowed r (clobbers_allowed hf₁ hbmem₁ himem₁ ha))
    · have hrR : r ∈ Lir.Conv.resultRegs := List.mem_of_mem_take ha
      have hlt : ∃ i, i < rets.length ∧ Lir.Conv.resultRegs[i]? = some r := by
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ha
        rw [List.getElem?_take] at hi
        split at hi
        · exact ⟨i, by rw [← harity]; assumption, hi⟩
        · simp at hi
      obtain ⟨i, hi, hri⟩ := hlt
      have e₂ : b₁ = b₁'' := Option.some.inj (hpos₁.block.symm.trans hb₁'')
      subst e₂
      obtain ⟨code, -, hinst⟩ := hpos₁.insts (fr₁.pos - 1) _ hcall'
      obtain ⟨r', hr', hrets⟩ := conventionResults_get (inst_call_conv hinst) hi
      rw [hri] at hr'
      cases hr'
      rcases results_allowed hf₁ hbmem₁ himem₁ (List.mem_of_getElem? hrets) with h | h
      · exact resultReg_not_saved hs₁ hrR h
      · exact hr (hact₁.allowed r h)
  -- The caller's registers
  have hcs : ∀ r, r ∈ SysV.calleeSaved.toList → r ∉ a.allow := fun r hr ha => by
    obtain ⟨g₀, gf₀, hgf₀, hallow₀⟩ := hm.chain.allow hf
    obtain ⟨_, _, hfg₀⟩ := fnAt_of S hgf₀
    rw [hallow₀] at ha
    exact calleeSaved_not_callerSaved hr (allowed_callerSaved hfg₀ ha)
  have h15 : (core₁.setReg .rsp (ret.returnSlot + 8)).readReg .r15 = W.ctx := by
    rw [hcallerReg _ (hcs _ (by decide)) (by decide), h15₁]
  obtain ⟨hsizeR, hgetR⟩ := returnRegs_spec hsize₁ fr₁.clobber vals
  have hglob : Global W s.mem
      { core := core₁.setReg .rsp (ret.returnSlot + 8), pc := ret.continuation,
        returns := ((fr₁, a₁, ret₁) :: rest).map (·.2.2), status := .running } holes := by
    refine Global.mono hg (by show (core₁.setReg _ _).memory.readable = _; rw [← hm₁]; rfl)
      (by show (core₁.setReg _ _).memory.writable = _; rw [← hm₁]; rfl)
      (fun x _ => by show (core₁.setReg _ _).memory.bytes x = _; rw [← hm₁]; rfl) (fun x hx => .inl hx) h15 ?_
    rcases hg.entry.outer with h | ⟨inner, f₀, h, h₁, h₂⟩
    · rw [hm.returns] at h; cases h
    · rw [hm.returns] at h
      cases inner with
      | nil => simp at h
      | cons x inner' =>
        simp only [List.cons_append, List.cons.injEq] at h
        refine .inr ⟨inner', f₀, by simp only [List.map_cons]; exact h.2, h₁,
          fun g hg' => h₂ g (List.mem_cons_of_mem _ hg')⟩
  have span₁ := hact₁.span hg.top
  have hmem : (core₁.setReg .rsp (ret.returnSlot + 8)).memory = m.core.memory := hm₁
  have hchain := Chain.retop (fr := fr₁) (fr' := resumed fr₁) rfl hrest
  rw [← hmem] at hchain hact₁
  refine ⟨_, _, hst, rfl, rfl, by simp, hm.ctx, ⟨f₁, l₁, pl₁, ⟨hf₁, ⟨b₁, codes₁, post₁, t₁, ⟨hpos₁.block, hpos₁.found, hpos₁.len, hpos₁.insts, hpos₁.term, hpos₁.pos⟩, hcont⟩,
    ⟨hsizeR, ?_, h15, ?_, ?_, ?_⟩, hspNew, ?_, ?_, ?_, fun _ => hroom₁, hin₁⟩⟩, hchain, hglob⟩
  · -- Registers
    intro r hr v hv
    rcases hgetR r v hv with ⟨i, hri, hvi⟩ | ⟨hnr, hncl, hsv⟩
    · -- A result
      have hiv : i < vs.length := by rw [← hlenV]; exact (List.getElem?_eq_some_iff.1 hvi).1
      obtain ⟨r', hr', hvsi⟩ := conventionResults_get hcr hiv
      rw [hri] at hr'
      cases hr'
      obtain ⟨v', hv', hrd⟩ := hgetV i _ hvsi
      have e : v' = v := Option.some.inj (hv'.symm.trans hvi)
      subst e
      rw [Xl.read_reg hr] at hrd
      have hrR : r ∈ Lir.Conv.resultRegs := List.mem_of_getElem? hri
      have hrsp : r ≠ .rsp := by intro e; subst e; simp [Lir.Conv.resultRegs] at hrR
      show (core₁.setReg .rsp (ret.returnSlot + 8)).readReg r = v'
      rw [hregNew r hrsp, hk r hrsp (resultReg_not_saved hs hrR)]
      exact htop.agree.regsRel r hr v' hrd
    · -- The caller's own value
      have hrsp : r ≠ .rsp := by intro e; subst e; simp [Xl.reserved] at hr
      have hna : r ∉ a.allow := by
        rw [hallow]
        simp only [allowedChanges, List.mem_append, not_or]
        refine ⟨fun hc => ?_, fun ht => hnr ?_⟩
        · rw [← hclob] at hc
          simp at hncl; exact hncl hc
        · rw [harity, ← hres', hres] at ht
          exact mem_take_zip_fst ht
      show (core₁.setReg .rsp (ret.returnSlot + 8)).readReg r = v
      rw [hcallerReg r hna hrsp]
      exact hregs₁ r hr v hsv
  · -- Xl's memory inside the machine's
    show Inside s.mem (core₁.setReg .rsp (ret.returnSlot + 8)).memory
    rw [show (core₁.setReg .rsp (ret.returnSlot + 8)).memory = core₁.memory from rfl, hm₁]
    exact htop.agree.inside
  · -- Cells
    intro x hx v hv
    have hv' : Xl.read Xl.Regs.empty fr₁ x = some v := by
      cases x with
      | reg r => simp [Loc.isCell] at hx
      | _ => simpa [Xl.read, resumed] using hv
    obtain ⟨mm, hmm, hmv, -⟩ := hcells₁ x hx v hv'
    refine ⟨mm, hmm, ?_⟩
    rw [cell_rsp hmm (c₂ := atSp a₁.sp) (by rw [hspNew]; rfl)]
    show core₁.memory.read64 _ = v
    rw [hm₁]; exact hmv
  · exact frameCells_of hglob hs₁ span₁ hf₁.play hf₁.pfacts hspNew
  · -- Registers the caller keeps
    intro r hr hsp'
    rcases hkept₁ r hr hsp' with h | h
    · exact .inl h
    · exact .inr (by rw [hcallerReg r (hallowSub r hr) hsp', h])
  · exact ⟨hact₁.saves, hact₁.savesData, hact₁.allowed, hact₁.slot, hact₁.retAddr, hact₁.snapshot, hact₁.align,
      hact₁.low, hact₁.high, hact₁.inBound⟩
  · intro x hx v hv mm hmm
    have hv' : Xl.read Xl.Regs.empty fr₁ x = some v := by
      cases x with
      | reg r => simp [Loc.isCell] at hx
      | _ => simpa [Xl.read, resumed] using hv
    obtain ⟨mm', hmm', -, hdata⟩ := hcells₁ x hx v hv'
    rw [hmm] at hmm'
    cases hmm'
    rw [cell_rsp hmm (c₂ := atSp a₁.sp) (by rw [hspNew]; rfl)]
    exact hdata

end IxCC.Xv.Stacking.Proof
