import Compilatrix.Xv.Stacking.Proof.Return

/-!
# A return as machine steps

`ret_steps`: at a `ret`, the epilogue restores the saved registers and
frees the frame, and the machine's `ret` passes its checks (the stack
pointer at the return slot, the slot holding the continuation, the
callee-saved registers as at the call), because an activation may change
only caller-saved registers (`allowed_callerSaved`).
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86 Compilatrix.X86.Stream

/-- What a function may change is caller-saved. -/
theorem allowed_callerSaved {S : Stk} {g : Lir.FunId} {gf : Func Loc} {gl : FrameLayout} {gpl : Placed}
    (hfg : FnAt S g gf gl gpl) {r : GPR} (hr : r ∈ allowedChanges S.env g gf) : r ∈ SysV.callerSaved.toList := by
  have hx := hfg.checks.2.1
  simp only [extraChanges, List.append_eq_nil_iff, List.filter_eq_nil_iff] at hx
  simp only [allowedChanges, List.mem_append] at hr
  rcases hr with hr | hr
  · have := hx.2 r hr
    simpa using this
  · have := List.mem_of_mem_take hr
    simp only [Lir.Conv.resultRegs, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl <;> decide

/-- The running activation's allowed changes are some function's. -/
theorem Chain.allow {S : Stk} {W : Wrap} {mem : Memory} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hc : Chain S W mem holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (hf : FnAt S fr.fn f l pl) :
    ∃ g gf, S.p.funcs[g]? = some gf ∧ a.allow = allowedChanges S.env g gf := by
  cases below with
  | nil =>
    obtain ⟨-, -, -, ⟨mf, hmf, h⟩, -⟩ := hc f l pl hf
    exact ⟨_, mf, hmf, h⟩
  | cons x rest =>
    obtain ⟨fr₁, a₁, ret₁⟩ := x
    obtain ⟨⟨f₁, l₁, pl₁, hf₁⟩, hlink, -⟩ := hc
    obtain ⟨⟨-, -, -, ⟨-, g, -, -, gf, -, -, hgf, h⟩, -⟩, -, -⟩ := hlink f l pl hf f₁ l₁ pl₁ hf₁
    exact ⟨g, gf, hgf, h⟩

theorem calleeSaved_not_callerSaved {r : GPR} (h : r ∈ SysV.calleeSaved.toList) : r ∉ SysV.callerSaved.toList := by
  simp only [SysV.calleeSaved, SysV.callerSaved, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem calleeSavedMatch_of {core : Core} {e : GPR → Word} (h : ∀ r ∈ SysV.calleeSaved.toList, core.readReg r = e r) :
    core.calleeSavedMatch (SysV.calleeSaved.map e) = true := by
  simp only [Core.calleeSavedMatch, Core.calleeSavedSnapshot, beq_iff_eq]
  simp only [SysV.calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at h
  simp [SysV.calleeSaved, h]

/-- A `ret`: the epilogue and the return, as checked steps. -/
theorem ret_steps {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} {below : List (Xl.Frame × Act × ReturnFrame)} (hm : Match S W s m holes fr a ret below)
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) (hpc : m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes))
    (hend : fr.pos = b.body.size) {vs : List Loc} (hterm : b.term = .ret vs) :
    ∃ core₁ : Core, SafeSteps Runtime.rejecting S.cs ((epilogue l).length + 1) holes m holes
        { core := core₁.setReg .rsp (ret.returnSlot + 8), pc := ret.continuation, returns := below.map (·.2.2),
          status := .running } ∧
      core₁.memory = m.core.memory ∧ core₁.readReg .rsp = ret.returnSlot ∧
      (∀ r, r ∉ a.allow → r ≠ .rsp → core₁.readReg r = a.entry r) ∧
      (∀ r, r ≠ .rsp → r ∉ l.saved → core₁.readReg r = m.core.readReg r) := by
  have hg := hm.global
  have hf := htop.fn
  have hs := hf.checks.1
  have hact := htop.act
  have span := hact.span hg.top
  have hbd := hs.bounded
  -- The terminator's code
  have hterm' := hpos.term
  rw [hterm] at hterm'
  have hpt : epilogue l = post ∧ Terminator.ret = t := by
    by_cases hcr : Xl.conventionResults vs = true
    · simpa [FnCtx.term, hcr, pure, Except.pure, ctxOf, hf.play] using hterm'
    · simp [FnCtx.term, hcr, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hterm'
  obtain ⟨rfl, rfl⟩ := hpt
  obtain ⟨hcode, hseg⟩ := hpos.blockCode
  have hoffEnd : offsetOf l fr.label fr.pos codes = (preOf l fr.label ++ codes.flatten).length := by
    simp [offsetOf, hend, ← hpos.len, List.take_length]
  have hoffLen : offsetOf l fr.label codes.length codes = (preOf l fr.label ++ codes.flatten).length := by
    simp [offsetOf, List.take_length]
  rw [hoffEnd] at hpc
  rw [hoffLen] at hseg
  have hm₀ := machine_at hm.running hpc
  have hfits := hcode.fits
  -- The epilogue
  have hrd : ∀ r o, (r, o) ∈ l.saveOff → ∀ i < 8, m.core.memory.readable (a.sp + UInt64.ofNat o + UInt64.ofNat i) = true := by
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
  -- The callee-saved registers and the activation's entry
  obtain ⟨g, gf, hgf, hallow⟩ := hm.chain.allow hf
  obtain ⟨gl, gpl, hfg⟩ := fnAt_of S hgf
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
  have hslot : core₁.readReg .rsp = ret.returnSlot := by rw [hr₁, hact.slot]
  have hcs : ∀ r ∈ SysV.calleeSaved.toList, core₁.readReg r = a.entry r := by
    intro r hr
    refine hkeep r (fun ha => ?_) (rsp_not_calleeSaved (by simpa using hr))
    rw [hallow] at ha
    exact calleeSaved_not_callerSaved hr (allowed_callerSaved hfg ha)
  have hreadable : core₁.memory.read64? ret.returnSlot = .ok ret.continuation.encode := by
    rw [hm₁, ← hact.retAddr]
    have h := (rangeAllowed_iff m.core.memory.readable ret.returnSlot 8).2 fun i hi => by
      rw [hact.slot]
      have e : a.sp + UInt64.ofNat l.size + UInt64.ofNat i = a.sp + UInt64.ofNat (l.size + i) := by
        rw [UInt64.add_assoc, ← UInt64.ofNat_add]
      rw [e]
      exact (hg.stack _ (span.byte (o := l.size + i) (by omega)).2).2.2.1
    simp [Memory.read64?, Memory.read?, w64_bytes, h, Memory.read64]
  have hret := hcode.safe_ret Runtime.rejecting core₁ ret (below.map (·.2.2)) holes hslot hreadable (by
    rw [hact.snapshot]; exact calleeSavedMatch_of hcs)
  rw [← hm.returns] at hret
  refine ⟨core₁, ?_, hm₁, hslot, hkeep, fun r hr hns => hk₁ r hr hns⟩
  rw [List.length_append] at hret
  have := hepi.append hret
  simpa [List.length_append] using this

end Compilatrix.Xv.Stacking.Proof
