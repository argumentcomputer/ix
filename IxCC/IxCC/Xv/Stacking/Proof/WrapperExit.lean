import IxCC.Xv.Stacking.Proof.TailStep

/-!
# The export's success exit

When the outermost activation returns, the machine resumes in the export
wrapper after its call (`WrapCont`): `mov rdx, rax; xor eax, eax`, the
wrapper's epilogue and `ret` (`success_exit`) leave status 0 and the result
in `rax:rdx`, with the caller's callee-saved registers, stack pointer and
return address as at entry. `step_done`: an Xl return from the outermost
activation, which ends the run, is matched by the epilogue, the return into
the wrapper and its exit, with `Final`: the result is the single value Xl
returns, Xl's memory lies inside the machine's, and the holes are where Xl
cannot look. -/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

/-- The wrapper's code after its call: the status and value, the epilogue
(then `ret`). -/
def wrapperTail : List Instr :=
  [Instr.mov .w64 .rdx (.reg .rax), Instr.alu .xor .w32 .rax (.reg .rax)] ++ wrapperEpilogue

/-- The wrapper's call returns to its tail (`wrapperTail`, then `ret`). -/
def WrapCont (S : Stk) (W : Wrap) : Prop :=
  ∃ (blk : BlockId) (pre : List Instr), BlockCode S.cs blk (pre ++ wrapperTail) .ret ∧
    W.frame.continuation = ⟨blk, UInt32.ofNat pre.length⟩

/-- How a successful run ends: the export's value is the single value Xl
returns, Xl's final memory lies inside the machine's, and every hole is
memory Xl cannot read or write. -/
def Final (v : List Word × Memory) (val : Word) (mm : Memory) (holes : Holes) : Prop :=
  v.1 = [val] ∧ Inside v.2 mm ∧ ∀ x, holes x → v.2.readable x = false ∧ v.2.writable x = false

/-- The wrapper's tail from `rsp = entrySp`: ten checked steps to an `Exit`
with status 0 and the value in `rax`. -/
theorem success_exit {cs : Checked} {blk : BlockId} {pre : List Instr}
    (code : BlockCode cs blk (pre ++ wrapperTail) .ret) {holes : Holes} {core : Core} {ctx entrySp : Word}
    {core₀ : Core} {retAddr : Word} {returns : List ReturnFrame}
    (ef : EntryFrame ctx entrySp core₀ retAddr (inFrame core blk pre.length returns) holes)
    (hret : returns = []) (hrsp : core.readReg .rsp = entrySp) :
    ∃ after, SafeSteps Runtime.rejecting cs 10 holes (inFrame core blk pre.length returns) holes after ∧
      Exit core₀ retAddr 0 (core.readReg .rax) after ∧ after.core.memory = core.memory ∧
      ReadableData holes (after.core.readReg .rsp) 8 := by
  subst hret
  have hfound : cs.program.blocks[blk.toNat]? = some { instructions := (pre ++ wrapperTail).toArray, terminator := .ret } :=
    code.found
  have seg : Straight.Segment cs blk pre.length wrapperTail :=
    Straight.Segment.of_block hfound (post := []) (by simp)
  have hfits := code.fits
  simp only [wrapperTail, List.length_append, wrapperEpilogue, List.length_cons, List.length_map, wrapperSaves,
    List.length_reverse, List.length_nil] at hfits
  -- `mov rdx, rax`
  let c₁ := core.setReg .rdx (core.readReg .rax)
  have s1 : SafeSteps Runtime.rejecting cs 1 holes (inFrame core blk pre.length []) holes
      (inFrame c₁ blk (pre.length + 1) []) := by
    refine seg_safe_reg (Straight.Segment.left (xs := [Instr.mov .w64 .rdx (.reg .rax)]) seg) (by omega)
      (fun _ => by simp [Instr.mov]) (fun _ => by simp [Instr.mov]) rfl Runtime.rejecting ?_ ?_
    · exact footprint_noMem _ rfl (by simp)
    · rw [executeInstr_mov]; rfl
  -- `xor eax, eax`
  let c₂ := c₁.writeReg .w32 .rax (AluOp.xor.eval (c₁.readReg .rax) (c₁.readReg .rax))
  have seg₂ : Straight.Segment cs blk (pre.length + 1) ([Instr.alu .xor .w32 .rax (.reg .rax)] ++ wrapperEpilogue) := by
    simpa [wrapperTail] using Straight.Segment.right (xs := [Instr.mov .w64 .rdx (.reg .rax)]) seg
  have s2 : SafeSteps Runtime.rejecting cs 1 holes (inFrame c₁ blk (pre.length + 1) []) holes
      (inFrame c₂ blk (pre.length + 2) []) := by
    refine seg_safe_reg (Straight.Segment.left seg₂) (by omega)
      (fun _ => by simp [Instr.alu]) (fun _ => by simp [Instr.alu]) rfl Runtime.rejecting ?_ ?_
    · exact footprint_noMem _ rfl (by simp)
    · rw [executeInstr_alu]; rfl
  -- the epilogue
  have hc₂mem : c₂.memory = core.memory := by simp [c₂, c₁, Core.writeReg, Core.setReg]
  have hc₂rsp : c₂.readReg .rsp = entrySp := by simp [c₂, c₁, Core.writeReg, readReg_setReg', hrsp]
  have hmem0 : (inFrame core blk pre.length []).core.memory = core.memory := rfl
  obtain ⟨c₃, s3, hc₃mem, hc₃rsp, hc₃pop, hc₃other⟩ := epilogue_safe (b := blk) (o := pre.length + 2)
    (by simpa [Nat.add_assoc] using Straight.Segment.right seg₂) (by omega) Runtime.rejecting (holes := holes)
    (R := []) (core₀ := core₀) (retAddr := retAddr) hc₂rsp
    (fun i hi => by rw [hc₂mem]; exact ef.saves i (by omega)) (fun i hi => ef.savesData i (by omega))
  -- `ret`
  have hd6 : ReadableData holes (c₃.readReg .rsp) 8 := by rw [hc₃rsp]; simpa using ef.savesData 6 (by decide)
  have hret := code.safe_ret_top Runtime.rejecting c₃ holes hd6
  have hlen : (pre ++ wrapperTail).length = pre.length + 2 + 7 := by
    simp [wrapperTail, wrapperEpilogue, wrapperSaves]
  rw [hlen] at hret
  refine ⟨{ inFrame c₃ blk (pre.length + 2 + 7) [] with status := .halted (c₃.readReg .rax) }, ?_, ?_, ?_, ?_⟩
  · have := (((s1.append s2).append s3).append hret)
    simpa using this
  · have hrax : c₃.readReg .rax = 0 := by
      rw [hc₃other .rax (by decide) (by decide)]
      simp [c₂, Core.writeReg, readReg_setReg', AluOp.eval, Width.truncate]
    refine ⟨by simp [hrax], ?_, ?_, ?_, ?_⟩
    · show c₃.readReg .rdx = core.readReg .rax
      rw [hc₃other .rdx (by decide) (by decide)]
      simp [c₂, c₁, Core.writeReg, readReg_setReg']
    · intro r hr
      have hr' : r ∈ popOrder := by
        have : r ∈ [GPR.rbx, .rbp, .r12, .r13, .r14, .r15] := by simpa [SysV.calleeSaved] using hr
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at this
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [popOrder]
      exact hc₃pop r hr'
    · show c₃.readReg .rsp = core₀.readReg .rsp
      rw [hc₃rsp, ef.rsp0]
    · show c₃.memory.read64? (c₃.readReg .rsp) = .ok retAddr
      rw [hc₃mem, hc₂mem, hc₃rsp]
      have h6 := ef.saves 6 (by decide)
      simpa [saveWord, popOrder, inFrame] using h6
  · show c₃.memory = core.memory
    rw [hc₃mem, hc₂mem]
  · exact hd6

/-- An Xl return from the outermost activation, which ends the run: the
epilogue and `ret` into the wrapper, then the wrapper's tail, to an `Exit`
with status 0 and `Final`. -/
theorem step_done {S : Stk} {W : Wrap} {s : Xl.State} {m : Machine} {holes : Holes} {fr : Xl.Frame} {a : Act}
    {ret : ReturnFrame} (hm : Match S W s m holes fr a ret [])
    {f : Func Loc} {l : FrameLayout} {pl : Placed} (htop : Top S W s m holes fr a ret f l pl)
    {b : Block Loc} {codes : List (List Instr)} {post : List Instr} {t : X86.Terminator}
    (hpos : XlPos S fr f l pl b codes post t) (hpc : m.pc = pcOf S pl fr.label (offsetOf l fr.label fr.pos codes))
    (hend : fr.pos = b.body.size) {vs : List Loc} (hterm : b.term = .ret vs) (hcr : Xl.conventionResults vs = true)
    {vals : List Word} (hread : Xl.readAll s.regs fr vs = some vals) (hone : f.results = 1)
    (hwc : WrapCont S W) :
    ∃ n holes' after, SafeSteps Runtime.rejecting S.cs n holes m holes' after ∧
      ∃ val, Exit W.core₀ W.retAddr 0 val after ∧ Final (vals, s.mem) val after.core.memory holes' ∧
        ReadableData holes' (after.core.readReg .rsp) 8 := by
  obtain ⟨core₁, hst, hm₁, hslot, -, hk⟩ := ret_steps hm htop hpos hpc hend hterm
  have hg := hm.global
  have hf := htop.fn
  have hs := hf.checks.1
  -- The return frame is the wrapper's.
  obtain ⟨hframe, -, -, -, -⟩ := hm.chain f l pl hf
  obtain ⟨blk, pre, hcode, hcont⟩ := hwc
  have hreturns : m.returns = [ret] := by simpa using hm.returns
  have hsp : ret.returnSlot + 8 = W.entrySp := by
    rcases hg.entry.outer with h | ⟨inner, f₁, h, h₁, -⟩
    · rw [hreturns] at h; cases h
    · rw [hreturns] at h
      cases inner with
      | nil =>
        simp only [List.nil_append, List.cons.injEq, and_true] at h
        rw [h]; exact h₁
      | cons x inner' => simp at h
  -- The machine in the wrapper
  let core₂ := core₁.setReg .rsp (ret.returnSlot + 8)
  simp only [List.map_nil] at hst
  have hM : ({ core := core₂, pc := ret.continuation, returns := [], status := .running } : Machine) =
      inFrame core₂ blk pre.length [] := by
    rw [hframe, hcont]; rfl
  rw [hM] at hst
  have hglob : Global W s.mem (inFrame core₂ blk pre.length []) holes := by
    refine Global.mono hg (by show core₂.memory.readable = _; simp [core₂, Core.setReg, hm₁])
      (by show core₂.memory.writable = _; simp [core₂, Core.setReg, hm₁])
      (fun x _ => by show core₂.memory.bytes x = _; simp [core₂, Core.setReg, hm₁]) (fun x hx => .inl hx) ?_ (.inl rfl)
    show core₂.readReg .r15 = W.ctx
    rw [Validate.readReg_setReg, if_neg (by decide),
      hk _ (by decide) (fun h => by rcases saved_mem hs h with h | h | h | h <;> cases h)]
    exact htop.agree.ctxReg
  have hrsp₂ : core₂.readReg .rsp = W.entrySp := by
    rw [Validate.readReg_setReg, if_pos rfl, hsp]
  obtain ⟨after, hex, hexit, hmem, hdata⟩ := success_exit hcode hglob.entry rfl hrsp₂
  refine ⟨_, holes, after, hst.append hex, core₂.readReg .rax, hexit, ⟨?_, ?_, fun x hx => hg.holesFree x hx⟩, hdata⟩
  · -- The single result
    obtain ⟨hlenV, hgetV⟩ := readAll_get hread
    have hbmem : b ∈ f.blocks.toList := List.mem_of_getElem? (by simpa using hpos.block)
    have hvs : vs.length = 1 := by rw [(hf.arities hbmem).2.1 vs hterm, hone]
    obtain ⟨r, hr, hvs0⟩ := conventionResults_get hcr (i := 0) (by omega)
    simp only [Lir.Conv.resultRegs, List.getElem?_cons_zero, Option.some.injEq] at hr
    subst hr
    obtain ⟨v, hv, hrd⟩ := hgetV 0 _ hvs0
    have hreg : core₂.readReg .rax = v := by
      rw [Validate.readReg_setReg, if_neg (by decide), hk .rax (by decide) (resultReg_not_saved hs (by
        simp [Lir.Conv.resultRegs]))]
      exact htop.agree.regsRel .rax rfl v (by simpa [Xl.read, Xl.reserved] using hrd)
    obtain ⟨v', rfl⟩ := List.length_eq_one_iff.1 (hlenV.trans hvs)
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
    simp [hv, hreg]
  · show Inside s.mem after.core.memory
    rw [hmem]
    show Inside s.mem core₁.memory
    rw [hm₁]
    exact htop.agree.inside

end IxCC.Xv.Stacking.Proof
