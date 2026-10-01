import Compilatrix.Xv.Stacking.Proof.Shape
import Compilatrix.Xv.Stacking.Proof.Steps
import Compilatrix.X86.SafeStepsObject

/-!
# The failure exit (05 §6.1)

Every failure leaves through the export wrapper that was entered: a
`fail_k` block puts the status `k` in `eax` and jumps to `failExit`, which
reloads `rsp` from the context's `entrySp` cell (`unwind`, which drops the
ghost frames above the wrapper's), zeroes `edx`, and runs the wrapper's
epilogue. `EntryFrame` is what makes that sound: the cell holds the
wrapper's `rsp` at its call, the ghost frames end with the wrapper's own
call frame, the caller's callee-saved registers and return address sit
above `entrySp`, and `r15` still holds the context. `Wrapper.fail_safe`:
from any `fail_k` block under an `EntryFrame`, at most 13 checked typed steps
reach an `Exit` with status `k` and value 0.
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86 Compilatrix.X86.Stream


/-! ## The wrapper's frame -/

/-- The registers the wrapper's epilogue pops, in order: `r15` … `rbx`. -/
def popOrder : List X86.GPR := [.r15, .r14, .r13, .r12, .rbp, .rbx]

/-- The words above `entrySp`: the caller's `r15` … `rbx` (pushed in the
reverse order, then `sub rsp, 8`), then its return address. -/
def saveWord (core₀ : Core) (retAddr : Word) (i : Nat) : Word :=
  match popOrder[i]? with
  | some r => core₀.readReg r
  | none => retAddr

/-- What the failure exit needs (05 §6.1). `entrySp` is the wrapper's `rsp`
at its call, `ctx` the context register's value. -/
structure EntryFrame (ctx entrySp : Word) (core₀ : Core) (retAddr : Word) (s : Machine) (holes : Holes) : Prop where
  cell : s.core.memory.read64? (ctx - 64) = .ok entrySp
  cellData : ReadableData holes (ctx - 64) 8
  /-- No ghost frame at all (before the call), or the wrapper's call frame
  last, with no inner frame returning to `entrySp`. -/
  outer : s.returns = [] ∨ ∃ inner f₁, s.returns = inner ++ [f₁] ∧ f₁.returnSlot + 8 = entrySp ∧
    ∀ g ∈ inner, g.returnSlot + 8 ≠ entrySp
  saves : ∀ i < 7, s.core.memory.read64? (entrySp + UInt64.ofNat (8 + 8 * i)) = .ok (saveWord core₀ retAddr i)
  savesData : ∀ i < 7, ReadableData holes (entrySp + UInt64.ofNat (8 + 8 * i)) 8
  r15 : s.core.readReg .r15 = ctx
  rsp0 : core₀.readReg .rsp = entrySp + 56

/-- The cut lands on the wrapper's frame: no ghost frame is left. -/
theorem EntryFrame.cut {ctx entrySp : Word} {core₀ : Core} {retAddr : Word} {s : Machine} {holes : Holes}
    (ef : EntryFrame ctx entrySp core₀ retAddr s holes) : cutAt entrySp s.returns = some [] := by
  rcases ef.outer with h | ⟨inner, f₁, h, hf, hin⟩
  · rw [h]; rfl
  · rw [h]
    have hidx : (inner ++ [f₁]).findIdx? (·.returnSlot + 8 == entrySp) = some inner.length := by
      rw [List.findIdx?_append]
      have hn : inner.findIdx? (·.returnSlot + 8 == entrySp) = none := by
        rw [List.findIdx?_eq_none_iff]
        intro g hg
        simpa using hin g hg
      simp [hn, hf]
    cases hl : inner ++ [f₁] with
    | nil => simp at hl
    | cons g gs =>
        rw [← hl]
        simp only [cutAt]
        rw [hl] at hidx ⊢
        show Option.map (fun index => List.drop (index + 1) (g :: gs))
          (List.findIdx? (fun x => x.returnSlot + 8 == entrySp) (g :: gs)) = some []
        rw [hidx]
        simp only [Option.map_some, Option.some.injEq]
        rw [← hl]
        simp

/-! ## Addresses and frame instructions -/

theorem signExtend32_ofNat {n : Nat} (h : n < 2 ^ 31) : signExtend32 (UInt32.ofNat n) = UInt64.ofNat n := by
  have h32 : n < 2 ^ 32 := by omega
  have hv : (UInt32.ofNat n).toNat = n := UInt32.toNat_ofNat_of_lt' h32
  have hlt : UInt32.ofNat n < 0x80000000 := by
    rw [UInt32.lt_iff_toNat_lt, hv]; exact h
  simp only [signExtend32, hlt, ↓reduceIte]
  apply UInt64.toNat_inj.mp
  have hw : (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  simp only [UInt32.toNat_toUInt64]
  omega

theorem signExtend32_ofInt_neg {n : Nat} (h : n ≤ 2 ^ 31) :
    signExtend32 (Int32.ofInt (-(n : Int))).toUInt32 = 0 - UInt64.ofNat n := by
  apply UInt64.toBitVec_inj.mp
  rw [Encode.signExtend32_ofInt_of_bounds _ (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  have hw : (UInt64.ofNat n).toBitVec.toNat = n := by
    rw [UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  simp only [BitVec.toNat_ofInt, UInt64.toBitVec_sub, BitVec.toNat_sub, hw]
  simp
  omega

theorem rspAt_eval {off : Nat} (h : off < 2 ^ 31) (core : Core) :
    (rspAt off).eval core = core.readReg .rsp + UInt64.ofNat off := by
  simp [rspAt, MemAddr.eval, signExtend32_ofNat h]

theorem rspBelow_eval {off : Nat} (h : off ≤ 2 ^ 31) (core : Core) :
    (rspBelow off).eval core = core.readReg .rsp - UInt64.ofNat off := by
  simp only [rspBelow, MemAddr.eval, signExtend32_ofInt_neg h]
  simp [UInt64.sub_eq_add_neg]

theorem ctxAt_eval {n : Nat} (h : n ≤ 2 ^ 31) (core : Core) :
    (ctxAt (-(n : Int))).eval core = core.readReg .r15 - UInt64.ofNat n := by
  simp only [ctxAt, MemAddr.eval, signExtend32_ofInt_neg h]
  simp [UInt64.sub_eq_add_neg]

theorem entrySpCell_eval (core : Core) : entrySpCell.eval core = core.readReg .r15 - 64 :=
  ctxAt_eval (n := 64) (by decide) core

theorem stackLimitCell_eval (core : Core) : stackLimitCell.eval core = core.readReg .r15 - 56 :=
  ctxAt_eval (n := 56) (by decide) core

theorem stackBudgetCell_eval (core : Core) : stackBudgetCell.eval core = core.readReg .r15 - 48 :=
  ctxAt_eval (n := 48) (by decide) core

/-- `add rsp, n` and `sub rsp, n` are the `alu` constructor's rows. -/
theorem addRsp_eq {n : Nat} (h : n < 2 ^ 31) : addRsp n = Instr.alu .add .w64 .rsp (.imm (UInt32.ofNat n)) := by
  simp only [addRsp, Instr.alu, AluOp.mnemonic, signExtend32_ofNat h]

theorem subRsp_eq {n : Nat} (h : n < 2 ^ 31) : subRsp n = Instr.alu .sub .w64 .rsp (.imm (UInt32.ofNat n)) := by
  simp only [subRsp, Instr.alu, AluOp.mnemonic, signExtend32_ofNat h]

theorem exec_addRsp {n : Nat} (h : n < 2 ^ 31) (runtime : Runtime) (checked : Checked) (m : Machine) :
    executeInstr runtime checked (addRsp n) m = m.advanceWith (m.core.setReg .rsp (m.core.readReg .rsp + UInt64.ofNat n)) := by
  rw [addRsp_eq h, executeInstr_alu]
  simp [AluSource.eval, signExtend32_ofNat h, AluOp.eval, Core.writeReg]

theorem exec_subRsp {n : Nat} (h : n < 2 ^ 31) (runtime : Runtime) (checked : Checked) (m : Machine) :
    executeInstr runtime checked (subRsp n) m = m.advanceWith (m.core.setReg .rsp (m.core.readReg .rsp - UInt64.ofNat n)) := by
  rw [subRsp_eq h, executeInstr_alu]
  simp [AluSource.eval, signExtend32_ofNat h, AluOp.eval, Core.writeReg]

/-! ## Pops -/

theorem pop_footprint (r : GPR) (core : Core) :
    Stream.operationReads (Encode.instructionOperation (Instr.pop r)) core = [⟨core.readReg .rsp, 8⟩] ∧
      Stream.operationWrites (Encode.instructionOperation (Instr.pop r)) core = [] := by
  simp [Instr.pop, Encode.instructionOperation, Stream.operationReads, Stream.operationWrites, Op.reads,
    Op.writes, Op.pops, Op.pushes, slotReads, slotWrites, desc, Table.popDesc, Table.regSlot, Arg.access]

theorem readReg_setReg' (c : Core) (r r' : GPR) (v : Word) :
    (c.setReg r v).readReg r' = if r' = r then v else c.readReg r' := by
  simp [Core.setReg, Core.readReg, Registers.set]

/-- A run of pops at consecutive offsets, from words at `base`, `base + 8`, …:
each register gets its word, `rsp` moves past them, nothing else changes. -/
theorem pops_safe {cs : Checked} {b : BlockId} (runtime : Runtime) {holes : Holes} {R : List ReturnFrame} :
    ∀ (L : List GPR) {o : Nat} {core : Core} {base : Word} {vals : List Word},
      Straight.Segment cs b o (L.map Instr.pop) → o + L.length < UInt32.size → vals.length = L.length →
      core.readReg .rsp = base → L.Nodup → GPR.rsp ∉ L →
      (∀ (i : Nat) (v : Word), vals[i]? = some v → core.memory.read64? (base + UInt64.ofNat (8 * i)) = .ok v) →
      (∀ i < L.length, ReadableData holes (base + UInt64.ofNat (8 * i)) 8) →
      ∃ core', SafeSteps runtime cs L.length holes (inFrame core b o R) holes (inFrame core' b (o + L.length) R) ∧
        core'.memory = core.memory ∧ core'.readReg .rsp = base + UInt64.ofNat (8 * L.length) ∧
        (∀ (i : Nat) (r : GPR), L[i]? = some r → vals[i]? = some (core'.readReg r)) ∧
        (∀ r, r ∉ L → r ≠ .rsp → core'.readReg r = core.readReg r)
  | [], o, core, base, vals, _, _, hl, hrsp, _, _, _, _ => by
      refine ⟨core, .refl _ _, rfl, by simpa using hrsp, by simp, fun _ _ _ => rfl⟩
  | r :: L, o, core, base, vals, seg, fits, hl, hrsp, hnd, hnr, hv, hd => by
      obtain ⟨v, vs, rfl⟩ : ∃ v vs, vals = v :: vs := by
        cases vals with
        | nil => simp at hl
        | cons v vs => exact ⟨v, vs, rfl⟩
      simp only [List.nodup_cons, List.mem_cons, not_or] at hnd hnr
      have hread : core.memory.read64? (core.readReg .rsp) = .ok v := by
        simpa [hrsp] using hv 0 v rfl
      let core₁ := (core.setReg .rsp (core.readReg .rsp + 8)).setReg r v
      have hfp := pop_footprint r core
      have one : SafeSteps runtime cs 1 holes (inFrame core b o R) holes (inFrame core₁ b (o + 1) R) := by
        refine (Straight.Segment.left (xs := [Instr.pop r]) seg).safe_exec (by simp only [List.length_cons] at fits; omega)
          (fun _ => nofun) (fun _ => nofun) rfl runtime ⟨?_, ?_⟩ ?_ ?_
        · intro access ha
          rw [hfp.1] at ha
          simp only [List.mem_singleton] at ha
          subst ha
          simpa [hrsp] using hd 0 (by simp)
        · intro access ha; rw [hfp.2] at ha; simp at ha
        · simp [Stream.nextHoles, hfp.2, Stream.clearAccesses]
        · rw [executeInstr_pop]
          simp only [inFrame, hread]
          rfl
      have hrsp₁ : core₁.readReg .rsp = base + UInt64.ofNat 8 := by
        simp [core₁, readReg_setReg', hnr.1, hrsp]
      obtain ⟨core', rest, hmem, hrsp', hvals, hother⟩ := pops_safe runtime L (o := o + 1) (core := core₁)
        (base := base + UInt64.ofNat 8) (vals := vs)
        (by simpa [Nat.add_comm] using (Straight.Segment.right (xs := [Instr.pop r]) seg))
        (by simp only [List.length_cons] at fits; omega) (by simpa using hl) hrsp₁ hnd.2 hnr.2
        (fun i w hw => by
          have := hv (i + 1) w (by simpa using hw)
          simp only [core₁, Core.setReg] at this ⊢
          rw [show base + UInt64.ofNat 8 + UInt64.ofNat (8 * i) = base + UInt64.ofNat (8 * (i + 1)) by
            rw [UInt64.add_assoc]; congr 1; apply UInt64.toNat_inj.mp; simp <;> omega]
          exact this)
        (fun i hi => by
          rw [show base + UInt64.ofNat 8 + UInt64.ofNat (8 * i) = base + UInt64.ofNat (8 * (i + 1)) by
            rw [UInt64.add_assoc]; congr 1; apply UInt64.toNat_inj.mp; simp <;> omega]
          exact hd (i + 1) (by simp; omega))
      refine ⟨core', ?_, ?_, ?_, ?_, ?_⟩
      · have := one.append rest
        rw [show 1 + L.length = (r :: L).length by simp [Nat.add_comm],
          show o + 1 + L.length = o + (r :: L).length by simp; omega] at this
        exact this
      · rw [hmem]; rfl
      · rw [hrsp', UInt64.add_assoc]; congr 1; apply UInt64.toNat_inj.mp; simp <;> omega
      · intro i q hq
        cases i with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
            subst hq
            rw [hother r hnd.1 (Ne.symm hnr.1)]
            simp [core₁, readReg_setReg']
        | succ i => simpa using hvals i q (by simpa using hq)
      · intro q hq hqr
        simp only [List.mem_cons, not_or] at hq
        rw [hother q hq.2 hqr]
        simp [core₁, readReg_setReg', hq.1, hqr]

theorem addRsp_footprint (n : Nat) (core : Core) :
    Stream.operationReads (Encode.instructionOperation (addRsp n)) core = [] ∧
      Stream.operationWrites (Encode.instructionOperation (addRsp n)) core = [] := by
  unfold addRsp Instr.ofRow aluImmRow
  split <;> exact footprint_noMem core rfl (by simp)

theorem subRsp_footprint (n : Nat) (core : Core) :
    Stream.operationReads (Encode.instructionOperation (subRsp n)) core = [] ∧
      Stream.operationWrites (Encode.instructionOperation (subRsp n)) core = [] := by
  unfold subRsp Instr.ofRow aluImmRow
  split <;> exact footprint_noMem core rfl (by simp)

/-- A register-only step that advances with a new core (no memory touched). -/
theorem seg_safe_reg {cs : Checked} {b : BlockId} {o : Nat} {ins : Instr}
    (seg : Straight.Segment cs b o [ins]) (fits : o + 1 < UInt32.size)
    (plain : ∀ t, ins ≠ .call t) (noRuntime : ∀ i, ins ≠ .callRuntime i) (single : ins.single = true)
    (runtime : Runtime) {holes : Holes} {R : List ReturnFrame} {core core' : Core}
    (fp : Stream.operationReads (Encode.instructionOperation ins) core = [] ∧
      Stream.operationWrites (Encode.instructionOperation ins) core = [])
    (exec : executeInstr runtime cs ins (inFrame core b o R) = (inFrame core b o R).advanceWith core') :
    SafeSteps runtime cs 1 holes (inFrame core b o R) holes (inFrame core' b (o + 1) R) :=
  seg.safe_exec fits plain noRuntime single runtime
    ⟨fun a ha => by rw [fp.1] at ha; simp at ha, fun a ha => by rw [fp.2] at ha; simp at ha⟩
    (by simp [Stream.nextHoles, fp.2, Stream.clearAccesses]) exec

theorem wrapperEpilogue_eq : wrapperEpilogue = addRsp 8 :: popOrder.map Instr.pop := rfl

/-- The wrapper's epilogue from `rsp = entrySp`: the caller's registers come
back from their saves and `rsp` stops at the caller's return address. -/
theorem epilogue_safe {cs : Checked} {b : BlockId} {o : Nat} (seg : Straight.Segment cs b o wrapperEpilogue)
    (fits : o + 7 < UInt32.size) (runtime : Runtime) {holes : Holes} {R : List ReturnFrame} {core core₀ : Core}
    {entrySp retAddr : Word} (hrsp : core.readReg .rsp = entrySp)
    (hsaves : ∀ i < 6, core.memory.read64? (entrySp + UInt64.ofNat (8 + 8 * i)) = .ok (saveWord core₀ retAddr i))
    (hdata : ∀ i < 6, ReadableData holes (entrySp + UInt64.ofNat (8 + 8 * i)) 8) :
    ∃ core', SafeSteps runtime cs 7 holes (inFrame core b o R) holes (inFrame core' b (o + 7) R) ∧
      core'.memory = core.memory ∧ core'.readReg .rsp = entrySp + 56 ∧
      (∀ r ∈ popOrder, core'.readReg r = core₀.readReg r) ∧
      (∀ r, r ∉ popOrder → r ≠ .rsp → core'.readReg r = core.readReg r) := by
  rw [wrapperEpilogue_eq] at seg
  let core₁ := core.setReg .rsp (core.readReg .rsp + UInt64.ofNat 8)
  have one : SafeSteps runtime cs 1 holes (inFrame core b o R) holes (inFrame core₁ b (o + 1) R) :=
    seg_safe_reg (Straight.Segment.left (xs := [addRsp 8]) seg) (by omega) (fun _ => by
      simp [addRsp, Instr.ofRow, aluImmRow]) (fun _ => by
      simp [addRsp, Instr.ofRow, aluImmRow]) (by
      simp [addRsp, Instr.ofRow, aluImmRow]; split <;> rfl) runtime (addRsp_footprint 8 core)
      (exec_addRsp (by decide) runtime cs _)
  have hrsp₁ : core₁.readReg .rsp = entrySp + UInt64.ofNat 8 := by
    simp [core₁, readReg_setReg', hrsp]
  obtain ⟨core', rest, hmem, hrsp', hvals, hother⟩ := pops_safe runtime popOrder (o := o + 1) (core := core₁)
    (base := entrySp + UInt64.ofNat 8) (vals := popOrder.map core₀.readReg)
    (by simpa [popOrder] using (Straight.Segment.right (xs := [addRsp 8]) seg)) (by simp [popOrder]; omega)
    (by simp) hrsp₁ (by decide) (by decide)
    (fun i v hv => by
      have hi : i < 6 := by
        have := (List.getElem?_eq_some_iff.1 hv).1; simpa [popOrder] using this
      have := hsaves i hi
      simp only [core₁, Core.setReg] at this ⊢
      rw [show entrySp + UInt64.ofNat 8 + UInt64.ofNat (8 * i) = entrySp + UInt64.ofNat (8 + 8 * i) by
        rw [UInt64.add_assoc]; congr 1; apply UInt64.toNat_inj.mp; simp <;> omega, this]
      congr 1
      simp only [saveWord, List.getElem?_map] at hv ⊢
      cases hp : popOrder[i]? with
      | none => simp [hp] at hv
      | some r => simp [hp] at hv ⊢; exact hv)
    (fun i hi => by
      rw [show entrySp + UInt64.ofNat 8 + UInt64.ofNat (8 * i) = entrySp + UInt64.ofNat (8 + 8 * i) by
        rw [UInt64.add_assoc]; congr 1; apply UInt64.toNat_inj.mp; simp <;> omega]
      exact hdata i (by simpa [popOrder] using hi))
  refine ⟨core', ?_, ?_, ?_, ?_, ?_⟩
  · have := one.append rest
    rw [show 1 + popOrder.length = 7 from rfl, show o + 1 + popOrder.length = o + 7 from rfl] at this
    exact this
  · rw [hmem]; rfl
  · rw [hrsp']; rw [UInt64.add_assoc]; congr 1
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    have := hvals i _ (List.getElem?_eq_getElem hi)
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] at this
    exact this.symm
  · intro r hr hrr
    rw [hother r hr hrr]
    simp [core₁, readReg_setReg', hrr]

/-! ## The failure exit -/

/-- The exit group's blocks are a program's first blocks (`exit_at`). -/
def ExitGroupAt (cs : Checked) : Prop := ∀ j < exitBlocks, cs.program.blocks[j]? = (exitGroup 0)[j]?

theorem ExitGroupAt.fail {cs : Checked} (h : ExitGroupAt cs) {k : Nat} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    BlockCode cs (UInt32.ofNat (k - 1)) [Instr.mov .w32 .rax (.imm (UInt64.ofNat k))] (.jump (UInt32.ofNat 4)) := by
  refine ⟨?_, by simp [UInt32.size]⟩
  rw [UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega), h (k - 1) (by simp [exitBlocks]; omega)]
  have hk : k - 1 < 4 := by omega
  rw [exitGroup, List.getElem?_append_left (by simpa using hk), List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Nat.zero_add, show k - 1 + 1 = k by omega]

theorem ExitGroupAt.failExit {cs : Checked} (h : ExitGroupAt cs) :
    BlockCode cs (UInt32.ofNat 4) (Instr.unwind entrySpCell :: Instr.alu .xor .w32 .rdx (.reg .rdx) :: wrapperEpilogue)
      .ret := by
  refine ⟨?_, by decide⟩
  rw [UInt32.toNat_ofNat_of_lt' (by decide), h 4 (by decide)]
  rfl

/-- **The failure exit** (05 §6.1): from a `fail_k` block under an
`EntryFrame`, at most 13 checked typed steps reach an `Exit` with status `k`
and value 0, the caller's callee-saved registers and stack pointer
restored. -/
theorem Wrapper.fail_safe {cs : Checked} (hexit : ExitGroupAt cs) (runtime : Runtime) {ctx entrySp retAddr : Word}
    {core₀ : Core} {s : Machine} {holes : Holes} {k : Nat} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (ef : EntryFrame ctx entrySp core₀ retAddr s holes) (pc : s.pc = ⟨UInt32.ofNat (k - 1), 0⟩)
    (running : s.status = .running) :
    ∃ n after, n ≤ 13 ∧ SafeSteps runtime cs n holes s holes after ∧ Exit core₀ retAddr (UInt64.ofNat k) 0 after := by
  have hs : s = inFrame s.core (UInt32.ofNat (k - 1)) 0 s.returns := by
    rw [inFrame_eq running, pc]; rfl
  have fcode := hexit.fail hk1 hk4
  have xcode := hexit.failExit
  have h4 : cs.program.hasBlock (UInt32.ofNat 4) = true := xcode.hasBlock
  -- `mov eax, k`
  let c₁ := s.core.writeReg .w32 .rax (UInt64.ofNat k)
  have s1 : SafeSteps runtime cs 1 holes (inFrame s.core (UInt32.ofNat (k - 1)) 0 s.returns) holes
      (inFrame c₁ (UInt32.ofNat (k - 1)) 1 s.returns) := by
    refine seg_safe_reg (fcode.segment) (by decide) (fun _ => by simp [Instr.mov, Instr.ofRow, movImmRow])
      (fun _ => by simp [Instr.mov, Instr.ofRow, movImmRow]) rfl runtime ?_ ?_
    · exact footprint_noMem _ rfl (by simp [movImmRow])
    · rw [executeInstr_mov]; rfl
  -- `jmp failExit`
  have s2 := fcode.safe_jump h4 runtime c₁ s.returns holes
  -- `unwind [r15 − 64]`
  have hc₁r15 : c₁.readReg .r15 = ctx := by simp [c₁, Core.writeReg, readReg_setReg', ef.r15]
  have hc₁mem : c₁.memory = s.core.memory := by simp [c₁, Core.writeReg, Core.setReg]
  have s3 := Straight.Segment.safe_unwind (block := UInt32.ofNat 4) (offset := 0)
    (Straight.Segment.left (xs := [Instr.unwind entrySpCell]) xcode.segment) (by decide) runtime c₁ s.returns
    holes (sp := entrySp) (by rw [entrySpCell_eval, hc₁r15]; exact ef.cellData)
    (by rw [entrySpCell_eval, hc₁r15, hc₁mem]; exact ef.cell) ef.cut
  -- `xor edx, edx`
  let c₂ := c₁.setReg .rsp entrySp
  let c₃ := c₂.writeReg .w32 .rdx (AluOp.xor.eval (c₂.readReg .rdx) (c₂.readReg .rdx))
  have s4 : SafeSteps runtime cs 1 holes (inFrame c₂ (UInt32.ofNat 4) 1 []) holes
      (inFrame c₃ (UInt32.ofNat 4) 2 []) := by
    refine seg_safe_reg (Straight.Segment.left (xs := [Instr.alu .xor .w32 .rdx (.reg .rdx)])
      (Straight.Segment.right (xs := [Instr.unwind entrySpCell]) xcode.segment)) (by decide)
      (fun _ => by simp [Instr.alu]) (fun _ => by simp [Instr.alu]) rfl runtime ?_ ?_
    · exact footprint_noMem _ rfl (by simp)
    · rw [executeInstr_alu]; rfl
  -- the epilogue
  have hc₃mem : c₃.memory = s.core.memory := by simp [c₃, c₂, Core.writeReg, Core.setReg, hc₁mem]
  have hc₃rsp : c₃.readReg .rsp = entrySp := by simp [c₃, c₂, Core.writeReg, readReg_setReg']
  obtain ⟨c₄, s5, hc₄mem, hc₄rsp, hc₄pop, hc₄other⟩ := epilogue_safe (b := UInt32.ofNat 4) (o := 2)
    (by simpa using (Straight.Segment.right (xs := [Instr.unwind entrySpCell, Instr.alu .xor .w32 .rdx (.reg .rdx)])
      (by simpa using xcode.segment))) (by decide) runtime (holes := holes) (R := []) (core₀ := core₀)
    (retAddr := retAddr) hc₃rsp (fun i hi => by rw [hc₃mem]; exact ef.saves i (by omega))
    (fun i hi => ef.savesData i (by omega))
  -- `ret`
  have hret := xcode.safe_ret_top runtime c₄ holes (by rw [hc₄rsp]; simpa using ef.savesData 6 (by decide))
  refine ⟨12, { inFrame c₄ (UInt32.ofNat 4) 9 [] with status := .halted (c₄.readReg .rax) }, by decide, ?_, ?_⟩
  · rw [hs]
    have := ((((s1.append s2).append s3).append s4).append s5).append hret
    simpa [wrapperEpilogue_eq, popOrder] using this
  · have hrax : c₄.readReg .rax = UInt64.ofNat k := by
      rw [hc₄other .rax (by decide) (by decide)]
      simp only [c₃, c₂, c₁, Core.writeReg, readReg_setReg']
      simp only [reduceCtorEq, ↓reduceIte]
      exact Encode.truncate32_of_small _ (by rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]; omega)
    refine ⟨by simp [inFrame, hrax], ?_, ?_, ?_, ?_⟩
    · show c₄.readReg .rdx = 0
      rw [hc₄other .rdx (by decide) (by decide)]
      simp [c₃, Core.writeReg, readReg_setReg', AluOp.eval, Width.truncate]
    · intro r hr
      have hr' : r ∈ popOrder := by
        have : r ∈ [GPR.rbx, .rbp, .r12, .r13, .r14, .r15] := by simpa [SysV.calleeSaved] using hr
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at this
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [popOrder]
      exact hc₄pop r hr'
    · show c₄.readReg .rsp = core₀.readReg .rsp
      rw [hc₄rsp, ef.rsp0]
    · show c₄.memory.read64? (c₄.readReg .rsp) = .ok retAddr
      rw [hc₄mem, hc₃mem, hc₄rsp]
      simpa [saveWord, popOrder] using ef.saves 6 (by decide)

end Compilatrix.Xv.Stacking.Proof
