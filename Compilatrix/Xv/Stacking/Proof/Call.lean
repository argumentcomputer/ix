import Compilatrix.Xv.Stacking.Proof.StepTerm

/-!
# The machine steps of a call

A direct call (`Straight.Segment.safe_call`), a callee's stack check
(`check_steps`: `lea r11, [rsp − (size + slack)]`, then `cmp r11,
[r15 − 56]; jb fail₂`), and its prologue (`prologue_steps`: `sub rsp,
size` and one store per saved register), each as checked steps.
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86 Compilatrix.X86.Stream

/-- A direct call: one checked step that pushes the return address, adds
its slot to the holes and records the return frame. -/
theorem Straight.Segment.safe_call {checked : Checked} {block target : BlockId} {offset : Nat}
    (segment : Straight.Segment checked block offset [.call target]) (fits : offset + 1 < UInt32.size)
    (valid : checked.program.hasBlock target = true) (runtime : Runtime) {holes : Holes}
    {returns : List ReturnFrame} {core : Core} (aligned : SysV.callSiteAligned (core.readReg .rsp) = true)
    (writable : Memory.rangeAllowed core.memory.writable (core.readReg .rsp - 8) 8 = true)
    (disjoint : FramesDisjoint returns (core.readReg .rsp - 8) 8) :
    SafeSteps runtime checked 1 holes (inFrame core block offset returns) (addRange holes (core.readReg .rsp - 8) 8)
      (inFrame (callCore core block offset) target 0 (callFrame core block offset :: returns)) := by
  obtain ⟨code, found, reads⟩ := segment
  have head := reads 0 (by simp)
  simp only [Nat.add_zero, List.getElem?_cons_zero] at head
  have hoff : (UInt32.ofNat offset).toNat = offset := UInt32.toNat_ofNat_of_lt' (by omega)
  have hsafe : SafeAt checked.program holes (inFrame core block offset returns) := by
    simp only [SafeAt, inFrame, hoff, found, head]
    exact ⟨aligned, writable, disjoint⟩
  have hholes : holeStep checked.program (inFrame core block offset returns) holes =
      addRange holes (core.readReg .rsp - 8) 8 := by
    simp only [holeStep, inFrame, hoff, found, head]
  rw [← hholes]
  exact SafeSteps.single hsafe (call_inFrame ⟨code, found, reads⟩ fits valid runtime core returns aligned writable)

/-! ## The stack check -/

theorem lea_foot (d : GPR) (m : MemAddr) (core : Core) :
    Stream.operationReads (Encode.instructionOperation (Instr.lea d m)) core = [] ∧
      Stream.operationWrites (Encode.instructionOperation (Instr.lea d m)) core = [] := by
  simp [Instr.lea, Encode.instructionOperation, Stream.operationReads, Stream.operationWrites, Op.reads,
    Op.writes, Op.pops, Op.pushes, desc, Table.leaDesc, Table.regSlot, slotReads, slotWrites, Arg.access]

/-- `cmp r, [m]`: the carry is the unsigned comparison. -/
theorem cmp_exec (r : GPR) (m : MemAddr) (core : Core) {v : Word} (h : core.memory.read? .w64 (m.eval core) = .ok v) :
    cmpRM.exec [.reg r, .mem m] core {} =
      .ok (core, ByteEval.Flags.merge Table.allSet {} (ByteEval.aluFlags .sub .w64 (core.readReg r) v)) := by
  simp [cmpRM, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.arithDesc, Table.cmpArith, Table.Arith.sem,
      Table.Arith.role, Table.cmpSem, Table.rmSlot, Table.regSlot, readSlots, writeSlots, Arg.load, Arg.store,
      Except.mapError, h, bind, Except.bind, pure, Except.pure]

theorem cmp_test (a b : Word) :
    (ByteEval.Flags.merge Table.allSet {} (ByteEval.aluFlags .sub .w64 a b)).test .unsignedLt =
      some (decide (a.toNat < b.toNat)) := by
  simp [ByteEval.Flags.test, ByteEval.Flags.merge, Table.allSet, FlagEffect.pick, ByteEval.aluFlags,
      ByteEval.subFlags, ByteEval.resultFlags, BitVec.usubOverflow, Width.bits]

theorem cmp_foot (r : GPR) (m : MemAddr) (core : Core) :
    Op.reads cmpRM [.reg r, .mem m] core = [⟨m.eval core, 8⟩] ∧ Op.writes cmpRM [.reg r, .mem m] core = [] := by
  simp [cmpRM, Op.reads, Op.writes, Op.pops, Op.pushes, desc, Table.arithDesc, Table.cmpArith, Table.Arith.role,
    Table.rmSlot, Table.regSlot, slotReads, slotWrites, Arg.access, Width.bytes]

/-- A checked function's stack check from `rsp = R`: `lea` then the branch,
two checked steps to `fail₂` when `R − (size + slack)` is below the limit
and to `next` otherwise; only `r11` changes. -/
theorem check_steps {cs : Checked} {block fail₂ next : BlockId} {l : FrameLayout}
    (code : BlockCode cs block [Instr.lea .r11 (rspBelow (l.size + slack))]
      (.branch cmpRM [.reg .r11, .mem stackLimitCell] .unsignedLt fail₂ next))
    (hbound : l.size + slack ≤ 2 ^ 31) (h2 : cs.program.hasBlock fail₂ = true) (hn : cs.program.hasBlock next = true)
    {holes : Holes} {returns : List ReturnFrame} {core : Core} {lim : Word}
    (hlim : core.memory.read64? (core.readReg .r15 - 56) = .ok lim)
    (hdata : ReadableData holes (core.readReg .r15 - 56) 8) :
    SafeSteps Runtime.rejecting cs 2 holes (inFrame core block 0 returns) holes
      (inFrame (core.setReg .r11 (core.readReg .rsp - UInt64.ofNat (l.size + slack)))
        (if (core.readReg .rsp - UInt64.ofNat (l.size + slack)).toNat < lim.toNat then fail₂ else next) 0 returns) := by
  have hseg : Straight.Segment cs block 0 [Instr.lea .r11 (rspBelow (l.size + slack))] := code.segment
  have hlea := seg_safe_reg hseg (by simp [UInt32.size]) (fun _ => nofun) (fun _ => nofun) rfl Runtime.rejecting
    (holes := holes) (R := returns) (core := core)
    (core' := core.setReg .r11 (core.readReg .rsp - UInt64.ofNat (l.size + slack))) (lea_foot _ _ core) (by
      rw [executeInstr_lea, rspBelow_eval hbound]; rfl)
  obtain ⟨core₁, hcore₁⟩ : ∃ c, c = core.setReg .r11 (core.readReg .rsp - UInt64.ofNat (l.size + slack)) :=
    ⟨_, rfl⟩
  rw [← hcore₁] at hlea ⊢
  have hc' : core₁.readReg .r15 = core.readReg .r15 := by rw [hcore₁]; simp [Validate.readReg_setReg]
  have hm' : core₁.memory = core.memory := by rw [hcore₁]; rfl
  have hr11 : core₁.readReg .r11 = core.readReg .rsp - UInt64.ofNat (l.size + slack) := by
    rw [hcore₁]; simp [Validate.readReg_setReg]
  have hev : stackLimitCell.eval core₁ = core.readReg .r15 - 56 := by rw [stackLimitCell_eval, hc']
  have hex := cmp_exec .r11 stackLimitCell core₁ (v := lim) (by rw [hev, hm']; exact hlim)
  have htest := cmp_test (core₁.readReg .r11) lim
  have hacc : OperationSafe holes returns (.op cmpRM [.reg .r11, .mem stackLimitCell]) core₁ := by
    refine ⟨fun acc hacc => ?_, fun acc hacc => ?_⟩
    · simp only [Stream.operationReads, (cmp_foot .r11 stackLimitCell core₁).1, List.mem_singleton] at hacc
      subst hacc
      rw [hev]; exact hdata
    · simp [Stream.operationWrites, (cmp_foot .r11 stackLimitCell core₁).2] at hacc
  have hvalid : cs.program.hasBlock (if decide ((core₁.readReg .r11).toNat < lim.toNat)
      then fail₂ else next) = true := by split <;> assumption
  have hbr := code.safe_branch Runtime.rejecting core₁ returns holes hacc hex htest hvalid
  have hkeep : Stream.nextHoles holes (.op cmpRM [.reg .r11, .mem stackLimitCell]) core₁ = holes := by
    simp [Stream.nextHoles, Stream.operationWrites, (cmp_foot .r11 stackLimitCell core₁).2, Stream.clearAccesses]
  rw [hkeep, hr11] at hbr
  have := hlea.append hbr
  simpa using this

/-! ## Stores of saved registers -/

theorem store_exec_ok {core : Core} {a : Word} {r : GPR} (hw : ∀ i < 8, core.memory.writable (a + UInt64.ofNat i) = true) :
    core.memory.write? .w64 a (core.readReg r) = .ok (core.memory.write .w64 a (core.readReg r)) := by
  have h := (rangeAllowed_iff core.memory.writable a 8).2 hw
  simp [Memory.write?, w64_bytes, h]

/-- Stores of registers to `rsp`-relative cells, one checked step each: the
cells hold the registers, no other byte changes, registers are kept, and
the stored cells are no longer holes. -/
theorem stores_steps {cs : Checked} {block : BlockId} {returns : List ReturnFrame} :
    ∀ (L : List (GPR × Nat)) {off : Nat} {holes : Holes} {core : Core},
      Straight.Segment cs block off (L.map fun p => Instr.store .w64 (rspAt p.2) p.1) →
      off + L.length < UInt32.size → (∀ p ∈ L, p.2 < 2 ^ 31) →
      (∀ p ∈ L, ∀ i < 8, core.memory.writable (core.readReg .rsp + UInt64.ofNat p.2 + UInt64.ofNat i) = true) →
      (∀ p ∈ L, FramesDisjoint returns (core.readReg .rsp + UInt64.ofNat p.2) 8) →
      L.Pairwise (fun p q => ∀ i < 8, ∀ j < 8,
        core.readReg .rsp + UInt64.ofNat p.2 + UInt64.ofNat i ≠ core.readReg .rsp + UInt64.ofNat q.2 + UInt64.ofNat j) →
      ∃ mem' holes', SafeSteps Runtime.rejecting cs L.length holes (inFrame core block off returns) holes'
          (inFrame { core with memory := mem' } block (off + L.length) returns) ∧
        mem'.readable = core.memory.readable ∧ mem'.writable = core.memory.writable ∧
        (∀ x, (∀ p ∈ L, ∀ i < 8, x ≠ core.readReg .rsp + UInt64.ofNat p.2 + UInt64.ofNat i) →
          mem'.bytes x = core.memory.bytes x) ∧
        (∀ p ∈ L, mem'.read64 (core.readReg .rsp + UInt64.ofNat p.2) = core.readReg p.1) ∧
        (∀ x, holes' x → holes x) ∧ (∀ p ∈ L, ReadableData holes' (core.readReg .rsp + UInt64.ofNat p.2) 8)
  | [], off, holes, core, _, _, _, _, _, _ =>
      ⟨core.memory, holes, by simpa using SafeSteps.refl holes (inFrame core block off returns), rfl, rfl,
        fun _ _ => rfl, by simp, fun _ h => h, by simp⟩
  | (r, o) :: L, off, holes, core, hseg, hfits, hoff, hw, hdis, hpw => by
      have hseg' : Straight.Segment cs block off
          ([Instr.store .w64 (rspAt o) r] ++ L.map fun p => Instr.store .w64 (rspAt p.2) p.1) := by simpa using hseg
      have hev : (rspAt o).eval core = core.readReg .rsp + UInt64.ofNat o := rspAt_eval (hoff (r, o) (by simp)) core
      have hwr := store_exec_ok (core := core) (a := core.readReg .rsp + UInt64.ofNat o) (r := r) (hw (r, o) (by simp))
      have hfoot := store64_foot (rspAt o) r core
      have hsafe : OperationSafe holes returns (Encode.instructionOperation (Instr.store .w64 (rspAt o) r)) core := by
        refine ⟨fun acc hacc => ?_, fun acc hacc => ?_⟩
        · simp [Instr.store, Encode.instructionOperation, Stream.operationReads, hfoot.1] at hacc
        · simp only [Instr.store, Encode.instructionOperation, Stream.operationWrites, hfoot.2,
            List.mem_singleton] at hacc
          subst hacc
          rw [hev]; exact hdis (r, o) (by simp)
      have hone := hseg'.left.safe_exec (by simp at hfits; omega) (fun _ => nofun) (fun _ => nofun) rfl
        Runtime.rejecting
        (core' := { core with memory := core.memory.write .w64 (core.readReg .rsp + UInt64.ofNat o) (core.readReg r) })
        hsafe rfl (by
          rw [executeInstr_store]
          simp only [inFrame, Core.storeReg?, hev, hwr, bind, Except.bind, pure, Except.pure])
      have hnext : Stream.nextHoles holes (Encode.instructionOperation (Instr.store .w64 (rspAt o) r)) core =
          clearRange holes (core.readReg .rsp + UInt64.ofNat o) 8 := by
        simp [Instr.store, Encode.instructionOperation, Stream.nextHoles, Stream.operationWrites, hfoot.2,
          Stream.clearAccesses, hev]
      rw [hnext] at hone
      have hpw' := List.pairwise_cons.1 hpw
      obtain ⟨mem', holes', hrest, hr', hw', hb', hv', hh', hd'⟩ := stores_steps L (off := off + 1)
        (holes := clearRange holes (core.readReg .rsp + UInt64.ofNat o) 8)
        (core := { core with memory := core.memory.write .w64 (core.readReg .rsp + UInt64.ofNat o) (core.readReg r) })
        (by simpa using hseg'.right) (by simp at hfits ⊢; omega) (fun p hp => hoff p (by simp [hp]))
        (fun p hp i hi => by simpa [Core.readReg] using hw p (by simp [hp]) i hi)
        (fun p hp => hdis p (by simp [hp])) hpw'.2
      refine ⟨mem', holes', ?_, by rw [hr']; simp, by rw [hw']; simp, fun x hx => ?_, fun p hp => ?_,
        fun x hx => (hh' x hx).1, fun p hp => ?_⟩
      · have := hone.append hrest
        rw [show off + 1 + L.length = off + ((r, o) :: L).length by simp; omega,
          show 1 + L.length = ((r, o) :: L).length by simp; omega] at this
        exact this
      · rw [hb' x (fun p hp i hi => hx p (by simp [hp]) i hi)]
        exact Memory.writeLittle_bytes_outside _ _ _ _ _ fun i hi => hx (r, o) (by simp) i hi
      · rcases List.mem_cons.1 hp with rfl | hp
        · show mem'.read64 (core.readReg .rsp + UInt64.ofNat o) = core.readReg r
          rw [read64_congr (m := core.memory.write .w64 (core.readReg .rsp + UInt64.ofNat o) (core.readReg r))
            (m' := mem') (fun i hi => hb' _ (fun q hq j hj => hpw'.1 q hq i hi j hj))]
          exact Memory.read64_write64 _ _ _
        · exact hv' p hp
      · rcases List.mem_cons.1 hp with rfl | hp
        · intro i hi hx
          exact (hh' _ hx).2 ⟨i, hi, rfl⟩
        · exact hd' p hp

end Compilatrix.Xv.Stacking.Proof
