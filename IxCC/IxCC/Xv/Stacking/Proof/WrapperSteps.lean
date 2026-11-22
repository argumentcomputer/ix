import IxCC.Xv.Stacking.Proof.Sim

/-!
# The export wrapper's instructions as checked steps

Before its call, the wrapper runs with no ghost frame and no hole, so every
instruction that executes is a checked step (`bare_step`). Its pieces: the
pushes of the caller's callee-saved registers (`pushes_steps`), the rows of
its head (`subRM_exec`), the `Nat` check (`ors_steps`, `test_exec`,
`test_signedLt`: the OR of the `Nat` arguments has its sign bit set exactly
when one of them is at least 2^63, `or_big`), and the moves and tags of the
arguments into the internal convention's registers (`marshal_steps`).
`wrapper_ok` takes the wrapper's code apart.
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86 IxCC.X86.Stream

/-! ## Steps without holes or frames -/

/-- With no hole and no ghost frame, an instruction that executes is a
checked step, and leaves no hole. -/
theorem bare_step {cs : Checked} {blk : BlockId} {o : Nat} {ins : Instr} (seg : Straight.Segment cs blk o [ins])
    (fits : o + 1 < UInt32.size) (plain : ∀ t, ins ≠ .call t) (noRuntime : ∀ i, ins ≠ .callRuntime i)
    (single : ins.single = true) {holes : Holes} (hempty : ∀ x, ¬holes x) {core core' : Core}
    (exec : executeInstr Runtime.rejecting cs ins (inFrame core blk o []) = (inFrame core blk o []).advanceWith core') :
    ∃ holes', SafeSteps Runtime.rejecting cs 1 holes (inFrame core blk o []) holes' (inFrame core' blk (o + 1) []) ∧
      ∀ x, ¬holes' x :=
  ⟨_, seg.safe_exec fits plain noRuntime single Runtime.rejecting
      ⟨fun _ _ i _ h => hempty _ h, fun _ _ frame hf => by simp at hf⟩ rfl exec,
    fun x h => hempty x (clearAccesses_sub _ _ x h)⟩

theorem write64?_ok {mem : Memory} {a v : Word} (h : ∀ i < 8, mem.writable (a + UInt64.ofNat i) = true) :
    mem.write64? a v = .ok (mem.write64 a v) := by
  have h' := (rangeAllowed_iff mem.writable a 8).2 h
  simp [Memory.write64?, Memory.write?, w64_bytes, h', Memory.write64]

theorem read?_ok {mem : Memory} {a : Word} (h : ∀ i < 8, mem.readable (a + UInt64.ofNat i) = true) :
    mem.read? .w64 a = .ok (mem.read64 a) := by
  have h' := (rangeAllowed_iff mem.readable a 8).2 h
  simp [Memory.read?, w64_bytes, h', Memory.read64]

/-! ## Rows of the wrapper -/

theorem subRM_exec (r : GPR) (m : MemAddr) (core : Core) {v : Word}
    (h : core.memory.read? .w64 (m.eval core) = .ok v) :
    ∃ fl, subRM.exec [.reg r, .mem m] core {} = .ok (core.setReg r (core.readReg r - v), fl) := by
  simp [subRM, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.arithDesc, Table.subArith, Table.Arith.sem,
      Table.Arith.role, Table.aluSem, Table.rmSlot, Table.regSlot, readSlots, writeSlots, Arg.load, Arg.store,
      Except.mapError, h, bind, Except.bind, pure, Except.pure, Core.writeReg, AluOp.eval]

theorem orMR_exec (d s : GPR) (core : Core) :
    ∃ fl, orMR.exec [.reg d, .reg s] core {} = .ok (core.setReg d (core.readReg d ||| core.readReg s), fl) := by
  simp [orMR, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.arithDesc, Table.orArith, Table.Arith.sem,
      Table.Arith.role, Table.aluSem, Table.rmSlot, Table.regSlot, readSlots, writeSlots, Arg.load, Arg.store,
      Except.mapError, bind, Except.bind, pure, Except.pure, Core.writeReg, AluOp.eval]

theorem test_exec (r : GPR) (core : Core) :
    testMR.exec [.reg r, .reg r] core {} =
      .ok (core, ByteEval.Flags.merge Table.allSet {} (ByteEval.aluFlags .and .w64 (core.readReg r) (core.readReg r))) := by
  simp [testMR, Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.testDesc, Table.testSem, Table.rmSlot,
      Table.regSlot, readSlots, writeSlots, Arg.load, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- `test r, r; jl`: taken exactly when the sign bit is set. -/
theorem test_signedLt (a : Word) :
    (ByteEval.Flags.merge Table.allSet {} (ByteEval.aluFlags .and .w64 a a)).test .signedLt =
      some (decide (2 ^ 63 ≤ a.toNat)) := by
  simp [ByteEval.Flags.test, ByteEval.Flags.merge, Table.allSet, FlagEffect.pick, ByteEval.aluFlags,
      ByteEval.resultFlags, Width.bits]
  have h : ∀ x : BitVec 64, (x &&& x).msb = decide (2 ^ 63 ≤ x.toNat) := by
    intro x; rw [BitVec.and_self, BitVec.msb_eq_decide]
  exact (h a.toBitVec).trans (by simp)

theorem word_big (a : Word) : (2 ^ 63 ≤ a.toNat) = (a.toBitVec.msb = true) := by
  rw [BitVec.msb_eq_decide]; simp

/-- The sign bit of an OR. -/
theorem or_big (a b : Word) : 2 ^ 63 ≤ (a ||| b).toNat ↔ 2 ^ 63 ≤ a.toNat ∨ 2 ^ 63 ≤ b.toNat := by
  rw [word_big, word_big, word_big]
  simp [BitVec.msb_or]

theorem foldl_or_big (rest : List Word) : ∀ (a : Word),
    2 ^ 63 ≤ (rest.foldl (· ||| ·) a).toNat ↔ 2 ^ 63 ≤ a.toNat ∨ ∃ b ∈ rest, 2 ^ 63 ≤ b.toNat := by
  induction rest with
  | nil => intro a; simp
  | cons b rest ih =>
    intro a
    rw [List.foldl_cons, ih, or_big]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_assoc

/-! ## Pushes -/

theorem word_sub_sub (x : Word) (a b : Nat) : x - UInt64.ofNat a - UInt64.ofNat b = x - UInt64.ofNat (a + b) := by
  apply UInt64.toBitVec_inj.mp
  simp [BitVec.sub_sub]

/-- A run of pushes from `rsp = sp`: each register's word below the last,
`rsp` moved past them, nothing else changed. -/
theorem pushes_steps {cs : Checked} {blk : BlockId} :
    ∀ (L : List GPR) {o : Nat} {core : Core} {holes : Holes},
      Straight.Segment cs blk o (L.map Instr.push) → o + L.length < UInt32.size → GPR.rsp ∉ L →
      (∀ x, ¬holes x) → 8 * L.length ≤ (core.readReg .rsp).toNat →
      (∀ x : Word, (core.readReg .rsp).toNat - 8 * L.length ≤ x.toNat → x.toNat < (core.readReg .rsp).toNat →
        core.memory.writable x = true) →
      ∃ core' holes', SafeSteps Runtime.rejecting cs L.length holes (inFrame core blk o []) holes'
          (inFrame core' blk (o + L.length) []) ∧ (∀ x, ¬holes' x) ∧
        core'.readReg .rsp = core.readReg .rsp - UInt64.ofNat (8 * L.length) ∧
        (∀ r, r ≠ .rsp → core'.readReg r = core.readReg r) ∧
        core'.memory.readable = core.memory.readable ∧ core'.memory.writable = core.memory.writable ∧
        (∀ x : Word, ¬((core.readReg .rsp).toNat - 8 * L.length ≤ x.toNat ∧ x.toNat < (core.readReg .rsp).toNat) →
          core'.memory.bytes x = core.memory.bytes x) ∧
        (∀ i r, L[i]? = some r → core'.memory.read64 (core.readReg .rsp - UInt64.ofNat (8 * (i + 1))) = core.readReg r)
  | [], o, core, holes, _, _, _, hempty, _, _ =>
      ⟨core, holes, by simpa using SafeSteps.refl holes (inFrame core blk o []), hempty, by simp, fun _ _ => rfl,
        rfl, rfl, fun _ _ => rfl, by simp⟩
  | r :: L, o, core, holes, seg, fits, hnr, hempty, hroom, hw => by
      simp only [List.mem_cons, not_or] at hnr
      simp only [List.length_cons] at fits hroom hw ⊢
      have hlt : (core.readReg .rsp).toNat < 2 ^ 64 := (core.readReg .rsp).toBitVec.isLt
      have hR8 : (core.readReg .rsp - 8).toNat = (core.readReg .rsp).toNat - 8 := sub8_toNat (by omega)
      have hb8 : ∀ j < 8, (core.readReg .rsp - 8 + UInt64.ofNat j).toNat = (core.readReg .rsp).toNat - 8 + j :=
        fun j hj => by rw [addr_toNat (by rw [hR8]; omega), hR8]
      have hwr := write64?_ok (mem := core.memory) (a := core.readReg .rsp - 8) (v := core.readReg r)
        fun j hj => hw _ (by rw [hb8 j hj]; omega) (by rw [hb8 j hj]; omega)
      let core₁ : Core := { core.setReg .rsp (core.readReg .rsp - 8) with
        memory := core.memory.write64 (core.readReg .rsp - 8) (core.readReg r) }
      have seg' : Straight.Segment cs blk o ([Instr.push r] ++ L.map Instr.push) := by simpa using seg
      obtain ⟨holes₁, one, hempty₁⟩ := bare_step (core := core) (core' := core₁) seg'.left (by omega)
        (fun _ => nofun) (fun _ => nofun) rfl hempty (by rw [executeInstr_push]; simp only [inFrame, hwr]; rfl)
      have hrsp₁ : core₁.readReg .rsp = core.readReg .rsp - 8 := by
        simp [core₁, Core.readReg, Core.setReg]
      obtain ⟨core', holes', rest, hempty', hrsp', hregs', hr', hw', hb', hv'⟩ :=
        pushes_steps L (o := o + 1) (core := core₁) (holes := holes₁) (by simpa using seg'.right) (by omega)
          hnr.2 hempty₁ (by rw [hrsp₁, hR8]; omega)
          (fun x h₁ h₂ => by
            show (core.memory.write64 _ _).writable x = true
            rw [Memory.write64_writable]
            rw [hrsp₁, hR8] at h₁ h₂
            exact hw x (by omega) (by omega))
      refine ⟨core', holes', ?_, hempty', ?_, fun q hq => ?_, ?_, ?_, fun x hx => ?_, fun i q hq => ?_⟩
      · have := one.append rest
        rwa [show o + 1 + L.length = o + (L.length + 1) by omega, show 1 + L.length = L.length + 1 by omega] at this
      · rw [hrsp', hrsp₁, show (8 : Word) = UInt64.ofNat 8 from rfl, word_sub_sub]
        congr 2; omega
      · rw [hregs' q hq]
        simp [core₁, Core.readReg, Core.setReg, Registers.set, hq]
      · rw [hr']; show (core.memory.write64 _ _).readable = _; simp
      · rw [hw']; show (core.memory.write64 _ _).writable = _; simp
      · rw [hb' x (fun ⟨h₁, h₂⟩ => hx ⟨by rw [hrsp₁, hR8] at h₁; omega, by rw [hrsp₁, hR8] at h₂; omega⟩)]
        show (core.memory.write64 _ _).bytes x = _
        exact write64_bytes_off (by rw [hR8]; omega)
          (fun ⟨h₁, h₂⟩ => hx ⟨by rw [hR8] at h₁; omega, by rw [hR8] at h₂; omega⟩)
      · cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
          subst hq
          have e : core.readReg .rsp - UInt64.ofNat (8 * (0 + 1)) = core.readReg .rsp - 8 := rfl
          rw [e]
          have hkeep : core'.memory.read64 (core.readReg .rsp - 8) = core₁.memory.read64 (core.readReg .rsp - 8) :=
            read64_congr fun j hj => hb' _ fun ⟨_, h₂⟩ => by rw [hb8 j hj] at h₂; rw [hrsp₁, hR8] at h₂; omega
          rw [hkeep]
          exact Memory.read64_write64 _ _ _
        | succ i =>
          have := hv' i q (by simpa using hq)
          rw [hrsp₁, show (8 : Word) = UInt64.ofNat 8 from rfl, word_sub_sub] at this
          rw [show 8 * (i + 1 + 1) = 8 + 8 * (i + 1) by omega, this]
          have hq' : q ≠ .rsp := fun e => hnr.2 (e ▸ List.mem_of_getElem? (by simpa using hq))
          simp [core₁, Core.readReg, Core.setReg, Registers.set, hq']

/-! ## The `Nat` check -/

/-- `mov r11, first; or r11, r; …`: `r11` holds the OR of the registers. -/
theorem ors_steps {cs : Checked} {blk : BlockId} :
    ∀ (rest : List GPR) {o : Nat} {core : Core} {holes : Holes},
      Straight.Segment cs blk o (rest.map fun r => .op orMR [.reg .r11, .reg r]) → o + rest.length < UInt32.size →
      GPR.r11 ∉ rest → (∀ x, ¬holes x) →
      ∃ holes', SafeSteps Runtime.rejecting cs rest.length holes (inFrame core blk o []) holes'
          (inFrame (core.setReg .r11 ((rest.map core.readReg).foldl (· ||| ·) (core.readReg .r11))) blk
            (o + rest.length) []) ∧ (∀ x, ¬holes' x)
  | [], o, core, holes, _, _, _, hempty => by
      refine ⟨holes, ?_, hempty⟩
      simpa [setReg_self] using SafeSteps.refl holes (inFrame core blk o [])
  | r :: rest, o, core, holes, seg, fits, h11, hempty => by
      simp only [List.mem_cons, not_or] at h11
      simp only [List.length_cons] at fits ⊢
      have seg' : Straight.Segment cs blk o ([.op orMR [.reg .r11, .reg r]] ++
          rest.map fun r => .op orMR [.reg .r11, .reg r]) := by simpa using seg
      obtain ⟨fl, hex⟩ := orMR_exec .r11 r core
      let core₁ := core.setReg .r11 (core.readReg .r11 ||| core.readReg r)
      obtain ⟨holes₁, one, hempty₁⟩ := bare_step (core := core) (core' := core₁) seg'.left (by omega)
        (fun _ => nofun) (fun _ => nofun) rfl hempty (by
          show (inFrame core blk o []).afterRow (orMR.exec [.reg .r11, .reg r] core {}) = _
          rw [hex]; rfl)
      obtain ⟨holes', rest', hempty'⟩ := ors_steps rest (o := o + 1) (core := core₁) (by simpa using seg'.right)
        (by omega) h11.2 hempty₁
      refine ⟨holes', ?_, hempty'⟩
      have := one.append rest'
      have hc : core₁.setReg .r11 ((rest.map core₁.readReg).foldl (· ||| ·) (core₁.readReg .r11)) =
          core.setReg .r11 (((r :: rest).map core.readReg).foldl (· ||| ·) (core.readReg .r11)) := by
        have hm : rest.map core₁.readReg = rest.map core.readReg := by
          apply List.map_congr_left; intro q hq
          have : q ≠ .r11 := fun e => h11.2 (e ▸ hq)
          simp only [core₁, Validate.readReg_setReg, if_neg this]
        have h1 : core₁.readReg .r11 = core.readReg .r11 ||| core.readReg r := by
          simp only [core₁, Validate.readReg_setReg, if_pos]
        rw [hm, h1]
        simp [core₁, Core.setReg, Registers.set_set]
      rw [hc] at this
      rwa [show o + 1 + rest.length = o + (rest.length + 1) by omega, show 1 + rest.length = rest.length + 1 by omega]
        at this

/-! ## Marshalling the arguments -/

/-- An argument as the internal convention passes it: a `Nat` tagged
`2n+1`, a word as is. -/
def tagged : ArgRep → Word → Word
  | .nat, w => w + w + 1
  | .word, w => w

/-- The instruction moving one argument from its SysV register to its
internal one (`wrapper`'s marshalling). -/
def marshalOne (p : (GPR × GPR) × ArgRep) : Except String Instr :=
  match p.2 with
  | .nat => tagInto p.1.2 p.1.1
  | .word => pure (X86.Instr.mov .w64 p.1.2 (.reg p.1.1))

theorem marshalOne_exec {p : (GPR × GPR) × ArgRep} {ins : Instr} (h : marshalOne p = .ok ins) :
    (∀ t, ins ≠ .call t) ∧ (∀ i, ins ≠ .callRuntime i) ∧ ins.single = true ∧
      ∀ (runtime : Runtime) (cs : Checked) (m : Machine),
        executeInstr runtime cs ins m = m.advanceWith (m.core.setReg p.1.2 (tagged p.2 (m.core.readReg p.1.1))) := by
  obtain ⟨⟨src, dst⟩, rep⟩ := p
  cases rep with
  | nat =>
    simp only [marshalOne, tagInto] at h
    cases hi : indexReg src with
    | none => simp [hi, throw, throwThe, MonadExceptOf.throw] at h
    | some index =>
      simp only [hi, pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨fun _ => nofun, fun _ => nofun, rfl, fun runtime cs m => ?_⟩
      rw [executeInstr_lea]
      simp [MemAddr.eval, indexReg_gpr hi, Scale.word, tagged, signExtend32]
  | word =>
    simp only [marshalOne, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨fun _ => nofun, fun _ => nofun, rfl, fun runtime cs m => ?_⟩
    rw [executeInstr_mov]
    rfl

/-- The marshalling moves, one checked step each: each destination gets its
tagged source (read before any earlier move overwrote it, and not
overwritten later), and nothing else changes. -/
theorem marshal_steps {cs : Checked} {blk : BlockId} :
    ∀ (P : List ((GPR × GPR) × ArgRep)) (ins : List Instr) {o : Nat} {core : Core} {holes : Holes},
      P.mapM marshalOne = .ok ins → Straight.Segment cs blk o ins → o + ins.length < UInt32.size →
      (∀ x, ¬holes x) →
      ∃ core' holes', SafeSteps Runtime.rejecting cs ins.length holes (inFrame core blk o []) holes'
          (inFrame core' blk (o + ins.length) []) ∧ (∀ x, ¬holes' x) ∧ core'.memory = core.memory ∧
        (∀ r, r ∉ P.map (·.1.2) → core'.readReg r = core.readReg r) ∧
        ∀ (i : Nat) (p : (GPR × GPR) × ArgRep), P[i]? = some p →
          (∀ (j : Nat) (q : (GPR × GPR) × ArgRep), j < i → P[j]? = some q → q.1.2 ≠ p.1.1) →
          (∀ (j : Nat) (q : (GPR × GPR) × ArgRep), i < j → P[j]? = some q → q.1.2 ≠ p.1.2) →
          core'.readReg p.1.2 = tagged p.2 (core.readReg p.1.1)
  | [], ins, o, core, holes, h, _, _, hempty => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨core, holes, by simpa using SafeSteps.refl holes (inFrame core blk o []), hempty, rfl, fun _ _ => rfl,
        fun i p hp => by simp at hp⟩
  | p :: P, ins, o, core, holes, h, seg, fits, hempty => by
      obtain ⟨i₀, ins', h₀, h', rfl⟩ : ∃ i₀ ins', marshalOne p = .ok i₀ ∧ P.mapM marshalOne = .ok ins' ∧
          ins = i₀ :: ins' := by
        simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
        split at h
        · cases h
        · rename_i i₀ h₀
          split at h
          · cases h
          · rename_i ins' h'
            simp only [Except.ok.injEq] at h
            exact ⟨i₀, ins', h₀, h', h.symm⟩
      obtain ⟨hp, hr, hs, hex⟩ := marshalOne_exec h₀
      simp only [List.length_cons] at fits ⊢
      have seg' : Straight.Segment cs blk o ([i₀] ++ ins') := by simpa using seg
      let core₁ := core.setReg p.1.2 (tagged p.2 (core.readReg p.1.1))
      obtain ⟨holes₁, one, hempty₁⟩ := bare_step (core := core) (core' := core₁) seg'.left (by omega) hp hr hs
        hempty (hex _ _ _)
      obtain ⟨core', holes', rest, hempty', hmem', hkeep', hval'⟩ := marshal_steps P ins' (o := o + 1)
        (core := core₁) h' (by simpa using seg'.right) (by omega) hempty₁
      refine ⟨core', holes', ?_, hempty', by rw [hmem']; rfl, fun r hr' => ?_, fun i q hq hbefore hafter => ?_⟩
      · have := one.append rest
        rwa [show o + 1 + ins'.length = o + (ins'.length + 1) by omega,
          show 1 + ins'.length = ins'.length + 1 by omega] at this
      · simp only [List.map_cons, List.mem_cons, not_or] at hr'
        rw [hkeep' r hr'.2]
        simp [core₁, Core.readReg, Core.setReg, Registers.set, hr'.1]
      · cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
          cases hq
          have hnot : p.1.2 ∉ P.map (·.1.2) := by
            intro hm
            obtain ⟨q', hq', e⟩ := List.mem_map.1 hm
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hq'
            exact hafter (j + 1) q' (by omega) (by simpa using hj) e
          rw [hkeep' _ hnot]
          simp [core₁, Core.readReg, Core.setReg, Registers.set]
        | succ i =>
          have hq' : P[i]? = some q := by simpa using hq
          rw [hval' i q hq' (fun j q' hj hq'' => hbefore (j + 1) q' (by omega) (by simpa using hq''))
            (fun j q' hj hq'' => hafter (j + 1) q' (by omega) (by simpa using hq''))]
          have hne : p.1.2 ≠ q.1.1 := hbefore 0 p (by omega) rfl
          simp [core₁, Core.readReg, Core.setReg, Registers.set, Ne.symm hne]

/-! ## The wrapper's code -/

/-- The wrapper's head: the pushes, `sub rsp, 8`, the context register,
`entrySp` and `stackLimit`. -/
def wrapperHead : List Instr :=
  wrapperSaves.map X86.Instr.push ++
    [subRsp 8, X86.Instr.lea .r15 { base := some .rdi, displacement := 64 },
      X86.Instr.store .w64 entrySpCell .rsp, X86.Instr.mov .w64 .r11 (.reg .rsp),
      .op subRM [.reg .r11, .mem stackBudgetCell], X86.Instr.store .w64 stackLimitCell .r11]

/-- Each argument's SysV register, internal register and passing. -/
def argPairs (reps : List ArgRep) : List ((GPR × GPR) × ArgRep) := (sysvArgs.zip Lir.Conv.argRegs).zip reps

/-- The SysV registers of the `Nat` arguments. -/
def natSrcs (reps : List ArgRep) : List GPR :=
  (argPairs reps).filterMap fun ((src, _), rep) => if rep == .nat then some src else none

/-- The `Nat` check: the OR of the `Nat` arguments into `r11`. -/
def natCheck (first : GPR) (rest : List GPR) : List Instr :=
  X86.Instr.mov .w64 .r11 (.reg first) :: rest.map fun r => .op orMR [.reg .r11, .reg r]

/-- What `wrapper` emits: the head, then the call directly (no `Nat`
argument), or the `Nat` check and a branch to `fail₃`, then the call in a
second block; the call's code is the marshalling, the call and the tail. -/
theorem wrapper_ok {entry fail₃ : BlockId} {reps : List ArgRep} {start : Nat} {blks : List X86.Block}
    (h : wrapper entry fail₃ reps start = .ok blks) :
    reps.length ≤ sysvArgs.length ∧ ∃ marshal, (argPairs reps).mapM marshalOne = .ok marshal ∧
      ((natSrcs reps = [] ∧
          blks = [{ instructions := (wrapperHead ++ (marshal ++ [Instr.call entry]) ++ wrapperTail).toArray,
                    terminator := .ret }]) ∨
        ∃ first rest, natSrcs reps = first :: rest ∧
          blks = [{ instructions := (wrapperHead ++ natCheck first rest).toArray,
                    terminator := .branch testMR [.reg .r11, .reg .r11] .signedLt fail₃ (UInt32.ofNat (start + 1)) },
                  { instructions := ((marshal ++ [Instr.call entry]) ++ wrapperTail).toArray, terminator := .ret }]) := by
  unfold wrapper at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i hlen
    split at h
    · cases h
    · rename_i marshal hm
      have hm' : (argPairs reps).mapM marshalOne = .ok marshal := by
        have e : (fun (x : (GPR × GPR) × ArgRep) => match x with
            | ((src, dst), rep) => match rep with
              | .nat => tagInto dst src
              | .word => (pure (X86.Instr.mov .w64 dst (.reg src)) : Except String Instr)) = marshalOne := by
          funext x; obtain ⟨⟨s, d⟩, r⟩ := x; cases r <;> rfl
        rw [argPairs, ← e]; exact hm
      refine ⟨by simpa using hlen, marshal, hm', ?_⟩
      split at h
      · rename_i hnil
        simp only [Except.ok.injEq] at h
        subst h
        left
        refine ⟨hnil, ?_⟩
        simp only [List.cons.injEq, and_true]
        simp [wrapperHead, wrapperTail]
      · rename_i first rest hcons
        simp only [Except.ok.injEq] at h
        subst h
        right
        refine ⟨first, rest, hcons, ?_⟩
        simp [wrapperHead, natCheck, wrapperTail]
  · cases h

end IxCC.Xv.Stacking.Proof
