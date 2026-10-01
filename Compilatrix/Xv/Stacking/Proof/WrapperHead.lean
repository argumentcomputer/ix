import Compilatrix.Xv.Stacking.Proof.WrapperProof

/-!
# The export wrapper's head

`wrapper_head`: from the export's entry, the wrapper's twelve head
instructions are checked steps that push the caller's callee-saved
registers, set `rsp` to `entrySp`, load the context register, and store
`entrySp` and `stackLimit` in the context: afterwards the words above
`entrySp` are the caller's registers and return address (`saveWord`), and
memory is otherwise the caller's outside the pushed words and the two
context cells.
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86 Compilatrix.X86.Stream

theorem word_add_ne {a : Word} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (h : i ≠ j) :
    a + UInt64.ofNat i ≠ a + UInt64.ofNat j := by
  intro e
  have e' : UInt64.ofNat i = UInt64.ofNat j := by simpa using congrArg (fun x => x - a) e
  have := congrArg UInt64.toNat e'
  rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega),
    UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)] at this
  exact h this

theorem saves_popOrder : ∀ i < 6, wrapperSaves[5 - i]? = popOrder[i]? := by decide

theorem ctx_48 (ctx : Word) : ctx - 48 = ctx - 64 + UInt64.ofNat 16 := by
  rw [UInt64.sub_eq_add_neg, UInt64.sub_eq_add_neg, UInt64.add_assoc]
  congr 1

theorem store_exec {core : Core} {m : MemAddr} {r : GPR} {a : Word} (ha : m.eval core = a)
    (hw : ∀ i < 8, core.memory.writable (a + UInt64.ofNat i) = true) (runtime : Runtime) (cs : Checked)
    (mc : Machine) (hmc : mc.core = core) :
    executeInstr runtime cs (Instr.store .w64 m r) mc =
      mc.advanceWith { core with memory := core.memory.write64 a (core.readReg r) } := by
  rw [executeInstr_store, hmc, ha]
  have h := (rangeAllowed_iff core.memory.writable a 8).2 hw
  simp [Core.storeReg?, Memory.write?, w64_bytes, h, bind, Except.bind, pure, Except.pure, Memory.write64]


/-- From the export's entry, the wrapper's head. -/
theorem wrapper_head {cs : Checked} {blk : BlockId} (seg : Straight.Segment cs blk 0 wrapperHead)
    {core₀ : Core} {retAddr : Word} {mem : Memory} {ctx : Word} (base : EntryBase core₀ retAddr mem ctx) :
    ∃ core₁ holes, SafeSteps Runtime.rejecting cs 12 (fun _ => False) (inFrame core₀ blk 0 []) holes
        (inFrame core₁ blk 12 []) ∧ (∀ x, ¬holes x) ∧
      core₁.readReg .rsp = entrySpOf core₀ ∧ core₁.readReg .r15 = ctx ∧
      (∀ r, r ≠ .rsp → r ≠ .r15 → r ≠ .r11 → core₁.readReg r = core₀.readReg r) ∧
      core₁.memory.readable = core₀.memory.readable ∧ core₁.memory.writable = core₀.memory.writable ∧
      (∀ x, ¬InEntryStack core₀ ctx x → (∀ i < 16, x ≠ ctx - 64 + UInt64.ofNat i) →
        core₁.memory.bytes x = core₀.memory.bytes x) ∧
      core₁.memory.read64? (ctx - 64) = .ok (entrySpOf core₀) ∧
      core₁.memory.read64 (ctx - 56) = limitOf core₀ ctx ∧
      (∀ i < 7, core₁.memory.read64? (entrySpOf core₀ + UInt64.ofNat (8 + 8 * i)) = .ok (saveWord core₀ retAddr i)) := by
  have hlo := base.low
  have htop := base.top
  have hS : (core₀.readReg .rsp).toNat < 2 ^ 64 := (core₀.readReg .rsp).toBitVec.isLt
  have hE := base.entrySp_toNat
  have hctx8 : ∀ j < 8, ctx - 56 + UInt64.ofNat j = ctx - 64 + UInt64.ofNat (8 + j) := by
    intro j _; rw [ctx_56, UInt64.add_assoc, ← UInt64.ofNat_add]
  -- The head's pieces
  have hhead : wrapperHead = wrapperSaves.map Instr.push ++ ([subRsp 8] ++
      ([Instr.lea .r15 { base := some .rdi, displacement := 64 }] ++ ([Instr.store .w64 entrySpCell .rsp] ++
      ([Instr.mov .w64 .r11 (.reg .rsp)] ++ ([.op subRM [.reg .r11, .mem stackBudgetCell]] ++
      [Instr.store .w64 stackLimitCell .r11]))))) := rfl
  rw [hhead] at seg
  have hlen6 : (wrapperSaves.map Instr.push).length = 6 := rfl
  -- The pushes
  obtain ⟨c6, h6, s6, he6, hr6, hg6, hrd6, hwr6, hb6, hv6⟩ := pushes_steps (o := 0) (core := core₀)
    (holes := fun _ => False) wrapperSaves seg.left (by decide) (by decide) (fun _ h => h)
    (by simp only [wrapperSaves, List.length_cons, List.length_nil]; omega)
    (fun x h₁ h₂ => (base.stack x ⟨by simp only [wrapperSaves, List.length_cons, List.length_nil] at h₁; omega,
      by omega⟩).2.1)
  have seg6 := seg.right
  rw [hlen6] at seg6
  have hlenS : wrapperSaves.length = 6 := rfl
  rw [hlenS] at s6 hr6 hb6
  have hrsp6 : (c6.readReg .rsp).toNat = (core₀.readReg .rsp).toNat - 48 := by
    rw [hr6, sub_ofNat_toNat (by omega)]
  -- `sub rsp, 8`
  obtain ⟨c7, hc7⟩ : ∃ c, c = c6.setReg .rsp (c6.readReg .rsp - UInt64.ofNat 8) := ⟨_, rfl⟩
  obtain ⟨h7, s7, he7⟩ := bare_step (core := c6) (core' := c7) seg6.left (by decide)
    (fun _ => by simp [subRsp, Instr.ofRow, aluImmRow]) (fun _ => by simp [subRsp, Instr.ofRow, aluImmRow])
    (by simp [subRsp, Instr.ofRow, aluImmRow]; split <;> rfl) he6 (by rw [hc7]; exact exec_subRsp (by decide) _ _ _)
  have seg7 := seg6.right
  have r7 : ∀ r, c7.readReg r = if r = .rsp then c6.readReg .rsp - UInt64.ofNat 8 else c6.readReg r := by
    intro r; rw [hc7, Validate.readReg_setReg]
  have m7 : c7.memory = c6.memory := by rw [hc7]; rfl
  -- `lea r15, [rdi + 64]`
  obtain ⟨c8, hc8⟩ : ∃ c, c = c7.setReg .r15 ((({ base := some .rdi, displacement := 64 } : MemAddr)).eval c7) :=
    ⟨_, rfl⟩
  obtain ⟨h8, s8, he8⟩ := bare_step (core := c7) (core' := c8) seg7.left (by decide) (fun _ => nofun)
    (fun _ => nofun) rfl he7 (by rw [executeInstr_lea, hc8]; rfl)
  have seg8 := seg7.right
  have r8 : ∀ r, r ≠ .r15 → c8.readReg r = c7.readReg r := by
    intro r hr; rw [hc8, Validate.readReg_setReg, if_neg hr]
  have m8 : c8.memory = c6.memory := by rw [hc8, ← m7]; rfl
  have hrsp8 : c8.readReg .rsp = entrySpOf core₀ := by
    rw [r8 _ (by decide), r7, if_pos rfl]
    apply word_eq
    rw [sub_ofNat_toNat (by rw [hrsp6]; omega), hrsp6, hE]
    omega
  have h15₈ : c8.readReg .r15 = ctx := by
    rw [hc8, Validate.readReg_setReg, if_pos rfl]
    simp only [MemAddr.eval]
    rw [r7, if_neg (by decide), hg6 _ (by decide), base.rdi]
    simp [signExtend32]
  -- `mov [r15 − 64], rsp`
  have hctxW : ∀ i < 16, c8.memory.writable (ctx - 64 + UInt64.ofNat i) = true := fun i hi => by
    rw [m8, hwr6]; exact (base.ctxCells i hi).2.1
  have hev9 : entrySpCell.eval c8 = ctx - 64 := by rw [entrySpCell_eval, h15₈]
  obtain ⟨c9, hc9⟩ : ∃ c : Core, c = { c8 with memory := c8.memory.write64 (ctx - 64) (c8.readReg .rsp) } :=
    ⟨_, rfl⟩
  obtain ⟨h9, s9, he9⟩ := bare_step (core := c8) (core' := c9) seg8.left (by decide) (fun _ => nofun)
    (fun _ => nofun) rfl he8 (by rw [hc9]; exact store_exec hev9 (fun i hi => hctxW i (by omega)) _ _ _ rfl)
  have seg9 := seg8.right
  have r9 : ∀ r, c9.readReg r = c8.readReg r := fun r => by rw [hc9]; rfl
  have m9 : c9.memory = c6.memory.write64 (ctx - 64) (entrySpOf core₀) := by rw [hc9, hrsp8, m8]
  -- `mov r11, rsp`
  obtain ⟨c10, hc10⟩ : ∃ c, c = c9.setReg .r11 (c9.readReg .rsp) := ⟨_, rfl⟩
  obtain ⟨h10, s10, he10⟩ := bare_step (core := c9) (core' := c10) seg9.left (by decide) (fun _ => nofun)
    (fun _ => nofun) rfl he9 (by rw [executeInstr_mov, hc10]; rfl)
  have seg10 := seg9.right
  have r10 : ∀ r, r ≠ .r11 → c10.readReg r = c9.readReg r := by
    intro r hr; rw [hc10, Validate.readReg_setReg, if_neg hr]
  have m10 : c10.memory = c6.memory.write64 (ctx - 64) (entrySpOf core₀) := by rw [hc10, ← m9]; rfl
  have h11₁₀ : c10.readReg .r11 = entrySpOf core₀ := by
    rw [hc10, Validate.readReg_setReg, if_pos rfl, r9, hrsp8]
  -- `sub r11, [r15 − 48]`
  have h15₁₀ : c10.readReg .r15 = ctx := by rw [r10 _ (by decide), r9, h15₈]
  have hbudgetB : ∀ i < 8, c10.memory.bytes (ctx - 48 + UInt64.ofNat i) =
      core₀.memory.bytes (ctx - 48 + UInt64.ofNat i) := by
    intro i hi
    rw [m10, Memory.write64_bytes_outside _ _ _ _ fun j hj => by
      rw [ctx_48, UInt64.add_assoc, ← UInt64.ofNat_add]
      exact word_add_ne (by omega) (by omega) (by omega)]
    exact hb6 _ fun ⟨h₁, h₂⟩ => (base.budgetCell i hi).2 ⟨by omega, by omega⟩
  have hbudget : c10.memory.read? .w64 (stackBudgetCell.eval c10) = .ok (budgetOf core₀ ctx) := by
    rw [stackBudgetCell_eval, h15₁₀]
    rw [read?_ok fun i hi => by
      rw [m10, Memory.write64_readable, hrd6]; exact (base.budgetCell i hi).1]
    exact congrArg Except.ok (read64_congr hbudgetB)
  obtain ⟨fl, hsub⟩ := subRM_exec .r11 stackBudgetCell c10 hbudget
  obtain ⟨c11, hc11⟩ : ∃ c, c = c10.setReg .r11 (c10.readReg .r11 - budgetOf core₀ ctx) := ⟨_, rfl⟩
  obtain ⟨h11, s11, he11⟩ := bare_step (core := c10) (core' := c11) seg10.left (by decide) (fun _ => nofun)
    (fun _ => nofun) rfl he10 (by
      show (inFrame c10 blk _ []).afterRow (subRM.exec [.reg .r11, .mem stackBudgetCell] c10 {}) = _
      rw [hsub, hc11]; rfl)
  have seg11 := seg10.right
  have r11 : ∀ r, r ≠ .r11 → c11.readReg r = c10.readReg r := by
    intro r hr; rw [hc11, Validate.readReg_setReg, if_neg hr]
  have m11 : c11.memory = c6.memory.write64 (ctx - 64) (entrySpOf core₀) := by rw [hc11, ← m10]; rfl
  have h11₁₁ : c11.readReg .r11 = limitOf core₀ ctx := by
    rw [hc11, Validate.readReg_setReg, if_pos rfl, h11₁₀]; rfl
  -- `mov [r15 − 56], r11`
  have h15₁₁ : c11.readReg .r15 = ctx := by rw [r11 _ (by decide), h15₁₀]
  have hev12 : stackLimitCell.eval c11 = ctx - 56 := by rw [stackLimitCell_eval, h15₁₁]
  obtain ⟨c12, hc12⟩ : ∃ c : Core, c = { c11 with memory := c11.memory.write64 (ctx - 56) (c11.readReg .r11) } :=
    ⟨_, rfl⟩
  obtain ⟨h12, s12, he12⟩ := bare_step (core := c11) (core' := c12) seg11 (by decide) (fun _ => nofun)
    (fun _ => nofun) rfl he11 (by
      rw [hc12]
      exact store_exec hev12 (fun i hi => by
        rw [hctx8 i hi, m11, Memory.write64_writable, ← m8]; exact hctxW (8 + i) (by omega)) _ _ _ rfl)
  have r12 : ∀ r, c12.readReg r = c11.readReg r := fun r => by rw [hc12]; rfl
  have hmem12 : c12.memory = (c6.memory.write64 (ctx - 64) (entrySpOf core₀)).write64 (ctx - 56) (limitOf core₀ ctx) := by
    rw [hc12, h11₁₁, m11]
  refine ⟨c12, h12, ?_, he12, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, fun x hx hc => ?_, ?_, ?_, fun i hi => ?_⟩
  · have := (((((s6.append s7).append s8).append s9).append s10).append s11).append s12
    simpa using this
  · rw [r12, r11 _ (by decide), r10 _ (by decide), r9, hrsp8]
  · rw [r12, h15₁₁]
  · rw [r12, r11 _ h3, r10 _ h3, r9, r8 _ h2, r7, if_neg h1, hg6 r h1]
  · rw [hmem12]; simp [hrd6]
  · rw [hmem12]; simp [hwr6]
  · rw [hmem12, Memory.write64_bytes_outside _ _ _ _ fun j hj e => hc (8 + j) (by omega) (by rw [e, hctx8 j hj]),
      Memory.write64_bytes_outside _ _ _ _ fun j hj e => hc j (by omega) e]
    exact hb6 x fun ⟨h₁, h₂⟩ => hx ⟨by omega, by omega⟩
  · rw [read64?_keep (mem := (c6.memory.write64 (ctx - 64) (entrySpOf core₀))) (by rw [hmem12]; simp)
      fun j hj => by
        rw [hmem12, Memory.write64_bytes_outside _ _ _ _ fun k hk => by
          rw [hctx8 k hk]; exact word_add_ne (by omega) (by omega) (by omega)]]
    rw [Memory.read64?, read?_ok fun i hi => by rw [Memory.write64_readable, hrd6]; exact (base.ctxCells i (by omega)).1]
    exact congrArg _ (Memory.read64_write64 _ _ _)
  · rw [hmem12]; exact Memory.read64_write64 _ _ _
  · -- The saves above `entrySp`
    have hstackA : ∀ j < 8, InEntryStack core₀ ctx (entrySpOf core₀ + UInt64.ofNat (8 + 8 * i) + UInt64.ofNat j) := by
      intro j hj
      simp only [InEntryStack]
      rw [addr_toNat (by rw [addr_toNat (by omega)]; omega), addr_toNat (by omega), hE]
      omega
    have hkeep12 : ∀ j < 8, c12.memory.bytes (entrySpOf core₀ + UInt64.ofNat (8 + 8 * i) + UInt64.ofNat j) =
        c6.memory.bytes (entrySpOf core₀ + UInt64.ofNat (8 + 8 * i) + UInt64.ofNat j) := by
      intro j hj
      rw [hmem12, Memory.write64_bytes_outside _ _ _ _ fun k hk e => (base.ctxCells (8 + k) (by omega)).2.2.2.2
          (by rw [← hctx8 k hk, ← e]; exact hstackA j hj),
        Memory.write64_bytes_outside _ _ _ _ fun k hk e => (base.ctxCells k (by omega)).2.2.2.2
          (by rw [← e]; exact hstackA j hj)]
    have hrdA : ∀ j < 8, c12.memory.readable (entrySpOf core₀ + UInt64.ofNat (8 + 8 * i) + UInt64.ofNat j) = true := by
      intro j hj; rw [hmem12]; simp only [Memory.write64_readable]; rw [hrd6]; exact (base.stack _ (hstackA j hj)).1
    rw [Memory.read64?, read?_ok hrdA]
    refine congrArg Except.ok ?_
    rw [read64_congr hkeep12]
    by_cases h6 : i = 6
    · subst h6
      have e : entrySpOf core₀ + UInt64.ofNat (8 + 8 * 6) = core₀.readReg .rsp := by simp [entrySpOf]
      rw [e, read64_congr (m := core₀.memory) fun j hj => hb6 _ fun ⟨_, h₂⟩ => by
        rw [addr_toNat (by omega)] at h₂; omega]
      have := base.slot
      rw [Memory.read64?, read?_ok fun j hj => (base.stack _ ⟨by rw [addr_toNat (by omega)]; omega,
        by rw [addr_toNat (by omega)]; omega⟩).1] at this
      simpa [saveWord, popOrder] using Except.ok.inj this
    · have hi6 : i < 6 := by omega
      have e : entrySpOf core₀ + UInt64.ofNat (8 + 8 * i) = core₀.readReg .rsp - UInt64.ofNat (8 * ((5 - i) + 1)) := by
        apply word_eq
        rw [addr_toNat (by omega), hE, sub_ofNat_toNat (by omega)]
        omega
      obtain ⟨r, hr⟩ : ∃ r, popOrder[i]? = some r := ⟨_, List.getElem?_eq_getElem (by simp [popOrder]; omega)⟩
      have hws : wrapperSaves[5 - i]? = some r := by rw [← hr]; exact saves_popOrder i hi6
      rw [e, hv6 (5 - i) r hws]
      simp [saveWord, hr]

end Compilatrix.Xv.Stacking.Proof
