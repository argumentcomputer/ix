import IxCC.X86.Exe.Machine.Proof.Blocks

/-!
# The two calls of an iteration (X0-P, third part)

Each iteration of the shell calls `cx_init` from the `loop` block and the
step from the `callStep` block. The model of the two calls is
`X86.LinkedAt`: `cx_init` under a driver, the step from a site of its own.
This module builds both from the process and proves that the shell's code
between the two calls realises the second:

- `initDriverOf L ce s₀`: `cx_init`'s driver at an iteration, from the
  process at its call site (its bytes, flags and registers; the layout's
  region, budget and stack pointer; the return address after the `loop`
  block's export call). `initDriver_ok`: it keeps the contract.
- `stepSite L ce s₀`: the step's site (the address after `callStep`'s export
  call, the flags `test 0, 0` leaves, `cx_init`'s registers with `rax` zero
  and `r10`, `r11` the call top). It is fixed before `cx_init` returns.
- `glue_at` (and `glue`, the site left existential): from every return of
  `cx_init` with status 0, the shell's next 18 instructions (the rest of
  `loop`, `initBack`, `callStep` up to its call) reach the step's call in the
  state the step's driver at `stepSite` gives it, or fault.
- `iteration_calls_at` (and `iteration_calls`): the call lemma's `two_calls`
  with `glue_at`, `file_text` and `initDriver_ok`: the session model's call on
  the state and event, lifted to the process.

The numbers come from the layout the file was checked for
(`Machine.fileFacts`) and the contract the writer established at its calls
(`CertifiedFor.contract`).
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

open IxCC.Sem (Result Obs Lang)
open IxCC.X86.Encode (instructionOperation)
open IxCC.X86.Exe.Shell (blockOffset instrOffset)

/-- The word at `a` of a byte function. -/
def wordOf (bytes : Word → UInt8) (a : Word) : Word := (⟨bytes, fun _ => true, fun _ => true⟩ : Memory).read64 a

/-- Instructions from `cx_init`'s return to the step's call: the rest of `loop`
(`mov r11`, `cmp`, `jne`, `jmp`), `initBack` (two moves, `test`, `jne`, `jmp`)
and `callStep`'s nine instructions before the call. -/
def glueSteps : Nat := 18

theorem run_one {image : ByteArray} {s s' : ByteEval.State} (h : ByteEval.step image fetchBase s = .ok s') :
    ByteEval.run image fetchBase 1 s = .ok s' := by
  rw [run_succ h]; rfl

theorem read64?_value {m : Memory} {a v : Word} (h : m.read64? a = .ok v) : v = m.read64 a := by
  unfold Memory.read64? Memory.read? at h
  split at h
  · cases h; rfl
  · cases h

section
variable {L : Machine.Layout} {step : String} {object : ByteArray}

/-- `cx_init`'s driver at an iteration, from the process at its call site: the return address
is the instruction after the `loop` block's export call (its twelfth). -/
def initDriverOf (L : Machine.Layout) (ce : Machine.Certified L step object) (s₀ : ByteEval.State) : Driver :=
  { L.driverWith ce.checked.plan.placement.textOffset (shellAddr L step ce.checked Machine.B.loop 12)
      s₀.core.memory.bytes with
    flags := s₀.flags, other := s₀.core.registers }

/-- The step's call site at an iteration (see the module note). -/
def stepSite (L : Machine.Layout) (ce : Machine.Certified L step object) (s₀ : ByteEval.State) : Driver.Site :=
  ⟨UInt64.ofNat (shellAddr L step ce.checked Machine.B.callStep 10), ByteEval.aluFlags .and .w64 0 0,
    ((s₀.core.registers.set .rax 0).set .r10 (UInt64.ofNat L.callTop)).set .r11 (UInt64.ofNat L.callTop)⟩

/-- **The layout's numbers** a checked machine executable keeps. -/
theorem layout_numbers (ce : Machine.Certified L step object) :
    256 ≤ L.stackArea ∧ dataBase + L.stackArea + 0x1000 + L.region ≤ 2 ^ 47 ∧
      L.callTop = dataBase + L.stackArea - 256 ∧ L.shellTop = dataBase + L.stackArea ∧
      L.regionStart = dataBase + L.stackArea + 0x1000 := by
  have ff := Machine.fileFacts ce.checked
  have h1 := le_alignUp (L.stack + Machine.scratch) 0x1000 (by decide)
  have h2 := le_alignUp L.region 0x1000 (by decide)
  have h3 := ff.regionEnd
  have e1 : L.stackArea = alignUp (L.stack + Machine.scratch) 0x1000 := rfl
  have e2 : L.regionStart = dataBase + L.stackArea + 0x1000 := rfl
  have hs : Machine.scratch = 256 := rfl
  refine ⟨by omega, by omega, rfl, rfl, rfl⟩

theorem toNat_small {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' (by show n < 18446744073709551616; omega)

/-- The stack pointer of a call, one word up, is the call top. -/
theorem sp_add8 (ce : Machine.Certified L step object) (ret : Nat) (init : Word → UInt8) :
    (L.driverWith ce.checked.plan.placement.textOffset ret init).sp + 8 = UInt64.ofNat L.callTop := by
  obtain ⟨h1, -, h3, -, -⟩ := layout_numbers ce
  have h8 : 8 ≤ L.callTop := by
    have hd : dataBase = 268435456 := rfl
    rw [h3, hd]
    omega
  show UInt64.ofNat (L.callTop - 8) + UInt64.ofNat 8 = UInt64.ofNat L.callTop
  rw [← UInt64.ofNat_add, Nat.sub_add_cancel h8]

/-- **The shell's 256 bytes lie outside every call's mapping.** -/
theorem scratch_unmapped (ce : Machine.Certified L step object) (ret : Nat) (init : Word → UInt8) {i : Nat}
    (hi : i < 256) :
    (L.driverWith ce.checked.plan.placement.textOffset ret init).mapped
      (UInt64.ofNat L.callTop + UInt64.ofNat i) = false := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := layout_numbers ce
  have hd : dataBase = 268435456 := rfl
  have ha : (UInt64.ofNat L.callTop + UInt64.ofNat i).toNat = L.callTop + i := by
    rw [← UInt64.ofNat_add, toNat_small (by omega)]
  simp only [Driver.mapped, Driver.inRegion, Driver.inStack, Machine.Layout.driverWith, ha,
    Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  rw [toNat_small (show L.regionStart < 2 ^ 64 by omega), toNat_small (show L.region < 2 ^ 64 by omega),
    toNat_small (show L.callTop - 8 < 2 ^ 64 by omega)]
  omega

/-- **The contract at any return address in the shell**, from the writer's contract at its calls
(every clause but the return address's is the layout's) and the placement (the shell lies after the
object's text). -/
theorem driver_ok_at (ce : Machine.Certified L step object) (init : Word → UInt8) {ret : Nat}
    (hlo : fileBase + ce.checked.plan.placement.shellOffset ≤ ret) (hhi : ret < 2 ^ 64) :
    (L.driverWith ce.checked.plan.placement.textOffset ret init).Ok ce.checked.plan.placement.textSize := by
  obtain ⟨parts, -, hplan, hf⟩ := ce.checked.valid
  have hcalls := hf.calls
  obtain ⟨c, rest, hc⟩ : ∃ c rest, ce.checked.plan.calls = c :: rest := by
    cases h : ce.checked.plan.calls with
    | nil => rw [h] at hcalls; simp [Machine.frame] at hcalls
    | cons c rest => exact ⟨c, rest, rfl⟩
  have hk := (ce.contract c (by rw [hc]; exact List.mem_cons_self) init).toOk
  have ff := Machine.fileFacts ce.checked
  have hd : dataBase = 268435456 := rfl
  have hfs : ce.checked.plan.placement.fileSize =
      ce.checked.plan.placement.shellOffset + ce.checked.plan.placement.shellSize := rfl
  have hsize := ff.size
  have hbelow := ff.below
  have hte := ff.textEnd
  have hde := ff.dataEnd
  refine ⟨hk.aligned, hk.minSize, hk.below, hk.spAlign, hk.spTop, hk.budgetMin, hk.spLow, hk.apart, ?_⟩
  show ce.checked.plan.placement.textSize ≤
    (UInt64.ofNat ret - UInt64.ofNat (fileBase + ce.checked.plan.placement.textOffset)).toNat
  have h1 : (UInt64.ofNat ret).toNat = ret := toNat_small hhi
  have h2 : (UInt64.ofNat (fileBase + ce.checked.plan.placement.textOffset)).toNat =
      fileBase + ce.checked.plan.placement.textOffset := toNat_small (by omega)
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h1, h2]; omega), h1, h2]
  omega

/-- A linear instruction of the shell is inside the file. -/
theorem shellAddr_in (ce : Machine.Certified L step object) {b j : Nat} (hb : b < 46) {i : X86.Instr}
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some (.instr i)) (hnc : ∀ t, i ≠ .call t) :
    shellAddr L step ce.checked b j < fileBase + ce.checked.bytes.size := by
  have hm := (shell_valid ce).instr b _ (shell_get ce.checked hb) j _ hi
  have hm' : Stream.decodes ce.checked.bytes
      (ce.checked.plan.placement.shellOffset + blockOffset (shellOf ce.checked) b +
        instrOffset (blockAt (shellOf ce.checked) b) j) (instructionOperation i) (Shell.Instr.size (.instr i)) = true := by
    cases i with
    | call t => exact absurd rfl (hnc t)
    | _ => simp only [Shell.instrMatches, Bool.and_eq_true] at hm; exact hm.2
  have := decodeAt_lt (decodes_some hm')
  unfold shellAddr
  omega

/-- The shell's addresses are below the zero-filled segments. -/
theorem shellAddr_below (ce : Machine.Certified L step object) {b j : Nat}
    (h : shellAddr L step ce.checked b j < fileBase + ce.checked.bytes.size) :
    shellAddr L step ce.checked b j < dataBase := by
  have ff := Machine.fileFacts ce.checked
  have := ff.below
  rw [ff.size] at h
  omega

/-- **The object's text in the file**, inside the address space. -/
theorem file_text (ce : Machine.Certified L step object) :
    ∃ text, ELFRead.text? object = some text ∧
      (∀ i < text.size, ce.checked.bytes[ce.checked.plan.placement.textOffset + i]? = text[i]?) ∧
      ce.checked.plan.placement.textOffset + text.size ≤ 2 ^ 64 := by
  have ff := Machine.fileFacts ce.checked
  obtain ⟨parsed, hp, hsize, htext⟩ := ff.text
  have hd : dataBase = 268435456 := rfl
  have hfs : ce.checked.plan.placement.fileSize =
      ce.checked.plan.placement.shellOffset + ce.checked.plan.placement.shellSize := rfl
  have := ff.below
  have := ff.textEnd
  have := ff.dataEnd
  refine ⟨parsed.text, by simp [ELFRead.text?, hp], fun i hi => htext i (hsize ▸ hi), ?_⟩
  omega

theorem loop_ret_in (ce : Machine.Certified L step object) :
    shellAddr L step ce.checked Machine.B.loop 12 < fileBase + ce.checked.bytes.size :=
  shellAddr_in ce (b := 6) (j := 12) (by decide) (i := Instr.mov .w64 .r11 (.imm (UInt64.ofNat L.callTop))) (by rw [block_loop]; rfl)
    (ne_call_of_op ⟨_, _, rfl⟩)

theorem step_ret_in (ce : Machine.Certified L step object) :
    shellAddr L step ce.checked Machine.B.callStep 10 < fileBase + ce.checked.bytes.size :=
  shellAddr_in ce (b := 8) (j := 10) (by decide) (i := Instr.mov .w64 .r11 (.imm (UInt64.ofNat L.callTop))) (by rw [block_callStep]; rfl)
    (ne_call_of_op ⟨_, _, rfl⟩)

/-- The contract for the iteration's `cx_init` driver. -/
theorem initDriver_ok (ce : Machine.Certified L step object) (s₀ : ByteEval.State) :
    (initDriverOf L ce s₀).Ok ce.checked.plan.placement.textSize := by
  have hlo : fileBase + ce.checked.plan.placement.shellOffset ≤ shellAddr L step ce.checked Machine.B.loop 12 := by
    unfold shellAddr; omega
  have h := driver_ok_at ce s₀.core.memory.bytes hlo (by have := shellAddr_below ce (loop_ret_in ce); have hd : dataBase = 268435456 := rfl; omega)
  exact ⟨h.aligned, h.minSize, h.below, h.spAlign, h.spTop, h.budgetMin, h.spLow, h.apart, h.retOut⟩

/-- The contract at the step's site. -/
theorem stepDriver_ok (ce : Machine.Certified L step object) (s₀ : ByteEval.State) :
    ((initDriverOf L ce s₀).withSite (stepSite L ce s₀)).Ok ce.checked.plan.placement.textSize := by
  have hlo : fileBase + ce.checked.plan.placement.shellOffset ≤ shellAddr L step ce.checked Machine.B.callStep 10 := by
    unfold shellAddr; omega
  have h := driver_ok_at ce s₀.core.memory.bytes hlo (by have := shellAddr_below ce (step_ret_in ce); have hd : dataBase = 268435456 := rfl; omega)
  exact ⟨h.aligned, h.minSize, h.below, h.spAlign, h.spTop, h.budgetMin, h.spLow, h.apart, h.retOut⟩

set_option maxRecDepth 20000 in
/-- **The glue at the step's site** (`stepSite`): with the state and event in `cx_init`'s bytes at
`C` and `C + 8` (outside the mapping, so `cx_init` keeps them), from every return of `cx_init`
with status 0 the shell's next 18 instructions reach the step's call in the state of the step's
driver (`rsi`, `rdx` the state and event loaded from `C`, `rdi` the region, `rcx`, `r8`, `r9`
zero, `rsp` the call top, the rest the site's), or fault on a memory access. -/
theorem glue_at (ce : Machine.Certified L step object) {state event : Nat} (_hs : state < 2 ^ 64)
    (_he : event < 2 ^ 64) {s₀ : ByteEval.State}
    (hst : wordOf (initDriverOf L ce s₀).initBytes (UInt64.ofNat L.callTop) = UInt64.ofNat state ∧
      wordOf (initDriverOf L ce s₀).initBytes (UInt64.ofNat L.callTop + 8) = UInt64.ofNat event) :
    ∀ s₁, Returned (initDriverOf L ce s₀) (initDriverOf L ce s₀).initBytes 0 s₁ →
      (∃ s₂, ByteEval.run ce.checked.bytes fetchBase glueSteps s₁ = .ok s₂ ∧
        AtCall ce.checked.bytes object step ((initDriverOf L ce s₀).withSite (stepSite L ce s₀))
          ([state, event].map UInt64.ofNat) s₁.core.memory.bytes s₂) ∨
      FaultsWithin ce.checked.bytes s₁ glueSteps := by
  intro s₁ hr
  -- the numbers and what the return gives
  have hC : (initDriverOf L ce s₀).sp + 8 = UInt64.ofNat L.callTop :=
    sp_add8 ce (shellAddr L step ce.checked Machine.B.loop 12) s₀.core.memory.bytes
  have hrsp : s₁.core.readReg .rsp = UInt64.ofNat L.callTop := hr.rsp.trans hC
  have hrax : s₁.core.readReg .rax = 0 := hr.rax
  have hsaved : ∀ r ∈ SysV.calleeSaved, s₁.core.readReg r = s₀.core.registers r := hr.saved
  have hword : ∀ k, k ≤ 248 →
      s₁.core.memory.read64 (UInt64.ofNat L.callTop + UInt64.ofNat k) =
        wordOf (initDriverOf L ce s₀).initBytes (UInt64.ofNat L.callTop + UInt64.ofNat k) := by
    intro k hk
    show s₁.core.memory.readLittle _ 8 = (⟨_, fun _ => true, fun _ => true⟩ : Memory).readLittle _ 8
    apply Memory.readLittle_congr
    intro i hi
    rw [UInt64.add_assoc, ← UInt64.ofNat_add]
    exact hr.frame _ (scratch_unmapped ce (shellAddr L step ce.checked Machine.B.loop 12) s₀.core.memory.bytes
      (i := k + i) (by omega))
  -- abbreviations
  let C : Word := UInt64.ofNat L.callTop
  let T : Word := UInt64.ofNat L.shellTop
  let R : Word := UInt64.ofNat L.regionStart
  let a : Nat → Nat → Word := fun b j => UInt64.ofNat (shellAddr L step ce.checked b j)
  let img := ce.checked.bytes
  let cmp : Compare := { width := .w64, left := .rsp, right := .reg .r11 }
  -- loop, instruction 12: mov r11, C
  let k1 := s₁.core.setReg .r11 C
  have e1 : ByteEval.step img fetchBase s₁ = .ok ⟨k1, a 6 13, s₁.flags⟩ :=
    mstep_ok ce (b := 6) (j := 12) (by decide) (s := s₁) (i := Instr.mov .w64 .r11 (.imm C)) (by rw [block_loop]; rfl)
      (ne_call_of_op ⟨_, _, rfl⟩) hr.rip (exec_mov _ _ _ _)
  -- loop's terminator: cmp rsp, r11 (equal), jne not taken, jmp initBack
  have e2 : ByteEval.run img fetchBase 3 ⟨k1, a 6 13, s₁.flags⟩ = .ok ⟨k1, a 7 0, cmp.flags k1⟩ :=
    mrun_branch ce (b := 6) (by decide) (o := cmp.row.1) (args := cmp.row.2) (cond := .ne) (yes := 42) (no := 7)
      (by rw [block_loop]; rfl) (s := ⟨k1, a 6 13, s₁.flags⟩) (core := k1) (fl := cmp.flags k1) (by rw [block_loop]; rfl) (exec_compare _ _ _) (taken := false) (by
        rw [compare_test]
        show some (Condition.holds .ne .w64 (k1.readReg .rsp) (k1.readReg .r11)) = some false
        have h1 : k1.readReg .rsp = C := by
          show (s₁.core.registers.set .r11 C) .rsp = C
          simp only [Registers.set]
          exact hrsp
        have h2 : k1.readReg .r11 = C := by
          show (s₁.core.registers.set .r11 C) .r11 = C
          simp [Registers.set]
        rw [h1, h2]
        simp [Condition.holds])
  -- initBack: mov r11, shellTop; mov rsp, r11; test rax, rax (zero), jne not taken, jmp callStep
  let k3 := k1.setReg .r11 T
  have e3 : ByteEval.step img fetchBase ⟨k1, a 7 0, cmp.flags k1⟩ = .ok ⟨k3, a 7 1, cmp.flags k1⟩ :=
    mstep_ok ce (b := 7) (j := 0) (by decide) (s := ⟨k1, a 7 0, cmp.flags k1⟩) (i := Instr.mov .w64 .r11 (.imm T)) (by rw [block_initBack]; rfl)
      (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
  let k4 := k3.setReg .rsp (k3.readReg .r11)
  have e4 : ByteEval.step img fetchBase ⟨k3, a 7 1, cmp.flags k1⟩ = .ok ⟨k4, a 7 2, cmp.flags k1⟩ :=
    mstep_ok ce (b := 7) (j := 1) (by decide) (s := ⟨k3, a 7 1, cmp.flags k1⟩) (i := Instr.mov .w64 .rsp (.reg .r11)) (by rw [block_initBack]; rfl)
      (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
  have hk4 : k4.readReg .rax = 0 := by
    simp only [k4, k3, k1, Core.readReg, Core.setReg, Registers.set]
    exact hrax
  have e5 : ByteEval.run img fetchBase 3 ⟨k4, a 7 2, cmp.flags k1⟩ =
      .ok ⟨k4, a 8 0, ByteEval.aluFlags .and .w64 0 0⟩ := by
    have h := mrun_branch ce (b := 7) (by decide) (o := { mn := .test, w := .w64, form := .MR })
      (args := [.reg .rax, .reg .rax]) (cond := .ne) (yes := 28) (no := 8) (by rw [block_initBack]; rfl)
      (s := ⟨k4, a 7 2, cmp.flags k1⟩) (core := k4)
      (fl := ByteEval.aluFlags .and .w64 (k4.readReg .rax) (k4.readReg .rax)) (by rw [block_initBack]; rfl) (exec_test _ _ _ _) (taken := false)
      (by rw [test_ne_self, hk4]; rfl)
    rw [hk4] at h
    exact h
  -- callStep: mov r10, C; mov rsi, [r10]; mov rdx, [r10 + 8]; mov rdi, region; rcx, r8, r9 zero;
  -- mov r11, C; mov rsp, r11
  let f2 := ByteEval.aluFlags .and .w64 0 0
  let k6 := k4.setReg .r10 C
  have e6 : ByteEval.step img fetchBase ⟨k4, a 8 0, f2⟩ = .ok ⟨k6, a 8 1, f2⟩ :=
    mstep_ok ce (b := 8) (j := 0) (by decide) (s := ⟨k4, a 8 0, f2⟩) (i := Instr.mov .w64 .r10 (.imm C)) (by rw [block_callStep]; rfl)
      (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
  have hmem6 : k6.memory = s₁.core.memory := rfl
  have hr10 : k6.readReg .r10 = C := by simp [k6, Core.readReg, Core.setReg, Registers.set]
  have hpre : ByteEval.run img fetchBase 10 s₁ = .ok ⟨k6, a 8 1, f2⟩ :=
    run_comp (run_one e1) (run_comp e2 (run_comp (run_one e3) (run_comp (run_one e4) (run_comp e5 (run_one e6)))))
  -- the state's load
  let A0 : MemAddr := { base := some .r10, displacement := UInt32.ofNat 0 }
  have hA0 : A0.eval k6 = C := by
    simp [A0, MemAddr.eval, hr10, signExtend32]
  cases hld1 : s₁.core.memory.read64? C with
  | error f =>
    right
    refine ⟨10, by decide, ⟨k6, a 8 1, f2⟩, f, hpre, ?_⟩
    refine mstep_fault ce (b := 8) (j := 1) (by decide) (s := ⟨k6, a 8 1, f2⟩) (i := Instr.load .w64 .rsi A0) (by rw [block_callStep]; rfl)
      (ne_call_of_op ⟨_, _, rfl⟩) rfl ?_
    rw [exec_load64]
    simp only [hA0, hmem6, hld1]
  | ok v1 =>
    have hv1 : v1 = UInt64.ofNat state := by
      rw [read64?_value hld1, show C = UInt64.ofNat L.callTop + UInt64.ofNat 0 by simp [C],
        hword 0 (by decide)]
      simpa using hst.1
    let k7 := k6.setReg .rsi v1
    have e7 : ByteEval.step img fetchBase ⟨k6, a 8 1, f2⟩ = .ok ⟨k7, a 8 2, f2⟩ :=
      mstep_ok ce (b := 8) (j := 1) (by decide) (s := ⟨k6, a 8 1, f2⟩) (i := Instr.load .w64 .rsi A0) (by rw [block_callStep]; rfl)
        (ne_call_of_op ⟨_, _, rfl⟩) rfl (by rw [exec_load64]; simp only [hA0, hmem6, hld1]; rfl)
    let A8 : MemAddr := { base := some .r10, displacement := UInt32.ofNat 8 }
    have hr10' : k7.readReg .r10 = C := by simp [k7, k6, Core.readReg, Core.setReg, Registers.set]
    have hA8 : A8.eval k7 = C + 8 := by
      simp [A8, MemAddr.eval, hr10', signExtend32]
    cases hld2 : s₁.core.memory.read64? (C + 8) with
    | error f =>
      right
      refine ⟨11, by decide, ⟨k7, a 8 2, f2⟩, f, run_comp hpre (run_one e7), ?_⟩
      refine mstep_fault ce (b := 8) (j := 2) (by decide) (s := ⟨k7, a 8 2, f2⟩) (i := Instr.load .w64 .rdx A8) (by rw [block_callStep]; rfl)
        (ne_call_of_op ⟨_, _, rfl⟩) rfl ?_
      rw [exec_load64]
      simp only [hA8, show k7.memory = s₁.core.memory from rfl, hld2]
    | ok v2 =>
      have hv2 : v2 = UInt64.ofNat event := by
        rw [read64?_value hld2, show C + 8 = UInt64.ofNat L.callTop + UInt64.ofNat 8 from rfl,
          hword 8 (by decide)]
        exact hst.2
      left
      let k8 := k7.setReg .rdx v2
      have e8 : ByteEval.step img fetchBase ⟨k7, a 8 2, f2⟩ = .ok ⟨k8, a 8 3, f2⟩ :=
        mstep_ok ce (b := 8) (j := 2) (by decide) (s := ⟨k7, a 8 2, f2⟩) (i := Instr.load .w64 .rdx A8) (by rw [block_callStep]; rfl)
          (ne_call_of_op ⟨_, _, rfl⟩) rfl
          (by rw [exec_load64]; simp only [hA8, show k7.memory = s₁.core.memory from rfl, hld2]; rfl)
      let k9 := k8.setReg .rdi R
      have e9 : ByteEval.step img fetchBase ⟨k8, a 8 3, f2⟩ = .ok ⟨k9, a 8 4, f2⟩ :=
        mstep_ok ce (b := 8) (j := 3) (by decide) (s := ⟨k8, a 8 3, f2⟩) (i := Instr.mov .w64 .rdi (.imm R)) (by rw [block_callStep]; rfl)
          (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
      let k10 := k9.setReg .rcx (UInt64.ofNat 0)
      have e10 : ByteEval.step img fetchBase ⟨k9, a 8 4, f2⟩ = .ok ⟨k10, a 8 5, f2⟩ :=
        mstep_ok ce (b := 8) (j := 4) (by decide) (s := ⟨k9, a 8 4, f2⟩) (i := Instr.mov .w64 .rcx (.imm (UInt64.ofNat 0))) (by rw [block_callStep]; rfl)
          (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
      let k11 := k10.setReg .r8 (UInt64.ofNat 0)
      have e11 : ByteEval.step img fetchBase ⟨k10, a 8 5, f2⟩ = .ok ⟨k11, a 8 6, f2⟩ :=
        mstep_ok ce (b := 8) (j := 5) (by decide) (s := ⟨k10, a 8 5, f2⟩) (i := Instr.mov .w64 .r8 (.imm (UInt64.ofNat 0))) (by rw [block_callStep]; rfl)
          (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
      let k12 := k11.setReg .r9 (UInt64.ofNat 0)
      have e12 : ByteEval.step img fetchBase ⟨k11, a 8 6, f2⟩ = .ok ⟨k12, a 8 7, f2⟩ :=
        mstep_ok ce (b := 8) (j := 6) (by decide) (s := ⟨k11, a 8 6, f2⟩) (i := Instr.mov .w64 .r9 (.imm (UInt64.ofNat 0))) (by rw [block_callStep]; rfl)
          (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
      let k13 := k12.setReg .r11 C
      have e13 : ByteEval.step img fetchBase ⟨k12, a 8 7, f2⟩ = .ok ⟨k13, a 8 8, f2⟩ :=
        mstep_ok ce (b := 8) (j := 7) (by decide) (s := ⟨k12, a 8 7, f2⟩) (i := Instr.mov .w64 .r11 (.imm C)) (by rw [block_callStep]; rfl)
          (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
      let k14 := k13.setReg .rsp (k13.readReg .r11)
      have e14 : ByteEval.step img fetchBase ⟨k13, a 8 8, f2⟩ = .ok ⟨k14, a 8 9, f2⟩ :=
        mstep_ok ce (b := 8) (j := 8) (by decide) (s := ⟨k13, a 8 8, f2⟩) (i := Instr.mov .w64 .rsp (.reg .r11)) (by rw [block_callStep]; rfl)
          (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
      have hrun : ByteEval.run img fetchBase glueSteps s₁ = .ok ⟨k14, a 8 9, f2⟩ :=
        run_comp hpre (run_comp (run_one e7) (run_comp (run_one e8) (run_comp (run_one e9)
          (run_comp (run_one e10) (run_comp (run_one e11) (run_comp (run_one e12)
            (run_comp (run_one e13) (run_one e14))))))))
      refine ⟨⟨k14, a 8 9, f2⟩, hrun, ?_, ?_, ?_, ?_, rfl, rfl⟩
      · exact mcallsTo ce (b := 8) (j := 9) (by decide) (name := step) (by rw [block_callStep]; rfl) rfl
      · show UInt64.ofNat (shellAddr L step ce.checked 8 10) = a 8 9 + 5
        exact (next_addr (p := shellOf ce.checked) (origin := ce.checked.plan.placement.shellOffset) (b := 8)
          (j := 9) (i := .callExport step) (by rw [block_callStep]; rfl)).symm
      · intro r hr'
        have h1 : s₁.core.registers .rbx = s₀.core.registers .rbx := hsaved .rbx (by simp [SysV.calleeSaved])
        have h2 : s₁.core.registers .rbp = s₀.core.registers .rbp := hsaved .rbp (by simp [SysV.calleeSaved])
        have h3 : s₁.core.registers .r12 = s₀.core.registers .r12 := hsaved .r12 (by simp [SysV.calleeSaved])
        have h4 : s₁.core.registers .r13 = s₀.core.registers .r13 := hsaved .r13 (by simp [SysV.calleeSaved])
        have h5 : s₁.core.registers .r14 = s₀.core.registers .r14 := hsaved .r14 (by simp [SysV.calleeSaved])
        have h6 : s₁.core.registers .r15 = s₀.core.registers .r15 := hsaved .r15 (by simp [SysV.calleeSaved])
        have h0 : s₁.core.registers .rax = 0 := hrax
        cases r <;> simp [k14, k13, k12, k11, k10, k9, k8, k7, k6, k4, k3, k1, Core.readReg, Core.setReg,
          Registers.set, Driver.core, Driver.regs, Driver.withSite, stepSite, initDriverOf,
          Machine.Layout.driverWith, hv1, hv2, C, R, h0, h1, h2, h3, h4, h5, h6] at hr' ⊢
        all_goals first
          | exact hrax
          | exact hsaved _ (by decide)
          | rfl
      · show k14.readReg .rsp = (initDriverOf L ce s₀).sp + 8
        rw [hC]
        simp [k14, k13, Core.readReg, Core.setReg, Registers.set, C]

/-- **The glue**: `glue_at`, with the site left existential (the step's site is fixed before
`cx_init` returns). -/
theorem glue (ce : Machine.Certified L step object) {state event : Nat} (hs : state < 2 ^ 64) (he : event < 2 ^ 64)
    {s₀ : ByteEval.State}
    (hst : wordOf (initDriverOf L ce s₀).initBytes (UInt64.ofNat L.callTop) = UInt64.ofNat state ∧
      wordOf (initDriverOf L ce s₀).initBytes (UInt64.ofNat L.callTop + 8) = UInt64.ofNat event) :
    ∃ site : Driver.Site, ((initDriverOf L ce s₀).withSite site).Ok ce.checked.plan.placement.textSize ∧
      ∀ s₁, Returned (initDriverOf L ce s₀) (initDriverOf L ce s₀).initBytes 0 s₁ →
        (∃ s₂, ByteEval.run ce.checked.bytes fetchBase glueSteps s₁ = .ok s₂ ∧
          AtCall ce.checked.bytes object step ((initDriverOf L ce s₀).withSite site)
            ([state, event].map UInt64.ofNat) s₁.core.memory.bytes s₂) ∨
        FaultsWithin ce.checked.bytes s₁ glueSteps :=
  ⟨stepSite L ce s₀, stepDriver_ok ce s₀, glue_at ce hs he hst⟩

/-- **The iteration's calls at the step's site**: from the process at `cx_init`'s call site in the
iteration's driver state, the session model's call on the state and event (`Lang.run` of
`linkedOf` with the step's site `stepSite`, the observation `objCallAtOf` and the session theorem
use) is lifted to the process (`two_calls`, with `glue_at` for the instructions between the
calls). -/
theorem iteration_calls_at (ce : Machine.Certified L step object)
    {roots : List Linked.Root} {sig : Rt.Sig}
    (hroot : roots[0]? = some { symbol := step, params := 2, ty := some (sig, .nat) })
    {state event : Nat} (hs : state < 2 ^ 64) (he : event < 2 ^ 64) {s₀ : ByteEval.State}
    (hat : AtCall ce.checked.bytes object Rt.Procs.initSymbol (initDriverOf L ce s₀)
      [(initDriverOf L ce s₀).size, (initDriverOf L ce s₀).budget] (initDriverOf L ce s₀).initBytes s₀)
    (hst : wordOf (initDriverOf L ce s₀).initBytes (UInt64.ofNat L.callTop) = UInt64.ofNat state ∧
      wordOf (initDriverOf L ce s₀).initBytes (UInt64.ofNat L.callTop + 8) = UInt64.ofNat event)
    (k : Nat) :
    CallsLift ce.checked.bytes (linkedOf object roots (initDriverOf L ce s₀) (stepSite L ce s₀))
      { symbol := step, params := 2, ty := some (sig, .nat) } s₀ (k + 1 + glueSteps + (k + 1)) k
      (Lang.run (linkedOf object roots (initDriverOf L ce s₀) (stepSite L ce s₀)) (0, [state, event]) k) := by
  obtain ⟨text, htext, hw, hfit⟩ := file_text ce
  have hrun : Lang.run (linkedOf object roots (initDriverOf L ce s₀) (stepSite L ce s₀)) (0, [state, event]) k =
      (linkedOf object roots (initDriverOf L ce s₀) (stepSite L ce s₀)).call
        { symbol := step, params := 2, ty := some (sig, .nat) } [state, event] k := by
    show LinkedAt.run _ _ k = _
    simp only [LinkedAt.run, linkedOf, hroot]
    exact Sem.entryRun_exact rfl k
  rw [hrun]
  have hns : [state, event].all (· < 2 ^ 64) = true := by simp [hs, he]
  exact two_calls (L := linkedOf object roots (initDriverOf L ce s₀) (stepSite L ce s₀))
    (r := { symbol := step, params := 2, ty := some (sig, .nat) }) (g := glueSteps) htext hw hfit
    (initDriver_ok ce s₀) (stepDriver_ok ce s₀) rfl hns hat (glue_at ce hs he hst) k

/-- **The iteration's calls**: `iteration_calls_at`, with the site left existential. -/
theorem iteration_calls (ce : Machine.Certified L step object)
    {roots : List Linked.Root} {sig : Rt.Sig}
    (hroot : roots[0]? = some { symbol := step, params := 2, ty := some (sig, .nat) })
    {state event : Nat} (hs : state < 2 ^ 64) (he : event < 2 ^ 64) {s₀ : ByteEval.State}
    (hat : AtCall ce.checked.bytes object Rt.Procs.initSymbol (initDriverOf L ce s₀)
      [(initDriverOf L ce s₀).size, (initDriverOf L ce s₀).budget] (initDriverOf L ce s₀).initBytes s₀)
    (hst : wordOf (initDriverOf L ce s₀).initBytes (UInt64.ofNat L.callTop) = UInt64.ofNat state ∧
      wordOf (initDriverOf L ce s₀).initBytes (UInt64.ofNat L.callTop + 8) = UInt64.ofNat event)
    (k : Nat) :
    ∃ site : Driver.Site, (initDriverOf L ce s₀).Ok ce.checked.plan.placement.textSize ∧
      ((initDriverOf L ce s₀).withSite site).Ok ce.checked.plan.placement.textSize ∧
      CallsLift ce.checked.bytes (linkedOf object roots (initDriverOf L ce s₀) site)
        { symbol := step, params := 2, ty := some (sig, .nat) } s₀ (k + 1 + glueSteps + (k + 1)) k
        (Lang.run (linkedOf object roots (initDriverOf L ce s₀) site) (0, [state, event]) k) :=
  ⟨stepSite L ce s₀, initDriver_ok ce s₀, stepDriver_ok ce s₀, iteration_calls_at ce hroot hs he hat hst k⟩

end

end IxCC.X86.Exe.Process
