import IxCC.X86.Exe.Machine.Proof.Call
import IxCC.X86.ByteFlags
import IxCC.X86.Constructors

/-!
# The shell's instructions on the byte machine (X0-P, third part)

The shell proof runs the generic shell (`X86/Exe/Machine.lean`) on the byte
machine (`ByteEval`), block by block. Each of the shell's instructions is a
row of the instruction table, and the byte machine executes a row through
`Op.exec`, the executor the typed machine (`X86.Eval`) also uses. The typed
machine's effects of the table's constructors are proved already
(`X86/Constructors.lean`: `executeInstr_mov`, `_lea`, `_alu`, `_load`,
`_store`, each with its memory fault). `execute_of_advance` and
`execute_of_trap` carry them over through the per-row agreement law
(`Encode.instruction_execution`), and `execute_flags` adds that a row which
declares no flag effect keeps the byte machine's flags.

What this gives, for any state: `mov r, imm` (each of its three rows) and
`mov r, r'`, `lea`, the 64-bit load and store with their faults, the byte
load (`movzx`) and store, and `op r, imm`/`op r, r'` at any width with some
flags. The flag producers of the shell's branches (`cmp`, `test`) are
`Encode.compare_execution` and `exec_test`.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process
open IxCC.X86.Encode (instructionOperation execute_linear linearInstruction)

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

/-! ## From the typed machine's effect to the byte machine's -/

/-- A typed machine about to run one instruction from `core`. -/
def probe (core : Core) : Machine := { core, pc := ⟨0, 0⟩, returns := [], status := .running }

/-- A checked program (the typed effect lemmas hold for every one). -/
def anyChecked : X86.Checked := ⟨{ blocks := #[{ instructions := #[], terminator := .ret }], entry := 0 }, by decide +kernel⟩

@[simp] theorem probe_core (core : Core) : (probe core).core = core := rfl

theorem probe_advance (core core' : Core) :
    (probe core).advanceWith core' = { core := core', pc := ⟨0, 1⟩, returns := [], status := .running } := rfl

/-- A linear row moves `rip` past itself. -/
theorem execute_rip {i : Instr} (lin : linearInstruction i = true) {len : Nat} {s st : ByteEval.State}
    (h : ByteEval.execute ⟨instructionOperation i, len⟩ s = .ok st) : st.rip = s.rip + UInt64.ofNat len := by
  cases i with
  | op o args =>
    simp only [linearInstruction, Bool.and_eq_true] at lin
    simp only [instructionOperation] at h
    rw [execute_linear lin.1] at h
    split at h
    · cases h; rfl
    · cases h
  | _ => simp [linearInstruction] at lin

/-- **The bridge**: where the typed machine advances with `core'`, the byte machine's
`execute` gives `core'`, past the instruction. -/
theorem execute_of_advance {i : Instr} (lin : linearInstruction i = true) {s : ByteEval.State} {core' : Core}
    (h : executeInstr Runtime.rejecting anyChecked i (probe s.core) = (probe s.core).advanceWith core')
    (len : Nat) : ∃ fl, ByteEval.execute ⟨instructionOperation i, len⟩ s = .ok ⟨core', s.rip + UInt64.ofNat len, fl⟩ := by
  have ha := Encode.instruction_execution i lin Runtime.rejecting anyChecked (probe s.core) s.rip s.flags len
  rw [h] at ha
  have hs : (⟨(probe s.core).core, s.rip, s.flags⟩ : ByteEval.State) = s := rfl
  rw [hs] at ha
  cases hx : ByteEval.execute ⟨instructionOperation i, len⟩ s with
  | ok st =>
    rw [hx] at ha
    have hc : core' = st.core := by
      simp only [Encode.LinearAgreement, probe_advance] at ha
      exact congrArg Machine.core ha
    refine ⟨st.flags, ?_⟩
    rw [hc, ← execute_rip lin hx]
  | error f =>
    rw [hx] at ha
    cases f <;> simp [Encode.LinearAgreement, Machine.advanceWith, PC.next?, Machine.trap, probe] at ha

/-- Where the typed machine traps on a memory fault, the byte machine faults alike. -/
theorem execute_of_trap {i : Instr} (lin : linearInstruction i = true) {s : ByteEval.State} {f : MemoryFault}
    (h : executeInstr Runtime.rejecting anyChecked i (probe s.core) = (probe s.core).trap (.memoryFault f))
    (len : Nat) : ByteEval.execute ⟨instructionOperation i, len⟩ s = .error (.memory f) := by
  have ha := Encode.instruction_execution i lin Runtime.rejecting anyChecked (probe s.core) s.rip s.flags len
  rw [h] at ha
  have hs : (⟨(probe s.core).core, s.rip, s.flags⟩ : ByteEval.State) = s := rfl
  rw [hs] at ha
  cases hx : ByteEval.execute ⟨instructionOperation i, len⟩ s with
  | ok st =>
    rw [hx] at ha
    simp [Encode.LinearAgreement, Machine.advanceWith, PC.next?, Machine.trap, probe] at ha
  | error g =>
    rw [hx] at ha
    cases g <;> simp [Encode.LinearAgreement, Machine.trap, probe] at ha
    subst ha; rfl

theorem merge_unchanged (flags computed : ByteEval.Flags) :
    flags.merge (fun _ => .unchanged) computed = flags := by cases flags; rfl

/-- A row that leaves every flag unchanged keeps the byte machine's flags. -/
theorem execute_flags {o : Op} {args : List Arg} (lin : o.linear = true)
    (hfl : (desc o).flagsOut = fun _ => .unchanged) {len : Nat} {s st : ByteEval.State}
    (h : ByteEval.execute ⟨.op o args, len⟩ s = .ok st) : st.flags = s.flags := by
  rw [execute_linear lin] at h
  unfold Op.exec at h
  cases hr : o.run args s.core (s.flags.restrict (desc o).flagsIn) with
  | error e => rw [hr] at h; cases h
  | ok r => rw [hr] at h; cases h; simp only [hfl, merge_unchanged]

/-! ## The shell's instructions -/

/-- `mov r, imm` (any of its three rows) and `mov r, r'`. -/
theorem exec_mov (s : ByteEval.State) (r : GPR) (src : MoveSource) (len : Nat) :
    ByteEval.execute ⟨instructionOperation (Instr.mov .w64 r src), len⟩ s =
      .ok ⟨s.core.setReg r (src.eval s.core), s.rip + UInt64.ofNat len, s.flags⟩ := by
  obtain ⟨fl, h⟩ := execute_of_advance (Encode.linear_mov .w64 r src) (s := s)
    (core' := s.core.setReg r (src.eval s.core)) (by simp [Core.writeReg, probe_core]) len
  rw [h]
  have hf : fl = s.flags := by
    cases src with
    | reg r' => exact execute_flags rfl rfl h
    | imm v =>
      simp only [Instr.mov, Instr.ofRow, movImmRow] at h
      split at h
      · exact execute_flags rfl rfl h
      · split at h
        · exact execute_flags rfl rfl h
        · exact execute_flags rfl rfl h
  rw [hf]

/-- `lea r, [a]`. -/
theorem exec_lea (s : ByteEval.State) (r : GPR) (a : MemAddr) (len : Nat) :
    ByteEval.execute ⟨instructionOperation (Instr.lea r a), len⟩ s =
      .ok ⟨s.core.setReg r (a.eval s.core), s.rip + UInt64.ofNat len, s.flags⟩ := by
  obtain ⟨fl, h⟩ := execute_of_advance (i := Instr.lea r a) rfl (s := s)
    (core' := s.core.setReg r (a.eval s.core)) (by simp [probe_core]) len
  have hf : fl = s.flags := execute_flags rfl rfl h
  exact hf ▸ h

/-- `mov r, [a]` (64 bits). -/
theorem exec_load64 (s : ByteEval.State) (r : GPR) (a : MemAddr) (len : Nat) :
    ByteEval.execute ⟨instructionOperation (Instr.load .w64 r a), len⟩ s =
      match s.core.memory.read64? (a.eval s.core) with
      | .ok v => .ok ⟨s.core.setReg r v, s.rip + UInt64.ofNat len, s.flags⟩
      | .error f => .error (.memory f) := by
  cases hr : s.core.memory.read64? (a.eval s.core) with
  | ok v =>
    obtain ⟨fl, h⟩ := execute_of_advance (i := Instr.load .w64 r a) rfl (s := s)
      (core' := s.core.setReg r v) (by
        simp only [executeInstr_load, Core.loadReg?, probe_core]
        unfold Memory.read64? at hr
        rw [hr]; simp [Encode.truncate64]) len
    have hf : fl = s.flags := execute_flags rfl rfl h
    exact hf ▸ h
  | error f =>
    exact execute_of_trap (i := Instr.load .w64 r a) rfl (by
      simp only [executeInstr_load, Core.loadReg?, probe_core]
      unfold Memory.read64? at hr
      rw [hr]; rfl) len

/-- `mov [a], r` (64 bits). -/
theorem exec_store64 (s : ByteEval.State) (a : MemAddr) (r : GPR) (len : Nat) :
    ByteEval.execute ⟨instructionOperation (Instr.store .w64 a r), len⟩ s =
      match s.core.memory.write64? (a.eval s.core) (s.core.readReg r) with
      | .ok m => .ok ⟨{ s.core with memory := m }, s.rip + UInt64.ofNat len, s.flags⟩
      | .error f => .error (.memory f) := by
  cases hw : s.core.memory.write64? (a.eval s.core) (s.core.readReg r) with
  | ok m =>
    obtain ⟨fl, h⟩ := execute_of_advance (i := Instr.store .w64 a r) rfl (s := s)
      (core' := { s.core with memory := m }) (by
        simp only [executeInstr_store, Core.storeReg?, probe_core]
        unfold Memory.write64? at hw
        rw [hw]; rfl) len
    have hf : fl = s.flags := execute_flags rfl rfl h
    exact hf ▸ h
  | error f =>
    exact execute_of_trap (i := Instr.store .w64 a r) rfl (by
      simp only [executeInstr_store, Core.storeReg?, probe_core]
      unfold Memory.write64? at hw
      rw [hw]; rfl) len

/-- `mov byte [a], r8` (the low byte of `r`). -/
theorem exec_store8 (s : ByteEval.State) (a : MemAddr) (r : GPR) (len : Nat) :
    ByteEval.execute ⟨instructionOperation (Instr.store .w8 a r), len⟩ s =
      match s.core.memory.write? .w8 (a.eval s.core) (s.core.readReg r) with
      | .ok m => .ok ⟨{ s.core with memory := m }, s.rip + UInt64.ofNat len, s.flags⟩
      | .error f => .error (.memory f) := by
  cases hw : s.core.memory.write? .w8 (a.eval s.core) (s.core.readReg r) with
  | ok m =>
    obtain ⟨fl, h⟩ := execute_of_advance (i := Instr.store .w8 a r) rfl (s := s)
      (core' := { s.core with memory := m }) (by
        simp only [executeInstr_store, Core.storeReg?, probe_core]
        rw [hw]; rfl) len
    have hf : fl = s.flags := execute_flags rfl rfl h
    exact hf ▸ h
  | error f =>
    exact execute_of_trap (i := Instr.store .w8 a r) rfl (by
      simp only [executeInstr_store, Core.storeReg?, probe_core]
      rw [hw]; rfl) len

/-- `movzx r32, byte [a]`. -/
theorem exec_load8 (s : ByteEval.State) (r : GPR) (a : MemAddr) (len : Nat) :
    ByteEval.execute ⟨instructionOperation (Instr.load .w8 r a), len⟩ s =
      match s.core.memory.read? .w8 (a.eval s.core) with
      | .ok v => .ok ⟨s.core.setReg r (Width.w8.truncate v), s.rip + UInt64.ofNat len, s.flags⟩
      | .error f => .error (.memory f) := by
  cases hr : s.core.memory.read? .w8 (a.eval s.core) with
  | ok v =>
    obtain ⟨fl, h⟩ := execute_of_advance (i := Instr.load .w8 r a) rfl (s := s)
      (core' := s.core.setReg r (Width.w8.truncate v)) (by
        simp only [executeInstr_load, Core.loadReg?, probe_core]
        rw [hr]; rfl) len
    have hf : fl = s.flags := execute_flags rfl rfl h
    exact hf ▸ h
  | error f =>
    exact execute_of_trap (i := Instr.load .w8 r a) rfl (by
      simp only [executeInstr_load, Core.loadReg?, probe_core]
      rw [hr]; rfl) len

/-- `op r, imm` and `op r, r'` (add, sub, and, …) at a width: the result, and some flags. -/
theorem exec_alu (s : ByteEval.State) (op : AluOp) (w : Width) (r : GPR) (src : AluSource) (len : Nat) :
    ∃ fl, ByteEval.execute ⟨instructionOperation (Instr.alu op w r src), len⟩ s =
      .ok ⟨s.core.writeReg w r (op.eval (s.core.readReg r) (src.eval s.core)), s.rip + UInt64.ofNat len, fl⟩ :=
  execute_of_advance (Encode.linear_alu op w r src) (by simp) len

/-- `test r, r'` (64 bits): the core unchanged, the flags of `r &&& r'`. -/
theorem exec_test (s : ByteEval.State) (r r' : GPR) (len : Nat) :
    ByteEval.execute ⟨.op { mn := .test, w := .w64, form := .MR } [.reg r, .reg r'], len⟩ s =
      .ok ⟨s.core, s.rip + UInt64.ofNat len, ByteEval.aluFlags .and .w64 (s.core.readReg r) (s.core.readReg r')⟩ := by
  rw [execute_linear rfl]
  simp [Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.testDesc, Table.rmSlot, Table.regSlot, Table.testSem,
    readSlots, writeSlots, Arg.load, Except.mapError, ByteEval.merge_allSet]

/-- `test r, r` takes `jne` exactly when `r` is nonzero. -/
theorem test_ne_self (v : Word) : (ByteEval.aluFlags .and .w64 v v).test .ne = some (v != 0) := by
  simp only [ByteEval.aluFlags, ByteEval.Flags.test, ByteEval.resultFlags, BitVec.and_self, Option.map_some]
  congr 1
  show (!(v.toBitVec.setWidth 64 == 0#64)) = !(v == 0)
  congr 1
  rw [BitVec.setWidth_eq]
  cases h : v == 0
  · have h1 : v ≠ 0 := by simpa using h
    have h2 : v.toBitVec ≠ 0#64 := fun e => h1 (UInt64.toBitVec_inj.mp (by rw [e]; rfl))
    simpa using h2
  · have h1 : v = 0 := by simpa using h
    subst h1
    rfl

/-- A comparison's `cmp` row: the core unchanged, the comparison's flags. -/
theorem exec_compare (cmp : Compare) (s : ByteEval.State) (len : Nat) :
    ByteEval.execute ⟨.op cmp.row.1 cmp.row.2, len⟩ s = .ok ⟨s.core, s.rip + UInt64.ofNat len, cmp.flags s.core⟩ := by
  rw [Encode.execute_linear (Compare.row_linear cmp), Compare.exec_eq, Compare.flags_eq]

/-- What a comparison's flags say of a condition. -/
theorem compare_test (cmp : Compare) (cond : Condition) (core : Core) :
    (cmp.flags core).test cond = some (cond.holds cmp.width (core.readReg cmp.left) (cmp.right.eval core)) := by
  rw [Compare.flags_test, Compare.holds_eq]

/-- A table instruction is no `call`. -/
theorem ne_call_of_op {i : Instr} (h : ∃ o args, i = .op o args) : ∀ t, i ≠ .call t := by
  obtain ⟨o, args, rfl⟩ := h
  intro t h
  cases h

end IxCC.X86.Exe.Process
