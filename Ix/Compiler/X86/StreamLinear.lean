import Ix.Compiler.X86.StreamValidate

/-! Actual text fetch and typed-PC advancement for every linear instruction.
The checked program supplies the successor bound; no unchecked PC-overflow
case is hidden in the successful core relation. -/

namespace Ix.Compiler.X86.Stream

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

def AtPC (program : Program) (base : Word) (pc : PC) (rip : Word) : Prop :=
  ∃ offset, pcOffset? program pc = some offset ∧ rip = base + UInt64.ofNat offset

theorem AtPC.offset {program : Program} {base rip : Word} {pc : PC} {block : Block}
    (atPC : AtPC program base pc rip) (found : program.blocks[pc.block.toNat]? = some block)
    (bound : pc.offset.toNat ≤ block.instructions.size) :
    rip = base + UInt64.ofNat (blockOffset program pc.block.toNat + instructionOffset block pc.offset.toNat) := by
  obtain ⟨offset, mapped, address⟩ := atPC
  simp [pcOffset?, found, bound] at mapped
  subst offset
  exact address

theorem AtPC.small {program : Program} {pc : PC} {offset : Nat}
    (bound : textSize program < UInt64.size) (mapped : pcOffset? program pc = some offset) :
    offset < UInt64.size := Nat.lt_trans (pcOffset_small mapped) bound

theorem linear_rip (instruction : Instr) (linear : Encode.linearInstruction instruction = true)
    (state : ByteEval.State) (length : Nat) {after : ByteEval.State}
    (evaluated : ByteEval.execute ⟨Encode.instructionOperation instruction, length⟩ state = .ok after) :
    after.rip = state.rip + UInt64.ofNat length := by
  cases instruction with
  | load width destination address =>
      cases memoryResult : state.core.loadReg? width destination (address.eval state.core) <;>
        simp_all [Encode.instructionOperation, ByteEval.execute, Except.mapError] <;> cases evaluated <;> rfl
  | store width address source =>
      cases memoryResult : state.core.storeReg? width (address.eval state.core) source <;>
        simp_all [Encode.instructionOperation, ByteEval.execute, Except.mapError] <;> cases evaluated <;> rfl
  | push source =>
      cases memoryResult : state.core.memory.write64? (state.core.readReg .rsp - 8) (state.core.readReg source) <;>
        simp_all [Encode.instructionOperation, ByteEval.execute, Except.mapError] <;> cases evaluated <;> rfl
  | pop destination =>
      cases memoryResult : state.core.memory.read64? (state.core.readReg .rsp) <;>
        simp_all [Encode.instructionOperation, ByteEval.execute, Except.mapError] <;> cases evaluated <;> rfl
  | spill slot source =>
      cases memoryResult : state.core.storeReg? .w64 (state.core.readReg .rbp - slot.displacement) source <;>
        simp_all [Encode.instructionOperation, ByteEval.execute, Except.mapError] <;> cases evaluated <;> rfl
  | reload destination slot =>
      cases memoryResult : state.core.loadReg? .w64 destination (state.core.readReg .rbp - slot.displacement) <;>
        simp_all [Encode.instructionOperation, ByteEval.execute, Except.mapError] <;> cases evaluated <;> rfl
  | _ => simp_all [Encode.linearInstruction, Encode.instructionOperation, ByteEval.execute] <;> cases evaluated <;> rfl

/-- Fetch uses the complete certified text and its actual byte RIP. -/
theorem fetch_linear {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (base rip : Word) (pc : PC)
    (atPC : AtPC checked.program base pc rip) {block : Block} {instruction : Instr}
    (found : checked.program.blocks[pc.block.toNat]? = some block)
    (foundInstruction : block.instructions[pc.offset.toNat]? = some instruction)
    (linear : Encode.linearInstruction instruction = true) :
    Decode.decodeAt output.text (rip - base).toNat =
      some ⟨Encode.instructionOperation instruction, instructionSize instruction⟩ := by
  have indexBound := (Array.getElem?_eq_some_iff.mp foundInstruction).1
  have address := atPC.offset found (by omega)
  have mapped : pcOffset? checked.program pc =
      some (blockOffset checked.program pc.block.toNat + instructionOffset block pc.offset.toNat) := by
    simp [pcOffset?, found, show pc.offset.toNat ≤ block.instructions.size by omega]
  rw [address, rip_offset _ _ (AtPC.small valid.textBound mapped)]
  exact valid.decode_linear found foundInstruction linear

def LinearResult (program : Program) (base : Word) (before after : Machine) :
    Except ByteEval.Fault ByteEval.State → Prop
  | .ok state => after.core = state.core ∧ after.status = .running ∧ AtPC program base after.pc state.rip
  | .error (.memory fault) => after = before.trap (.memoryFault fault)
  | .error _ => False

theorem linear_step {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (running : machine.status = .running) (base rip : Word) (flags : ByteEval.Flags)
    (atPC : AtPC checked.program base machine.pc rip) {block : Block} {instruction : Instr}
    (found : checked.program.blocks[machine.pc.block.toNat]? = some block)
    (foundInstruction : block.instructions[machine.pc.offset.toNat]? = some instruction)
    (linear : Encode.linearInstruction instruction = true) :
    LinearResult checked.program base machine (step runtime checked machine)
      (ByteEval.step output.text base ⟨machine.core, rip, flags⟩) := by
  have fetched := fetch_linear valid base rip machine.pc atPC found foundInstruction linear
  have bytesStep : ByteEval.step output.text base ⟨machine.core, rip, flags⟩ =
      ByteEval.execute ⟨Encode.instructionOperation instruction, instructionSize instruction⟩ ⟨machine.core, rip, flags⟩ := by
    simp [ByteEval.step, fetched]
  have sourceStep : step runtime checked machine = executeInstr runtime checked instruction machine := by
    simp [step, running, found, foundInstruction]
  have agreement := Encode.instruction_execution instruction linear runtime checked machine rip flags (instructionSize instruction)
  have next := pc_next found foundInstruction
  rw [sourceStep, bytesStep]
  cases evaluated : ByteEval.execute ⟨Encode.instructionOperation instruction, instructionSize instruction⟩
      ⟨machine.core, rip, flags⟩ with
  | error fault =>
      cases fault with
      | memory fault => exact (by simpa [LinearResult, Encode.LinearAgreement, evaluated] using agreement)
      | decode address | undefinedCondition condition => simp [Encode.LinearAgreement, evaluated] at agreement
  | ok after =>
      simp only [evaluated, Encode.LinearAgreement, Machine.advanceWith, next.1] at agreement
      rw [agreement]
      refine ⟨rfl, running, ?_⟩
      refine ⟨_, pcOffset_next found foundInstruction, ?_⟩
      have advance := linear_rip instruction linear ⟨machine.core, rip, flags⟩ (instructionSize instruction) evaluated
      have indexBound := (Array.getElem?_eq_some_iff.mp foundInstruction).1
      have address := atPC.offset found (by omega)
      simpa [address, UInt64.ofNat_add, UInt64.add_assoc] using advance

end Ix.Compiler.X86.Stream
