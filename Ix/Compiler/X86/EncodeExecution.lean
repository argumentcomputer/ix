import Ix.Compiler.X86.EncodeLength
import Ix.Compiler.X86.ByteFlags

/-! Per-form execution agreement with the existing typed evaluator, including
its modeled memory faults. Symbolic control addresses and external calls have
separate local contracts below; a complete linked stream relation is E2. -/

namespace Ix.Compiler.X86.Encode

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

def linearInstruction : Instr → Bool
  | .call _ | .callRuntime _ => false
  | _ => true

def LinearAgreement (before after : Machine) : Except ByteEval.Fault ByteEval.State → Prop
  | .ok state => after = before.advanceWith state.core
  | .error (.memory fault) => after = before.trap (.memoryFault fault)
  | .error _ => False

theorem moveOperand_write (width : Width) (destination : GPR) (source : MoveSource) (core : Core) :
    core.writeReg width destination (ByteEval.operand (moveOperand width source) core) =
      core.writeReg width destination (source.eval core) := by
  cases source <;> simp [moveOperand, ByteEval.operand, MoveSource.eval, writeReg_truncate]

theorem aluOperand_low (width : Width) (source : AluSource) (core : Core) :
    width.truncate (ByteEval.operand (aluOperand width source) core) =
      width.truncate (source.eval core) := by
  cases source <;> simp [aluOperand, ByteEval.operand, AluSource.eval, normalizedImmediate_truncate]

theorem aluOperand_write (operation : AluOp) (width : Width) (destination : GPR)
    (source : AluSource) (core : Core) :
    core.writeReg width destination
      (operation.eval (core.readReg destination) (ByteEval.operand (aluOperand width source) core)) =
    core.writeReg width destination (operation.eval (core.readReg destination) (source.eval core)) :=
  writeReg_congr _ _ _ _ _ (alu_congr_right _ _ _ _ _ (aluOperand_low width source core))

/-- Length, RIP and prior flags are arbitrary here: each emitted linear form
has the same register/memory effect or the same precise memory fault. -/
theorem instruction_execution (instruction : Instr) (linear : linearInstruction instruction = true)
    (runtime : Runtime) (checked : Checked) (machine : Machine)
    (rip : Word) (flags : ByteEval.Flags) (length : Nat) :
    LinearAgreement machine (executeInstr runtime checked instruction machine)
      (ByteEval.execute ⟨instructionOperation instruction, length⟩ ⟨machine.core, rip, flags⟩) := by
  cases instruction with
  | mov width destination source =>
    simp [instructionOperation, ByteEval.execute, LinearAgreement, executeInstr, moveOperand_write]
  | load width destination address =>
    simp only [instructionOperation, ByteEval.execute, normalizedAddress_eval, executeInstr]
    cases machine.core.loadReg? width destination (address.eval machine.core) <;>
      simp [LinearAgreement, Except.mapError]
  | store width address source =>
    simp only [instructionOperation, ByteEval.execute, normalizedAddress_eval, executeInstr]
    cases machine.core.storeReg? width (address.eval machine.core) source <;>
      simp [LinearAgreement, Except.mapError]
  | lea destination address =>
    simp [instructionOperation, ByteEval.execute, LinearAgreement, executeInstr]
  | alu operation width destination source =>
    simp [instructionOperation, ByteEval.execute, LinearAgreement, executeInstr, aluOperand_write]
  | imul width destination source =>
    simp [instructionOperation, ByteEval.execute, LinearAgreement, executeInstr]
  | push source =>
    simp only [instructionOperation, ByteEval.execute, executeInstr]
    cases machine.core.memory.write64? (machine.core.readReg .rsp - 8) (machine.core.readReg source) <;>
      simp [LinearAgreement, Except.mapError]
  | pop destination =>
    simp only [instructionOperation, ByteEval.execute, executeInstr]
    cases machine.core.memory.read64? (machine.core.readReg .rsp) <;>
      simp [LinearAgreement, Except.mapError]
  | allocFrame size | freeFrame size =>
    simp [instructionOperation, ByteEval.execute, LinearAgreement, executeInstr,
      ByteEval.operand, Core.writeReg, AluOp.eval]
  | spill slot source =>
    simp only [instructionOperation, ByteEval.execute, spillAddress_eval, executeInstr]
    cases machine.core.storeReg? .w64 (machine.core.readReg .rbp - slot.displacement) source <;>
      simp [LinearAgreement, Except.mapError]
  | reload destination slot =>
    simp only [instructionOperation, ByteEval.execute, spillAddress_eval, executeInstr]
    cases machine.core.loadReg? .w64 destination (machine.core.readReg .rbp - slot.displacement) <;>
      simp [LinearAgreement, Except.mapError]
  | call target | callRuntime intrinsic => simp [linearInstruction] at linear

/-- The execution theorem consumes the actual encoder bytes, surrounded by
arbitrary bytes. The explicit boundary is a premise for this local E1 result. -/
theorem encoded_instruction_execution (instruction : Instr)
    (linear : linearInstruction instruction = true) (before after : ByteArray)
    (runtime : Runtime) (checked : Checked) (machine : Machine) (flags : ByteEval.Flags)
    (textBase rip : Word) (boundary : (rip - textBase).toNat = before.size) :
    LinearAgreement machine (executeInstr runtime checked instruction machine)
      (ByteEval.step (before ++ (encodeInstr instruction).bytes ++ after) textBase
        ⟨machine.core, rip, flags⟩) := by
  rw [ByteEval.step, boundary, instruction_decodeAt]
  exact instruction_execution instruction linear runtime checked machine rip flags _

theorem condition_congr (condition : Condition) (width : Width) (left first second : Word)
    (equal : width.truncate first = width.truncate second) :
    condition.holds width left first = condition.holds width left second := by
  cases condition <;> simp [Condition.holds, Width.signedValue, equal]

theorem compare_execution (comparison : Compare) (condition : Condition)
    (state : ByteEval.State) (length : Nat) :
    let next := ByteEval.execute
      ⟨.compare comparison.width comparison.left (aluOperand comparison.width comparison.right), length⟩ state
    ∃ after, next = .ok after ∧ after.core = state.core ∧
      after.rip = state.rip + UInt64.ofNat length ∧
      after.flags.test condition = some (comparison.holds condition state.core) := by
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  rw [ByteEval.compare_flags]
  exact congrArg some (condition_congr _ _ _ _ _ (aluOperand_low _ _ _))

end Ix.Compiler.X86.Encode
