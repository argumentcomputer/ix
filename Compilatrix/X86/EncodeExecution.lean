import Compilatrix.X86.EncodeLength
import Compilatrix.X86.ByteFlags

/-! E1 execution agreement, generic over rows. Both machines run a linear
row through `Op.exec`, so its semantic function, operand reads and writes,
and memory faults are shared. A linear row declares no input flags, so the
typed machine (no flags) and the byte machine (its current flags) compute
the same core; only the byte machine keeps the merged flags. -/

namespace Compilatrix.X86.Encode

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

/-- Typed instructions executed by one linear row. Calls are separate
control laws. -/
def linearInstruction : Instr → Bool
  | .op o _ => o.linear && (desc o).flagsIn.isEmpty
  | .call _ | .callRuntime _ => false

@[simp] theorem linear_mov (width : Width) (destination : GPR) (source : MoveSource) :
    linearInstruction (.mov width destination source) = true := by
  cases source <;> cases width <;> simp only [Instr.mov, Instr.ofRow, movImmRow] <;> (try split) <;>
    (try split) <;> rfl

@[simp] theorem linear_alu (operation : AluOp) (width : Width) (destination : GPR) (source : AluSource) :
    linearInstruction (.alu operation width destination source) = true := by
  cases operation <;> cases source <;> simp only [Instr.alu, Instr.ofRow, aluImmRow] <;> (try split) <;> rfl

@[simp] theorem linear_allocFrame (size : FrameSize) : linearInstruction (.allocFrame size) = true := by
  simp only [Instr.allocFrame, Instr.ofRow, aluImmRow]
  split <;> rfl

@[simp] theorem linear_freeFrame (size : FrameSize) : linearInstruction (.freeFrame size) = true := by
  simp only [Instr.freeFrame, Instr.ofRow, aluImmRow]
  split <;> rfl

/-- Every listed linear row declares no input flags. -/
theorem table_flagsFree : Op.rows.all (fun o => !o.linear || (desc o).flagsIn.isEmpty) = true := by decide

theorem linear_of_wellFormed {instruction : Instr} (wf : instruction.wellFormed = true)
    (notCall : ∀ target, instruction ≠ .call target) (notRuntime : ∀ intrinsic, instruction ≠ .callRuntime intrinsic) :
    linearInstruction instruction = true := by
  cases instruction with
  | op o args =>
      obtain ⟨row, linear, _⟩ := wellFormed_op wf
      have free := List.all_eq_true.mp table_flagsFree o row
      simp only [linear, Bool.not_true, Bool.false_or] at free
      simp [linearInstruction, linear, free]
  | call target => exact absurd rfl (notCall target)
  | callRuntime intrinsic => exact absurd rfl (notRuntime intrinsic)

/-- A row that declares no input flags computes the same core from any flags. -/
theorem exec_flagsFree {o : Op} (free : (desc o).flagsIn = []) (args : List Arg) (core : Core)
    (flags : ByteEval.Flags) :
    o.exec args core flags =
      (o.run args core {}).map fun result => (result.1, flags.merge (desc o).flagsOut result.2.flags) := by
  unfold Op.exec
  rw [free, ByteEval.restrict_nil]
  cases o.run args core {} <;> rfl

theorem execute_linear {o : Op} (linear : o.linear = true) (args : List Arg) (length : Nat)
    (state : ByteEval.State) :
    ByteEval.execute ⟨.op o args, length⟩ state =
      match o.exec args state.core state.flags with
      | .ok (core, flags) => .ok { core, rip := state.rip + UInt64.ofNat length, flags }
      | .error fault => .error (ByteEval.Fault.ofExec fault) := by
  unfold ByteEval.execute
  cases hmn : o.mn <;> simp only [Op.linear, hmn, Bool.false_eq_true] at linear
  all_goals
    simp only [hmn]
    cases o.exec args state.core state.flags <;> rfl

def LinearAgreement (before after : Machine) : Except ByteEval.Fault ByteEval.State → Prop
  | .ok state => after = before.advanceWith state.core
  | .error (.memory fault) => after = before.trap (.memoryFault fault)
  | .error (.undefinedCondition condition) => after = before.trap (.semantic (.undefinedCondition condition))
  | .error .divideError => after = before.trap (.semantic .divideError)
  | .error (.decode _) => False

/-- One generic execution law for every linear row: the byte machine's
step and the typed step agree on the core or raise the same fault. RIP,
length and the byte machine's flags are arbitrary. -/
theorem row_execution {o : Op} (linear : o.linear = true) (free : (desc o).flagsIn = []) (args : List Arg)
    (runtime : Runtime) (checked : Checked) (machine : Machine)
    (rip : Word) (flags : ByteEval.Flags) (length : Nat) :
    LinearAgreement machine (executeInstr runtime checked (.op o args) machine)
      (ByteEval.execute ⟨.op o args, length⟩ ⟨machine.core, rip, flags⟩) := by
  rw [execute_linear linear]
  simp only [executeInstr]
  rw [exec_flagsFree free, exec_flagsFree free]
  cases o.run args machine.core {} with
  | ok result => rfl
  | error fault =>
      cases fault with
      | memory fault => rfl
      | semantic fault =>
          cases fault <;> rfl

theorem instruction_execution (instruction : Instr) (linear : linearInstruction instruction = true)
    (runtime : Runtime) (checked : Checked) (machine : Machine)
    (rip : Word) (flags : ByteEval.Flags) (length : Nat) :
    LinearAgreement machine (executeInstr runtime checked instruction machine)
      (ByteEval.execute ⟨instructionOperation instruction, length⟩ ⟨machine.core, rip, flags⟩) := by
  cases instruction with
  | op o args =>
      simp only [linearInstruction, Bool.and_eq_true, List.isEmpty_iff] at linear
      exact row_execution linear.1 linear.2 args runtime checked machine rip flags length
  | call target | callRuntime intrinsic => simp [linearInstruction] at linear

/-- The execution theorem consumes the actual encoder bytes, surrounded by
arbitrary bytes. The explicit boundary is a premise for this local E1 result. -/
theorem encoded_instruction_execution (instruction : Instr)
    (linear : linearInstruction instruction = true) (wf : instruction.wellFormed = true)
    (before after : ByteArray)
    (runtime : Runtime) (checked : Checked) (machine : Machine) (flags : ByteEval.Flags)
    (textBase rip : Word) (boundary : (rip - textBase).toNat = before.size) :
    LinearAgreement machine (executeInstr runtime checked instruction machine)
      (ByteEval.step (before ++ (encodeInstr instruction).bytes ++ after) textBase
        ⟨machine.core, rip, flags⟩) := by
  rw [ByteEval.step, boundary, instruction_decodeAt instruction wf]
  exact instruction_execution instruction linear runtime checked machine rip flags _

/-- The emitted `cmp` row leaves the core unchanged and produces flags
under which the condition tests to the typed comparison's outcome. -/
theorem compare_execution (comparison : Compare) (condition : Condition)
    (state : ByteEval.State) (length : Nat) :
    let next := ByteEval.execute ⟨.op comparison.row.1 comparison.row.2, length⟩ state
    ∃ after, next = .ok after ∧ after.core = state.core ∧
      after.rip = state.rip + UInt64.ofNat length ∧
      after.flags.test condition = some (comparison.holds condition state.core) := by
  have linear := Compare.row_linear comparison
  refine ⟨⟨state.core, state.rip + UInt64.ofNat length, comparison.flags state.core⟩,
    by rw [execute_linear linear, Compare.exec_eq, Compare.flags_eq], rfl, rfl, ?_⟩
  exact Compare.flags_test comparison condition state.core

end Compilatrix.X86.Encode
