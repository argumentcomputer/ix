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
  | .fused .. | .call _ | .callRuntime _ => false

theorem single_of_linear {instruction : Instr} (linear : linearInstruction instruction = true) :
    instruction.single = true := by
  cases instruction <;> simp_all [linearInstruction, Instr.single]

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
    (notCall : ∀ target, instruction ≠ .call target) (notRuntime : ∀ intrinsic, instruction ≠ .callRuntime intrinsic)
    (notFused : ∀ producer pargs consumer cargs, instruction ≠ .fused producer pargs consumer cargs) :
    linearInstruction instruction = true := by
  cases instruction with
  | op o args =>
      obtain ⟨row, linear, _⟩ := wellFormed_op wf
      have free := List.all_eq_true.mp table_flagsFree o row
      simp only [linear, Bool.not_true, Bool.false_or] at free
      simp [linearInstruction, linear, free]
  | fused producer pargs consumer cargs => exact absurd rfl (notFused producer pargs consumer cargs)
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

/-- A branch producer computes the same core from the typed machine's empty
flags as from the byte machine's, and the flags its condition reads agree:
the producer sets them all (`FusedOk`). -/
theorem produced_flags {producer : Op} {args : List Arg} {condition : Condition}
    (free : (desc producer).flagsIn = []) (fused : FusedOk producer (Op.jccRel32 condition) = true)
    {core after : Core} {typedFlags : ByteEval.Flags}
    (typed : producer.exec args core {} = .ok (after, typedFlags)) (flags : ByteEval.Flags) :
    ∃ byteFlags, producer.exec args core flags = .ok (after, byteFlags) ∧
      byteFlags.test condition = typedFlags.test condition := by
  rw [exec_flagsFree free] at typed ⊢
  cases hrun : producer.run args core {} with
  | error fault => simp [hrun] at typed
  | ok result =>
      simp only [hrun, Except.map, Except.ok.injEq, Prod.mk.injEq] at typed
      obtain ⟨rfl, rfl⟩ := typed
      refine ⟨_, rfl, ?_⟩
      exact ByteEval.test_merge_set (fun flag member => FusedOk.set fused flag (by simpa using member)) _ _ _

/-- The byte machine runs every non-control row through `Op.exec` on its
flags: linear rows and flag consumers alike. -/
theorem execute_row {o : Op} (control : o.control = false) (args : List Arg) (length : Nat)
    (state : ByteEval.State) :
    ByteEval.execute ⟨.op o args, length⟩ state =
      match o.exec args state.core state.flags with
      | .ok (core, flags) => .ok { core, rip := state.rip + UInt64.ofNat length, flags }
      | .error fault => .error (ByteEval.Fault.ofExec fault) := by
  unfold ByteEval.execute
  cases hmn : o.mn <;> simp only [Op.control, hmn, Bool.true_eq_false] at control
  all_goals
    simp only [hmn]
    cases o.exec args state.core state.flags <;> rfl

theorem _root_.Compilatrix.X86.Op.control_of_linear {o : Op} (linear : o.linear = true) : o.control = false := by
  unfold Op.linear at linear
  unfold Op.control
  split <;> simp_all

theorem _root_.Compilatrix.X86.Op.control_of_consumer {o : Op} (consumer : o.consumer = true) : o.control = false := by
  unfold Op.consumer at consumer
  unfold Op.control
  split <;> simp_all

theorem execute_linear {o : Op} (linear : o.linear = true) (args : List Arg) (length : Nat)
    (state : ByteEval.State) :
    ByteEval.execute ⟨.op o args, length⟩ state =
      match o.exec args state.core state.flags with
      | .ok (core, flags) => .ok { core, rip := state.rip + UInt64.ofNat length, flags }
      | .error fault => .error (ByteEval.Fault.ofExec fault) :=
  execute_row (Op.control_of_linear linear) args length state

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

/-- A consumer computes the same core and faults from any flags that agree
with its producer's on the flags it reads. -/
theorem consumer_flags {producer consumer : Op} (fused : FusedOk producer consumer = true)
    (args : List Arg) (core : Core) (before other computed : ByteEval.Flags) :
    (consumer.exec args core (before.merge (desc producer).flagsOut computed)).map (·.1) =
      (consumer.exec args core (other.merge (desc producer).flagsOut computed)).map (·.1) := by
  unfold Op.exec
  rw [ByteEval.restrict_merge_set (FusedOk.set fused) before other computed]
  cases consumer.run args core ((other.merge (desc producer).flagsOut computed).restrict (desc consumer).flagsIn) <;>
    rfl

/-- E1 for fused pairs: the byte machine's two steps (producer, then
consumer on the producer's flags) agree with the typed pair's one step on
the core, or raise the same fault. The consumer reads only flags the
producer sets (`FusedOk`), so the byte machine's earlier flags do not
matter. -/
theorem fused_execution {producer consumer : Op} {pargs cargs : List Arg}
    (wf : (Instr.fused producer pargs consumer cargs).wellFormed = true)
    (runtime : Runtime) (checked : Checked) (machine : Machine) (rip : Word) (flags : ByteEval.Flags)
    (producerLength consumerLength : Nat) :
    LinearAgreement machine (executeInstr runtime checked (.fused producer pargs consumer cargs) machine)
      (ByteEval.execute ⟨.op producer pargs, producerLength⟩ ⟨machine.core, rip, flags⟩ >>= fun middle =>
        ByteEval.execute ⟨.op consumer cargs, consumerLength⟩ middle) := by
  obtain ⟨_, linear, free, _, _, _, consumes, _, fused⟩ := wellFormed_fused wf
  rw [execute_linear linear]
  simp only [executeInstr]
  rw [exec_flagsFree free, exec_flagsFree free]
  cases hrun : producer.run pargs machine.core {} with
  | error fault =>
      cases fault with
      | memory fault => rfl
      | semantic fault => cases fault <;> rfl
  | ok result =>
      obtain ⟨core, out⟩ := result
      simp only [Except.map, bind, Except.bind]
      rw [execute_row (Op.control_of_consumer consumes)]
      have same := consumer_flags fused cargs core flags {} out.flags
      cases htyped : consumer.exec cargs core (({} : ByteEval.Flags).merge (desc producer).flagsOut out.flags) with
      | error fault =>
          cases hbyte : consumer.exec cargs core (flags.merge (desc producer).flagsOut out.flags) with
          | ok value => rw [htyped, hbyte] at same; cases same
          | error byteFault =>
              rw [htyped, hbyte] at same
              cases same
              cases fault with
              | memory fault => rfl
              | semantic fault => cases fault <;> rfl
      | ok value =>
          cases hbyte : consumer.exec cargs core (flags.merge (desc producer).flagsOut out.flags) with
          | error fault => rw [htyped, hbyte] at same; cases same
          | ok byteValue =>
              rw [htyped, hbyte] at same
              simp only [Except.map, Except.ok.injEq] at same
              simp only [Machine.afterRow, LinearAgreement, same]

theorem instruction_execution (instruction : Instr) (linear : linearInstruction instruction = true)
    (runtime : Runtime) (checked : Checked) (machine : Machine)
    (rip : Word) (flags : ByteEval.Flags) (length : Nat) :
    LinearAgreement machine (executeInstr runtime checked instruction machine)
      (ByteEval.execute ⟨instructionOperation instruction, length⟩ ⟨machine.core, rip, flags⟩) := by
  cases instruction with
  | op o args =>
      simp only [linearInstruction, Bool.and_eq_true, List.isEmpty_iff] at linear
      exact row_execution linear.1 linear.2 args runtime checked machine rip flags length
  | fused | call | callRuntime => simp [linearInstruction] at linear

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
  rw [ByteEval.step, boundary, instruction_decodeAt instruction wf (single_of_linear linear)]
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
