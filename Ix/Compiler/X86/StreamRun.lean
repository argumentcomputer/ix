import Ix.Compiler.X86.StreamControl
import Ix.Compiler.X86.Execution

/-! Complete terminating execution for call-free streams, including loops,
branches and the physical caller's return slot. Internal-call composition is
separate because typed and physical return-slot bytes are different. -/

namespace Ix.Compiler.X86.Stream

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

def CallFree (program : Program) : Prop :=
  ∀ (blockIndex : Nat) (block : Block), program.blocks[blockIndex]? = some block →
    ∀ (index : Nat) (instruction : Instr), block.instructions[index]? = some instruction →
      Encode.linearInstruction instruction = true

def callFree (program : Program) : Bool :=
  program.blocks.all (fun block => block.instructions.all Encode.linearInstruction)

theorem callFree_sound {program : Program} (accepted : callFree program = true) : CallFree program := by
  intro blockIndex block found index instruction foundInstruction
  obtain ⟨blockBound, blockEqual⟩ := Array.getElem?_eq_some_iff.mp found
  obtain ⟨indexBound, instructionEqual⟩ := Array.getElem?_eq_some_iff.mp foundInstruction
  have row := Array.all_eq_true.mp accepted blockIndex blockBound
  rw [blockEqual] at row
  have cell := Array.all_eq_true.mp row index indexBound
  simpa [instructionEqual] using cell

@[simp] theorem advance_returns (machine : Machine) (core : Core) :
    (machine.advanceWith core).returns = machine.returns := by
  unfold Machine.advanceWith
  split <;> rfl

theorem linear_returns (runtime : Runtime) (checked : Checked) (machine : Machine)
    (instruction : Instr) (linear : Encode.linearInstruction instruction = true) :
    (executeInstr runtime checked instruction machine).returns = machine.returns := by
  cases instruction <;> simp_all only [Encode.linearInstruction, Bool.false_eq_true]
  all_goals simp only [executeInstr]
  all_goals first | exact advance_returns _ _ | (split <;> simp [Machine.trap])

structure RunningAt (program : Program) (base : Word) (machine : Machine) (state : ByteEval.State) : Prop where
  core : state.core = machine.core
  running : machine.status = .running
  returns : machine.returns = []
  pc : AtPC program base machine.pc state.rip

theorem linear_progress {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (base : Word) (state : ByteEval.State) (related : RunningAt checked.program base machine state)
    {block : Block} {instruction : Instr}
    (found : checked.program.blocks[machine.pc.block.toNat]? = some block)
    (foundInstruction : block.instructions[machine.pc.offset.toNat]? = some instruction)
    (linear : Encode.linearInstruction instruction = true)
    (nextRunning : (step runtime checked machine).status = .running) :
    ∃ after, ByteEval.step output.text base state = .ok after ∧
      RunningAt checked.program base (step runtime checked machine) after := by
  have agreement := linear_step valid runtime machine related.running base state.rip state.flags
    related.pc found foundInstruction linear
  have stateEqual : ({ core := machine.core, rip := state.rip, flags := state.flags } : ByteEval.State) = state := by
    rw [← related.core]
  rw [stateEqual] at agreement
  have sourceStep : step runtime checked machine = executeInstr runtime checked instruction machine := by
    simp [step, related.running, found, foundInstruction]
  have returns : (step runtime checked machine).returns = [] := by
    rw [sourceStep, linear_returns runtime checked machine instruction linear, related.returns]
  cases evaluated : ByteEval.step output.text base state with
  | ok after =>
      simp only [evaluated, LinearResult] at agreement
      exact ⟨after, rfl, agreement.1.symm, agreement.2.1, returns, agreement.2.2⟩
  | error fault =>
      cases fault with
      | memory fault =>
          simp only [evaluated, LinearResult] at agreement
          rw [agreement] at nextRunning
          contradiction
      | decode rip | undefinedCondition condition => simp [evaluated, LinearResult] at agreement

theorem control_progress {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (base : Word) (state : ByteEval.State) (related : RunningAt checked.program base machine state)
    {block : Block} (found : checked.program.blocks[machine.pc.block.toNat]? = some block)
    (position : machine.pc.offset.toNat = block.instructions.size)
    (nextRunning : (step runtime checked machine).status = .running) :
    ∃ count after, 0 < count ∧ count ≤ 3 ∧ ByteEval.run output.text base count state = .ok after ∧
      RunningAt checked.program base (step runtime checked machine) after := by
  have sourceStep := source_terminator runtime machine related.running found position
  have address := related.pc.offset found (by omega)
  rw [position] at address
  have accepted := valid.terminator machine.pc.block.toNat block found
  have bound := terminator_bound found
  have textBound := valid.textBound
  cases term : block.terminator with
  | ret =>
      simp [sourceStep, term, executeTerminator, related.returns] at nextRunning
  | jump target | tailCall target =>
      rw [term] at accepted bound
      change targets _ _ _ .jump 5 target = true at accepted
      obtain ⟨targetBound, _, _⟩ := targets_sound accepted
      have jumped := jump_at accepted base state address (by simp only [terminatorSize] at bound; omega)
      have goEqual : step runtime checked machine = { machine with pc := ⟨target, 0⟩ } := by
        simp [sourceStep, term, executeTerminator, Machine.goto, hasBlock_of_bound targetBound]
      refine ⟨1, { state with rip := base + UInt64.ofNat (blockOffset checked.program target.toNat) },
        by decide, by decide, ?_, ?_⟩
      · simp [ByteEval.run, jumped]
      · rw [goEqual]
        exact ⟨related.core, related.running, related.returns, _, target_entry targetBound, rfl⟩
  | branch comparison condition yes no =>
      rw [term] at accepted bound
      have branched := branch_at accepted base state address (by simp only [terminatorSize] at bound; omega)
      have parts := accepted
      simp only [terminatorMatches, Bool.and_eq_true, and_assoc] at parts
      have yesBound := (targets_sound parts.2.1).1
      have noBound := (targets_sound parts.2.2).1
      have targetBound : (if comparison.holds condition state.core then yes else no).toNat < checked.program.blocks.size := by
        split <;> assumption
      have goEqual : step runtime checked machine =
          { machine with pc := ⟨if comparison.holds condition state.core then yes else no, 0⟩ } := by
        simp [sourceStep, term, executeTerminator, ← related.core, Machine.goto, hasBlock_of_bound targetBound]
      refine ⟨if comparison.holds condition state.core then 2 else 3, _, ?_, ?_, branched, ?_⟩
      · split <;> decide
      · split <;> decide
      · rw [goEqual]
        exact ⟨related.core, related.running, related.returns, _, target_entry targetBound, rfl⟩

theorem running_progress {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (free : CallFree checked.program)
    (runtime : Runtime) (machine : Machine) (base : Word) (state : ByteEval.State)
    (related : RunningAt checked.program base machine state)
    (nextRunning : (step runtime checked machine).status = .running) :
    ∃ count after, 0 < count ∧ count ≤ 3 ∧ ByteEval.run output.text base count state = .ok after ∧
      RunningAt checked.program base (step runtime checked machine) after := by
  obtain ⟨offset, mapped, _⟩ := related.pc
  obtain ⟨block, found, bound, _⟩ := pcOffset_info mapped
  cases foundInstruction : block.instructions[machine.pc.offset.toNat]? with
  | some instruction =>
      obtain ⟨after, evaluated, next⟩ := linear_progress valid runtime machine base state related found
        foundInstruction (free _ _ found _ _ foundInstruction) nextRunning
      exact ⟨1, after, by decide, by decide, by simp [ByteEval.run, evaluated], next⟩
  | none =>
      have position : machine.pc.offset.toNat = block.instructions.size := by
        have missing := Array.getElem?_eq_none_iff.mp foundInstruction
        omega
      exact control_progress valid runtime machine base state related found position nextRunning

theorem halting_ret {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (free : CallFree checked.program)
    (runtime : Runtime) (machine : Machine) (base : Word) (state : ByteEval.State)
    (related : RunningAt checked.program base machine state) {result : Word}
    (halted : (step runtime checked machine).status = .halted result) :
    (step runtime checked machine).core = machine.core ∧
      Decode.decodeAt output.text (state.rip - base).toNat = some ⟨.ret, 1⟩ := by
  obtain ⟨offset, mapped, _⟩ := related.pc
  obtain ⟨block, found, bound, offsetEqual⟩ := pcOffset_info mapped
  cases foundInstruction : block.instructions[machine.pc.offset.toNat]? with
  | some instruction =>
      have agreement := linear_step valid runtime machine related.running base state.rip state.flags
        related.pc found foundInstruction (free _ _ found _ _ foundInstruction)
      cases evaluated : ByteEval.step output.text base ⟨machine.core, state.rip, state.flags⟩ with
      | ok after => simp only [evaluated, LinearResult] at agreement; rw [agreement.2.1] at halted; contradiction
      | error fault =>
          cases fault with
          | memory fault =>
              simp only [evaluated, LinearResult] at agreement
              rw [agreement] at halted
              contradiction
          | decode rip | undefinedCondition condition => simp [evaluated, LinearResult] at agreement
  | none =>
      have position : machine.pc.offset.toNat = block.instructions.size := by
        have missing := Array.getElem?_eq_none_iff.mp foundInstruction
        omega
      have sourceStep := source_terminator runtime machine related.running found position
      have accepted := valid.terminator machine.pc.block.toNat block found
      have gotoStatus (target : BlockId) : (machine.goto checked target).status ≠ .halted result := by
        unfold Machine.goto
        split <;> simp [Machine.trap, related.running]
      cases term : block.terminator with
      | ret =>
          constructor
          · simp [sourceStep, term, executeTerminator, related.returns]
          · have address := related.pc.offset found bound
            rw [position] at address
            have small := AtPC.small valid.textBound mapped
            rw [offsetEqual, position] at small
            rw [address, rip_offset _ _ small]
            simpa [term, terminatorMatches, decodes, beq_iff_eq] using accepted
      | jump target | tailCall target =>
          simp only [sourceStep, term, executeTerminator] at halted
          exact False.elim (gotoStatus _ halted)
      | branch comparison condition yes no =>
          simp only [sourceStep, term, executeTerminator] at halted
          exact False.elim (gotoStatus _ halted)

theorem byte_run_add (text : ByteArray) (base : Word) (first second : Nat) (state : ByteEval.State) :
    ByteEval.run text base (first + second) state =
      (ByteEval.run text base first state >>= ByteEval.run text base second) := by
  induction first generalizing state with
  | zero => simp [ByteEval.run]
  | succ first ih =>
      rw [Nat.succ_add, ByteEval.run, ByteEval.run]
      cases ByteEval.step text base state <;> simp [ih]

/-- The physical RET consumes the caller's slot after the typed harness
halts. Every other register and every memory byte agree with the typed run. -/
def Returned (core : Core) (returnAddress : Word) (state : ByteEval.State) : Prop :=
  state.core = core.setReg .rsp (core.readReg .rsp + 8) ∧ state.rip = returnAddress

/-- A whole-stream theorem, quantified over every finite terminating run.
The return-slot premise is one concrete final memory read. No byte-step or
simulation callback is an input. -/
theorem run_to_return {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (free : CallFree checked.program)
    (runtime : Runtime) (base : Word) (fuel : Nat) (machine : Machine) (state : ByteEval.State)
    (related : RunningAt checked.program base machine state) {after : Machine} {result returnAddress : Word}
    (execution : run runtime checked fuel machine = after) (halted : after.status = .halted result)
    (slot : after.core.memory.read64? (after.core.readReg .rsp) = .ok returnAddress) :
    ∃ count finalState, 0 < count ∧ count ≤ 3 * fuel ∧
      ByteEval.run output.text base count state = .ok finalState ∧ Returned after.core returnAddress finalState := by
  induction fuel generalizing machine state with
  | zero =>
      have same : machine = after := execution
      rw [← same, related.running] at halted
      contradiction
  | succ fuel ih =>
      rw [run_succ] at execution
      cases nextStatus : (step runtime checked machine).status with
      | running =>
          obtain ⟨first, middle, positive, bound, one, next⟩ :=
            running_progress valid free runtime machine base state related nextStatus
          obtain ⟨rest, finalState, restPositive, restBound, remaining, returned⟩ := ih _ _ next execution
          refine ⟨first + rest, finalState, by omega, by omega, ?_, returned⟩
          rw [byte_run_add, one]
          exact remaining
      | trapped fault =>
          rw [run_of_not_running _ _ _ _ (by simp [nextStatus])] at execution
          rw [← execution, nextStatus] at halted
          contradiction
      | halted value =>
          rw [run_of_not_running _ _ _ _ (by simp [nextStatus])] at execution
          obtain ⟨coreEqual, fetched⟩ := halting_ret valid free runtime machine base state related nextStatus
          have stateCore : state.core = after.core := by rw [← execution, coreEqual]; exact related.core
          let finalState : ByteEval.State :=
            ⟨after.core.setReg .rsp (after.core.readReg .rsp + 8), returnAddress, state.flags⟩
          have last : ByteEval.step output.text base state = .ok finalState := by
            simp [ByteEval.step, fetched, ByteEval.execute, stateCore, slot, Except.mapError, finalState]
          exact ⟨1, finalState, by decide, by omega, by simp [ByteEval.run, last], rfl, rfl⟩

end Ix.Compiler.X86.Stream
