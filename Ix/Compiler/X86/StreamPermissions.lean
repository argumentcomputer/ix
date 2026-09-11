import Ix.Compiler.X86.StreamMemory

/-! Ordinary typed instructions cannot change page/byte permissions. This
connects a caller's entry-time return-slot read to the final physical RET. -/

namespace Ix.Compiler.X86.Stream

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

def Permissions (before after : Core) : Prop :=
  after.memory.readable = before.memory.readable ∧ after.memory.writable = before.memory.writable

theorem linear_permissions (runtime : Runtime) (checked : Checked) (machine : Machine)
    (instruction : Instr) (linear : Encode.linearInstruction instruction = true) :
    Permissions machine.core (executeInstr runtime checked instruction machine).core := by
  cases next : machine.pc.next? <;> cases instruction <;>
    simp_all only [Encode.linearInstruction, Bool.false_eq_true]
  all_goals simp only [executeInstr, Core.loadReg?, Core.storeReg?, Memory.read64?, Memory.write64?, Memory.read?, Memory.write?]
  all_goals (repeat' split) <;>
    simp_all [Permissions, Machine.advanceWith, Machine.trap, Memory.write, Core.setReg, Core.writeReg]
  all_goals (repeat' split at *) <;> simp_all
  all_goals subst_vars <;> simp

theorem terminator_memory (checked : Checked) (machine : Machine) (terminator : Terminator) :
    (executeTerminator checked terminator machine).core.memory = machine.core.memory := by
  cases terminator <;> simp only [executeTerminator, Machine.goto]
  all_goals (repeat' split) <;> rfl

theorem step_permissions (runtime : Runtime) (checked : Checked) (free : CallFree checked.program) (machine : Machine) :
    Permissions machine.core (step runtime checked machine).core := by
  cases running : machine.status with
  | halted _ | trapped _ => simp [step, running, Permissions]
  | running =>
      cases found : checked.program.blocks[machine.pc.block.toNat]? with
      | none => simp [step, running, found, Machine.trap, Permissions]
      | some block =>
          cases foundInstruction : block.instructions[machine.pc.offset.toNat]? with
          | some instruction =>
              simpa [step, running, found, foundInstruction] using
                linear_permissions runtime checked machine instruction (free _ _ found _ _ foundInstruction)
          | none =>
              simp only [step, running, found, foundInstruction]
              split
              · simp [Permissions, terminator_memory]
              · simp [Permissions, Machine.trap]

theorem run_permissions (runtime : Runtime) (checked : Checked) (free : CallFree checked.program) (fuel : Nat) (machine : Machine) :
    Permissions machine.core (run runtime checked fuel machine).core := by
  induction fuel generalizing machine with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
      rw [run_succ]
      have first := step_permissions runtime checked free machine
      have rest := ih (step runtime checked machine)
      exact ⟨rest.1.trans first.1, rest.2.trans first.2⟩

end Ix.Compiler.X86.Stream
