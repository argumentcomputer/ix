import Compilatrix.X86.StreamMemory

/-! Ordinary typed instructions cannot change page/byte permissions. This
connects a caller's entry-time return-slot read to the final physical RET. -/

namespace Compilatrix.X86.Stream

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

def Permissions (before after : Core) : Prop :=
  after.memory.readable = before.memory.readable ∧ after.memory.writable = before.memory.writable

theorem Permissions.refl (core : Core) : Permissions core core := ⟨rfl, rfl⟩

theorem Permissions.trans {first second third : Core} (left : Permissions first second)
    (right : Permissions second third) : Permissions first third :=
  ⟨right.1.trans left.1, right.2.trans left.2⟩

theorem store_permissions {before core after : Core} {width : Width} {value : Word} {arg : Arg}
    (stored : arg.store before width value core = .ok after) : Permissions core after := by
  cases arg with
  | reg register =>
      cases stored
      cases width <;> exact ⟨rfl, rfl⟩
  | imm immediate =>
      cases stored
      exact Permissions.refl _
  | mem address =>
      simp only [Arg.store, Memory.write?] at stored
      split at stored
      · cases stored
        simp [Permissions, Memory.write]
      · cases stored

theorem write_permissions {memory after : Memory} {width : Width} {address value : Word}
    (written : memory.write? width address value = .ok after) :
    after.readable = memory.readable ∧ after.writable = memory.writable := by
  unfold Memory.write? at written
  split at written
  · cases written
    simp [Memory.write]
  · cases written

theorem writeSlots_permissions (before : Core) (slots : List Slot) (args : List Arg) (results : List Word) :
    ∀ {core after : Core}, writeSlots before core slots args results = .ok after → Permissions core after := by
  induction slots generalizing args results with
  | nil =>
      intro core after written
      cases args <;> (cases written; exact Permissions.refl _)
  | cons slot slots ih =>
      intro core after written
      cases args with
      | nil => cases written; exact Permissions.refl _
      | cons arg args =>
          unfold writeSlots at written
          cases hrole : slot.role <;> rw [hrole] at written
          case read | address => exact ih args results written
          all_goals
            cases hstore : arg.store before slot.width (results.headD 0) core with
            | error fault =>
                rw [hstore] at written
                cases written
            | ok middle =>
                rw [hstore] at written
                exact (store_permissions hstore).trans (ih args results.tail written)

theorem stage_permissions {o : Op} {core after : Core} {out : SemOut}
    (staged : o.stage core out = .ok after) : Permissions core after := by
  unfold Op.stage at staged
  cases hstack : (desc o).stack <;> rw [hstack] at staged
  · cases staged
    exact Permissions.refl _
  · cases hwrite : core.memory.write64? (core.readReg .rsp - 8) (out.results.headD 0) with
    | error fault =>
        rw [hwrite] at staged
        cases staged
    | ok memory =>
        rw [hwrite] at staged
        cases staged
        exact write_permissions hwrite
  · cases staged
    exact ⟨rfl, rfl⟩

theorem run_permissions_row {o : Op} {args : List Arg} {core after : Core} {observed : ByteEval.Flags}
    {out : SemOut} (ran : o.run args core observed = .ok (after, out)) : Permissions core after := by
  unfold Op.run at ran
  cases hinputs : o.inputs args core with
  | error fault => simp [hinputs, Except.mapError] at ran
  | ok inputs =>
    cases hsem : (desc o).sem ⟨inputs, observed⟩ with
    | error fault => simp [hinputs, hsem, Except.mapError] at ran
    | ok result =>
      cases hstage : o.stage core result with
      | error fault => simp [hinputs, hsem, hstage, Except.mapError] at ran
      | ok staged =>
        cases hwrite : writeSlots core staged (desc o).slots args result.results with
        | error fault => simp [hinputs, hsem, hstage, hwrite, Except.mapError] at ran
        | ok final =>
          simp [hinputs, hsem, hstage, hwrite, Except.mapError] at ran
          obtain ⟨rfl, rfl⟩ := ran
          exact (stage_permissions hstage).trans (writeSlots_permissions core _ args _ hwrite)

theorem exec_ok {o : Op} {args : List Arg} {core after : Core} {flags flagsAfter : ByteEval.Flags}
    (executed : o.exec args core flags = .ok (after, flagsAfter)) :
    ∃ out, o.run args core (flags.restrict (desc o).flagsIn) = .ok (after, out) := by
  unfold Op.exec at executed
  cases hran : o.run args core (flags.restrict (desc o).flagsIn) with
  | error fault => simp [hran] at executed
  | ok result =>
      simp only [hran] at executed
      cases executed
      exact ⟨_, rfl⟩

theorem linear_permissions (runtime : Runtime) (checked : Checked) (machine : Machine)
    (instruction : Instr) (linear : Encode.linearInstruction instruction = true) :
    Permissions machine.core (executeInstr runtime checked instruction machine).core := by
  cases instruction with
  | op o args =>
      show Permissions machine.core (machine.afterRow (o.exec args machine.core {})).core
      cases hexec : o.exec args machine.core {} with
      | error fault =>
          cases fault <;> exact Permissions.refl _
      | ok result =>
          obtain ⟨after, flagsAfter⟩ := result
          obtain ⟨out, ran⟩ := exec_ok hexec
          have permissions := run_permissions_row ran
          show Permissions machine.core (machine.advanceWith after).core
          unfold Machine.advanceWith
          split
          · exact Permissions.refl _
          · exact permissions
  | call target | callRuntime intrinsic => simp [Encode.linearInstruction] at linear

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

end Compilatrix.X86.Stream
