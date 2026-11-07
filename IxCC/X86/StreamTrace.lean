import IxCC.X86.StreamCalls

/-! Concrete compiler/ABI conditions for composing internal calls. Safety
mentions only typed memory accesses, active frames and the deterministic
mask of return-slot differences. It contains no byte-execution premise. -/

namespace IxCC.X86.Stream

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

def holeStep (program : Program) (machine : Machine) (holes : Holes) : Holes :=
  match program.blocks[machine.pc.block.toNat]? with
  | none => holes
  | some block =>
      match block.instructions[machine.pc.offset.toNat]? with
      | some (.call _) => addRange holes (machine.core.readReg .rsp - 8) 8
      | some (.fused _ _ consumer cargs) => nextHoles holes (.op consumer cargs) machine.core
      | some instruction => nextHoles holes (Encode.instructionOperation instruction) machine.core
      | none => terminatorHoles holes block.terminator machine.core

def SafeAt (program : Program) (holes : Holes) (machine : Machine) : Prop :=
  match program.blocks[machine.pc.block.toNat]? with
  | none => False
  | some block =>
      match block.instructions[machine.pc.offset.toNat]? with
      | some (.call _) =>
          SysV.callSiteAligned (machine.core.readReg .rsp) = true ∧
          Memory.rangeAllowed machine.core.memory.writable (machine.core.readReg .rsp - 8) 8 = true ∧
          FramesDisjoint machine.returns (machine.core.readReg .rsp - 8) 8
      | some (.callRuntime _) => False
      | some (.fused producer pargs consumer cargs) =>
          OperationSafe holes machine.returns (.op producer pargs) machine.core ∧
            OperationSafe holes machine.returns (.op consumer cargs) machine.core
      | some instruction => OperationSafe holes machine.returns (Encode.instructionOperation instruction) machine.core
      | none =>
          machine.pc.offset.toNat = block.instructions.size ∧
          match block.terminator with
          | .ret =>
              match machine.returns with
              | [] => ReadableData holes (machine.core.readReg .rsp) 8
              | frame :: _ =>
                  machine.core.readReg .rsp = frame.returnSlot ∧
                  machine.core.memory.read64? frame.returnSlot = .ok frame.continuation.encode ∧
                  machine.core.calleeSavedMatch frame.calleeSaved = true
          | .branch producer args _ _ _ _ => OperationSafe holes machine.returns (.op producer args) machine.core
          | .jump _ | .tailCall _ => True

def SafeTrace (runtime : Runtime) (checked : Checked) : Nat → Holes → Machine → Prop
  | 0, _, _ => True
  | count + 1, holes, machine =>
      SafeAt checked.program holes machine ∧
      match (step runtime checked machine).status with
      | .running => SafeTrace runtime checked count (holeStep checked.program machine holes) (step runtime checked machine)
      | _ => True

theorem safe_progress {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (base : Word) (holes : Holes) (state : ByteEval.State) (related : Related checked.program base holes machine state)
    (safe : SafeAt checked.program holes machine)
    (nextRunning : (step runtime checked machine).status = .running) :
    ∃ count after, 0 < count ∧ count ≤ 3 ∧ ByteEval.run output.text base count state = .ok after ∧
      Related checked.program base (holeStep checked.program machine holes) (step runtime checked machine) after := by
  obtain ⟨offset, mapped, _⟩ := related.pc
  obtain ⟨block, found, bound, _⟩ := pcOffset_info mapped
  cases foundInstruction : block.instructions[machine.pc.offset.toNat]? with
  | some instruction =>
      by_cases linear : Encode.linearInstruction instruction = true
      · have access : OperationSafe holes machine.returns (Encode.instructionOperation instruction) machine.core := by
          cases instruction <;> simp_all [SafeAt, Encode.linearInstruction]
        have changed : holeStep checked.program machine holes =
            nextHoles holes (Encode.instructionOperation instruction) machine.core := by
          cases instruction <;> simp_all [holeStep, Encode.linearInstruction]
        obtain ⟨after, executed, next⟩ := paired_linear_progress valid runtime machine base holes state related
          found foundInstruction linear access nextRunning
        exact ⟨1, after, by decide, by decide, by simp [ByteEval.run, executed], changed.symm ▸ next⟩
      · cases instruction
        case op o args => exact absurd (checked_linear found foundInstruction) linear
        case call target =>
          simp only [SafeAt, found, foundInstruction] at safe
          obtain ⟨after, executed, next⟩ := call_progress valid runtime machine base holes state related
            found foundInstruction safe.1 safe.2.1 safe.2.2
          refine ⟨1, after, by decide, by decide, by simp [ByteEval.run, executed], ?_⟩
          simpa only [holeStep, found, foundInstruction] using next
        case callRuntime intrinsic => simp [SafeAt, found, foundInstruction] at safe
        case fused producer pargs consumer cargs =>
          simp only [SafeAt, found, foundInstruction] at safe
          obtain ⟨after, executed, next⟩ := fused_progress valid runtime machine base holes state related
            found foundInstruction safe.1 safe.2 nextRunning
          refine ⟨2, after, by decide, by decide, executed, ?_⟩
          simpa only [holeStep, found, foundInstruction] using next
        case unwind source =>
          simp only [SafeAt, found, foundInstruction] at safe
          have data : ReadableData holes (source.eval machine.core) 8 :=
            safe.1 ⟨source.eval machine.core, 8⟩ (by simp)
          obtain ⟨after, executed, next⟩ := unwind_progress valid runtime machine base holes state related
            found foundInstruction data nextRunning
          refine ⟨1, after, by decide, by decide, by simp [ByteEval.run, executed], ?_⟩
          have unchanged : holeStep checked.program machine holes = holes := by
            simp [holeStep, found, foundInstruction, nextHoles, clearAccesses]
          rwa [unchanged]
  | none =>
      simp only [SafeAt, found, foundInstruction] at safe
      by_cases term : block.terminator = .ret
      · have access := safe.2
        rw [term] at access
        cases returns : machine.returns with
        | nil =>
            simp [source_terminator runtime machine related.running found safe.1, term,
              executeTerminator, returns] at nextRunning
        | cons frame rest =>
            simp only [returns] at access
            obtain ⟨after, executed, next⟩ := ret_progress valid runtime machine base holes state related
              found safe.1 term frame rest returns access.1 access.2.1 access.2.2
            refine ⟨1, after, by decide, by decide, by simp [ByteEval.run, executed], ?_⟩
            simpa only [holeStep, found, foundInstruction, term, terminatorHoles] using next
      · have access : TerminatorSafe holes machine.returns block.terminator machine.core := by
          have terminatorSafe := safe.2
          cases hterm : block.terminator <;> simp_all [TerminatorSafe]
        obtain ⟨count, after, positive, countBound, executed, next⟩ :=
          paired_control_progress valid runtime machine base holes state related found safe.1 term access nextRunning
        refine ⟨count, after, positive, countBound, executed, ?_⟩
        simpa only [holeStep, found, foundInstruction] using next

theorem instruction_not_halted (runtime : Runtime) (checked : Checked) (machine : Machine)
    (running : machine.status = .running) (instruction : Instr) (result : Word) :
    (executeInstr runtime checked instruction machine).status ≠ .halted result := by
  intro halted
  cases next : machine.pc.next? <;> cases instruction <;> simp only [executeInstr, Machine.afterRow] at halted
  all_goals (repeat' split at halted) <;> simp_all [Machine.advanceWith, Machine.trap]

theorem halting_shape {checked : Checked} (runtime : Runtime) (machine : Machine)
    (running : machine.status = .running) {result : Word}
    (halted : (step runtime checked machine).status = .halted result) :
    ∃ block, checked.program.blocks[machine.pc.block.toNat]? = some block ∧
      machine.pc.offset.toNat = block.instructions.size ∧ block.terminator = .ret ∧
      machine.returns = [] ∧ (step runtime checked machine).core = machine.core := by
  cases found : checked.program.blocks[machine.pc.block.toNat]? with
  | none => simp [step, running, found, Machine.trap] at halted
  | some block =>
      cases foundInstruction : block.instructions[machine.pc.offset.toNat]? with
      | some instruction =>
          have one : step runtime checked machine = executeInstr runtime checked instruction machine := by
            simp [step, running, found, foundInstruction]
          exact False.elim (instruction_not_halted runtime checked machine running instruction result (one ▸ halted))
      | none =>
          by_cases position : machine.pc.offset.toNat = block.instructions.size
          · have one := source_terminator runtime machine running found position
            have gotoStatus (target : BlockId) : (machine.goto checked target).status ≠ .halted result := by
              unfold Machine.goto
              split <;> simp [Machine.trap, running]
            cases term : block.terminator with
            | jump target | tailCall target =>
                simp only [one, term, executeTerminator] at halted
                exact False.elim (gotoStatus _ halted)
            | branch producer args condition yes no reach =>
                rw [one, term] at halted
                exact False.elim (branch_not_halted checked machine running producer args condition yes no reach result halted)
            | ret =>
                cases returns : machine.returns with
                | nil => exact ⟨block, rfl, position, term, rfl, by simp [one, term, executeTerminator, returns]⟩
                | cons frame rest =>
                    simp only [one, term, executeTerminator, returns] at halted
                    (repeat' split at halted) <;> simp_all [Machine.trap]
          · simp [step, running, found, foundInstruction, position, Machine.trap] at halted

theorem final_ret {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (base : Word) (holes : Holes) (state : ByteEval.State) (related : Related checked.program base holes machine state)
    (safe : SafeAt checked.program holes machine) {result returnAddress : Word}
    (halted : (step runtime checked machine).status = .halted result)
    (slot : (step runtime checked machine).core.memory.read64?
      ((step runtime checked machine).core.readReg .rsp) = .ok returnAddress) :
    ∃ after, ByteEval.step output.text base state = .ok after ∧ after.rip = returnAddress ∧
      CoreRelated checked.program base holes []
        ((step runtime checked machine).core.setReg .rsp ((step runtime checked machine).core.readReg .rsp + 8)) after.core := by
  obtain ⟨block, found, position, term, returns, coreEqual⟩ := halting_shape runtime machine related.running halted
  have none : block.instructions[machine.pc.offset.toNat]? = none := by simp [position]
  have data : ReadableData holes (machine.core.readReg .rsp) 8 := by
    simpa [SafeAt, found, none, term, returns, position] using safe
  rw [coreEqual] at slot
  have readEqual := related.core.memory.read? .w64 (machine.core.readReg .rsp) data
  have physicalRead : state.core.memory.read64? (state.core.readReg .rsp) = .ok returnAddress := by
    rw [← related.core.readReg .rsp]
    change state.core.memory.read? .w64 (machine.core.readReg .rsp) = .ok returnAddress
    rw [← readEqual]
    exact slot
  have decode := valid.terminator _ _ found
  simp only [term, terminatorMatches, decodes, beq_iff_eq] at decode
  have address := related.pc.offset found (by omega)
  rw [position] at address
  have bound := terminator_bound found
  have textBound := valid.textBound
  rw [term] at bound
  have one := step_decoded address (by simp only [terminatorSize] at bound; omega) decode
  let after : ByteEval.State := ⟨state.core.setReg .rsp (state.core.readReg .rsp + 8), returnAddress, state.flags⟩
  refine ⟨after, ?_, rfl, ?_⟩
  · rw [one]
    simp [Encode.execute_ret, physicalRead, after]
  · change CoreRelated _ _ _ _ _ (state.core.setReg .rsp (state.core.readReg .rsp + 8))
    rw [coreEqual, ← related.core.readReg .rsp, ← returns]
    exact related.core.setReg .rsp _

/-- Complete terminating streams with direct calls and tail calls. The
residual mask precisely limits data-memory observations after return; every
ordinary byte outside it and all registers (with RET's RSP adjustment) agree. -/
theorem run_with_calls {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (base : Word)
    (fuel : Nat) (holes : Holes) (machine : Machine) (state : ByteEval.State)
    (related : Related checked.program base holes machine state) (safe : SafeTrace runtime checked fuel holes machine)
    {after : Machine} {result returnAddress : Word}
    (execution : run runtime checked fuel machine = after) (halted : after.status = .halted result)
    (slot : after.core.memory.read64? (after.core.readReg .rsp) = .ok returnAddress) :
    ∃ count finalHoles finalState, 0 < count ∧ count ≤ 3 * fuel ∧
      ByteEval.run output.text base count state = .ok finalState ∧ finalState.rip = returnAddress ∧
      CoreRelated checked.program base finalHoles [] (after.core.setReg .rsp (after.core.readReg .rsp + 8)) finalState.core := by
  induction fuel generalizing holes machine state with
  | zero =>
      have same : machine = after := execution
      rw [← same, related.running] at halted
      contradiction
  | succ fuel ih =>
      rw [run_succ] at execution
      obtain ⟨safeAt, restSafe⟩ := safe
      cases nextStatus : (step runtime checked machine).status with
      | running =>
          obtain ⟨first, middle, positive, bound, one, next⟩ :=
            safe_progress valid runtime machine base holes state related safeAt nextStatus
          simp only [nextStatus] at restSafe
          obtain ⟨rest, finalHoles, finalState, restPositive, restBound, remaining, returned, core⟩ :=
            ih _ _ _ next restSafe execution
          refine ⟨first + rest, finalHoles, finalState, by omega, by omega, ?_, returned, core⟩
          rw [byte_run_add, one]
          exact remaining
      | trapped fault =>
          rw [run_of_not_running _ _ _ _ (by simp [nextStatus])] at execution
          rw [← execution, nextStatus] at halted
          contradiction
      | halted value =>
          rw [run_of_not_running _ _ _ _ (by simp [nextStatus])] at execution
          obtain ⟨finalState, last, returned, core⟩ := final_ret valid runtime machine base holes state related safeAt
            nextStatus (execution ▸ slot)
          exact ⟨1, holes, finalState, by decide, by omega, by simp [ByteEval.run, last], returned, execution ▸ core⟩

end IxCC.X86.Stream
