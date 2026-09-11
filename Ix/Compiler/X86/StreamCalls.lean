import Ix.Compiler.X86.StreamEffects

/-! Complete-text call and return effects, with bytewise return-slot
correspondence preserved across ordinary callee instructions. -/

namespace Ix.Compiler.X86.Stream

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

structure Related (program : Program) (base : Word) (holes : Holes) (machine : Machine) (state : ByteEval.State) : Prop where
  core : CoreRelated program base holes machine.returns machine.core state.core
  running : machine.status = .running
  pc : AtPC program base machine.pc state.rip

theorem paired_linear_progress {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (base : Word) (holes : Holes) (state : ByteEval.State) (related : Related checked.program base holes machine state)
    {block : Block} {instruction : Instr}
    (found : checked.program.blocks[machine.pc.block.toNat]? = some block)
    (foundInstruction : block.instructions[machine.pc.offset.toNat]? = some instruction)
    (linear : Encode.linearInstruction instruction = true)
    (safe : OperationSafe holes machine.returns (Encode.instructionOperation instruction) machine.core)
    (nextRunning : (step runtime checked machine).status = .running) :
    ∃ after, ByteEval.step output.text base state = .ok after ∧
      Related checked.program base (nextHoles holes (Encode.instructionOperation instruction) machine.core)
        (step runtime checked machine) after := by
  have fetched := fetch_linear valid base state.rip machine.pc related.pc found foundInstruction linear
  have agreement := linear_step valid runtime machine related.running base state.rip state.flags
    related.pc found foundInstruction linear
  simp only [ByteEval.step, fetched] at agreement
  have pair := operation_pair checked.program base state.rip state.flags holes machine.returns
    machine.core state.core related.core (Encode.instructionOperation instruction) (instructionSize instruction)
    (instruction_linear_operation instruction linear) safe
  have sourceStep : step runtime checked machine = executeInstr runtime checked instruction machine := by
    simp [step, related.running, found, foundInstruction]
  have returns : (step runtime checked machine).returns = machine.returns := by
    rw [sourceStep, linear_returns runtime checked machine instruction linear]
  cases logicalStep : ByteEval.execute ⟨Encode.instructionOperation instruction, instructionSize instruction⟩
      ⟨machine.core, state.rip, state.flags⟩ with
  | error fault =>
      cases fault with
      | memory fault =>
          simp only [logicalStep, LinearResult] at agreement
          rw [agreement] at nextRunning
          contradiction
      | decode rip | undefinedCondition condition => simp [logicalStep, LinearResult] at agreement
  | ok logicalAfter =>
      simp only [logicalStep, LinearResult] at agreement
      cases physicalStep : ByteEval.execute ⟨Encode.instructionOperation instruction, instructionSize instruction⟩ state with
      | error fault => simp [logicalStep, physicalStep, CorePair] at pair
      | ok physicalAfter =>
          simp only [logicalStep, physicalStep, CorePair] at pair
          have sameRip := (linear_rip instruction linear state (instructionSize instruction) physicalStep).trans
            (linear_rip instruction linear ⟨machine.core, state.rip, state.flags⟩
              (instructionSize instruction) logicalStep).symm
          refine ⟨physicalAfter, by simp [ByteEval.step, fetched, physicalStep], ?_⟩
          refine ⟨?_, nextRunning, ?_⟩
          · rw [returns, agreement.1]
            exact pair
          · rw [sameRip]
            exact agreement.2.2

theorem CoreRelated.comparison {program : Program} {base : Word} {holes : Holes} {frames : List ReturnFrame}
    {logical physical : Core} (related : CoreRelated program base holes frames logical physical)
    (comparison : Compare) (condition : Condition) :
    comparison.holds condition logical = comparison.holds condition physical := by
  have source : comparison.right.eval logical = comparison.right.eval physical := by
    cases comparison.right <;> simp [AluSource.eval, related.readReg]
  simp only [Compare.holds, related.readReg, source]

theorem paired_control_progress {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (base : Word) (holes : Holes) (state : ByteEval.State) (related : Related checked.program base holes machine state)
    {block : Block} (found : checked.program.blocks[machine.pc.block.toNat]? = some block)
    (position : machine.pc.offset.toNat = block.instructions.size) (notRet : block.terminator ≠ .ret) :
    ∃ count after, 0 < count ∧ count ≤ 3 ∧ ByteEval.run output.text base count state = .ok after ∧
      Related checked.program base holes (step runtime checked machine) after := by
  have sourceStep := source_terminator runtime machine related.running found position
  have address := related.pc.offset found (by omega)
  rw [position] at address
  have accepted := valid.terminator machine.pc.block.toNat block found
  have bound := terminator_bound found
  have textBound := valid.textBound
  cases term : block.terminator with
  | ret => exact False.elim (notRet term)
  | jump target | tailCall target =>
      rw [term] at accepted bound
      change targets _ _ _ .jump 5 target = true at accepted
      have targetBound := (targets_sound accepted).1
      have jumped := jump_at accepted base state address (by simp only [terminatorSize] at bound; omega)
      have goEqual : step runtime checked machine = { machine with pc := ⟨target, 0⟩ } := by
        simp [sourceStep, term, executeTerminator, Machine.goto, hasBlock_of_bound targetBound]
      refine ⟨1, { state with rip := base + UInt64.ofNat (blockOffset checked.program target.toNat) },
        by decide, by decide, by simp [ByteEval.run, jumped], ?_⟩
      rw [goEqual]
      exact ⟨related.core, related.running, _, target_entry targetBound, rfl⟩
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
        simp [sourceStep, term, executeTerminator, related.core.comparison comparison condition,
          Machine.goto, hasBlock_of_bound targetBound]
      refine ⟨if comparison.holds condition state.core then 2 else 3, _, ?_, ?_, branched, ?_⟩
      · split <;> decide
      · split <;> decide
      · rw [goEqual]
        exact ⟨related.core, related.running, _, target_entry targetBound, rfl⟩

theorem call_progress {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (base : Word) (holes : Holes) (state : ByteEval.State) (related : Related checked.program base holes machine state)
    {block : Block} {target : BlockId}
    (found : checked.program.blocks[machine.pc.block.toNat]? = some block)
    (foundInstruction : block.instructions[machine.pc.offset.toNat]? = some (.call target))
    (aligned : SysV.callSiteAligned (machine.core.readReg .rsp) = true)
    (writable : Memory.rangeAllowed machine.core.memory.writable (machine.core.readReg .rsp - 8) 8 = true)
    (disjoint : FramesDisjoint machine.returns (machine.core.readReg .rsp - 8) 8) :
    ∃ after, ByteEval.step output.text base state = .ok after ∧
      Related checked.program base (addRange holes (machine.core.readReg .rsp - 8) 8)
        (step runtime checked machine) after := by
  have accepted := valid.instruction _ _ found _ _ foundInstruction
  change targets _ _ _ .call 5 target = true at accepted
  obtain ⟨targetBound, fits, fetched⟩ := targets_sound accepted
  have indexBound := (Array.getElem?_eq_some_iff.mp foundInstruction).1
  have address := related.pc.offset found (by omega)
  have mapped : pcOffset? checked.program machine.pc =
      some (blockOffset checked.program machine.pc.block.toNat + instructionOffset block machine.pc.offset.toNat) := by
    simp [pcOffset?, found, show machine.pc.offset.toNat ≤ block.instructions.size by omega]
  have physicalFetch := step_decoded address (AtPC.small valid.textBound mapped) fetched
  have next := pc_next found foundInstruction
  have continuation := pcOffset_next found foundInstruction
  have size : instructionSize (.call target) = 5 := rfl
  rw [size] at continuation
  let nextOffset := blockOffset checked.program machine.pc.block.toNat + instructionOffset block machine.pc.offset.toNat + 5
  have nextAddress : state.rip + 5 = base + UInt64.ofNat nextOffset := by
    simp [nextOffset, address, UInt64.ofNat_add, UInt64.add_assoc]
  have resolved := Encode.relative_resolves_base base nextOffset (blockOffset checked.program target.toNat) fits
  have sourceStep : step runtime checked machine =
      Encode.typedCallState machine target { machine.pc with offset := machine.pc.offset + 1 } := by
    simp [step, related.running, found, foundInstruction, executeInstr, aligned, hasBlock_of_bound targetBound,
      next.1, Memory.write64?, Memory.write?, Width.bytes, writable, Encode.typedCallState, Memory.write64]
  let physicalAfter : ByteEval.State := {
    core := { state.core.setReg .rsp (machine.core.readReg .rsp - 8) with
      memory := state.core.memory.write64 (machine.core.readReg .rsp - 8) (state.rip + 5) }
    rip := base + UInt64.ofNat (blockOffset checked.program target.toNat), flags := state.flags }
  have physicalStep : ByteEval.step output.text base state = .ok physicalAfter := by
    rw [physicalFetch]
    simp only [ByteEval.execute, Memory.write64?, Memory.write?, Width.bytes, ← related.core.readReg .rsp,
      ← related.core.memory.writable, writable, ↓reduceIte, Except.mapError, bind, Except.bind, pure, Except.pure]
    change Except.ok ({ core := _, rip := ByteEval.relative (state.rip + 5) (displacement nextOffset (blockOffset checked.program target.toNat)), flags := state.flags } : ByteEval.State) = _
    rw [nextAddress]
    change Except.ok ({ core := _, rip := ByteEval.relative (base + UInt64.ofNat nextOffset) (Int32.ofInt ((blockOffset checked.program target.toNat : Int) - nextOffset)).toUInt32, flags := state.flags } : ByteEval.State) = _
    rw [resolved]
    rfl
  refine ⟨physicalAfter, physicalStep, ?_⟩
  rw [sourceStep]
  refine ⟨?_, related.running, _, target_entry targetBound, rfl⟩
  refine ⟨(related.core.setReg .rsp _).registers, ?_, ?_⟩
  · exact related.core.memory.write_different _ _ _ 8
  · intro frame member
    change frame ∈ _ :: machine.returns at member
    rcases List.mem_cons.mp member with equal | member
    · subst frame
      exact ⟨nextOffset, continuation, by simpa [physicalAfter, Memory.read64_write64] using nextAddress⟩
    · exact related.core.frames.write _ _ 8 disjoint frame member

theorem ret_progress {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (runtime : Runtime) (machine : Machine)
    (base : Word) (holes : Holes) (state : ByteEval.State) (related : Related checked.program base holes machine state)
    {block : Block} (found : checked.program.blocks[machine.pc.block.toNat]? = some block)
    (position : machine.pc.offset.toNat = block.instructions.size) (term : block.terminator = .ret)
    (frame : ReturnFrame) (rest : List ReturnFrame) (returns : machine.returns = frame :: rest)
    (stack : machine.core.readReg .rsp = frame.returnSlot)
    (typedRead : machine.core.memory.read64? frame.returnSlot = .ok frame.continuation.encode)
    (saved : machine.core.calleeSavedMatch frame.calleeSaved = true) :
    ∃ after, ByteEval.step output.text base state = .ok after ∧
      Related checked.program base holes (step runtime checked machine) after := by
  obtain ⟨offset, continuation, slot⟩ := related.core.frames frame (by simp [returns])
  have allowed : Memory.rangeAllowed machine.core.memory.readable frame.returnSlot 8 = true := by
    by_cases allowed : Memory.rangeAllowed machine.core.memory.readable frame.returnSlot 8 = true
    · exact allowed
    · simp [Memory.read64?, Memory.read?, Width.bytes, allowed] at typedRead
  have physicalRead : state.core.memory.read64? frame.returnSlot = .ok (base + UInt64.ofNat offset) := by
    simp only [Memory.read64?, Memory.read?, ← related.core.memory.readable, Width.bytes, allowed, ↓reduceIte]
    exact congrArg Except.ok slot
  have sourceStep : step runtime checked machine =
      { machine with core := machine.core.setReg .rsp (frame.returnSlot + 8), pc := frame.continuation, returns := rest } := by
    rw [source_terminator runtime machine related.running found position, term]
    simp [executeTerminator, returns, stack, typedRead, saved]
  have fetched := valid.terminator _ _ found
  have decode : Decode.decodeAt output.text
      (blockOffset checked.program machine.pc.block.toNat + instructionOffset block block.instructions.size) =
      some ⟨.ret, 1⟩ := by
    simpa [term, terminatorMatches, decodes, beq_iff_eq] using fetched
  have address := related.pc.offset found (by omega)
  rw [position] at address
  have bound := terminator_bound found
  have textBound := valid.textBound
  rw [term] at bound
  have one := step_decoded address (by simp only [terminatorSize] at bound; omega) decode
  let after : ByteEval.State := ⟨state.core.setReg .rsp (frame.returnSlot + 8), base + UInt64.ofNat offset, state.flags⟩
  have executed : ByteEval.step output.text base state = .ok after := by
    rw [one]
    simp [ByteEval.execute, ← related.core.readReg .rsp, stack, physicalRead, Except.mapError, after]
  refine ⟨after, executed, ?_⟩
  rw [sourceStep]
  refine ⟨?_, related.running, offset, continuation, rfl⟩
  have core := related.core.setReg .rsp (frame.returnSlot + 8)
  refine ⟨core.registers, core.memory, ?_⟩
  intro remaining member
  exact core.frames remaining (by simp [returns, member])

end Ix.Compiler.X86.Stream
