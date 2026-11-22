import IxCC.X86.SafeSteps
import IxCC.X86.ObjectExecution

namespace IxCC.X86.Stream

theorem SafeSteps.finished {runtime : Runtime} {checked : Checked} {count : Nat}
    {before after : Machine} {holes finalHoles : Holes}
    (steps : SafeSteps runtime checked count holes before finalHoles after)
    (finished : before.status ≠ .running)
    (fixed : ∀ mask, holeStep checked.program before mask = mask) :
    after = before ∧ finalHoles = holes := by
  induction steps with
  | refl => exact ⟨rfl, rfl⟩
  | @cons before middle after holes finalHoles count access first rest ih =>
      have same : middle = before := first.symm.trans (step_of_not_running _ _ _ finished)
      have result := ih (by simpa only [same] using finished) (by simpa only [same] using fixed)
      exact ⟨result.1.trans same, result.2.trans (fixed _)⟩

/-- Preserve the exact final return-slot mask of a compositional trace. -/
theorem SafeSteps.run_with_calls {runtime : Runtime} {checked : Checked} {count : Nat}
    {machine after : Machine} {holes finalHoles : Holes}
    (steps : SafeSteps runtime checked count holes machine finalHoles after)
    {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) (base : Word) (state : ByteEval.State)
    (related : Related checked.program base holes machine state)
    {result returnAddress : Word} (halted : after.status = .halted result)
    (slot : after.core.memory.read64? (after.core.readReg .rsp) = .ok returnAddress) :
    ∃ byteCount finalState, 0 < byteCount ∧ byteCount ≤ 3 * count ∧
      ByteEval.run output.text base byteCount state = .ok finalState ∧ finalState.rip = returnAddress ∧
      CoreRelated checked.program base finalHoles []
        (after.core.setReg .rsp (after.core.readReg .rsp + 8)) finalState.core := by
  induction steps generalizing state with
  | refl => rw [related.running] at halted; contradiction
  | @cons machine middle after holes finalHoles count access first rest ih =>
      cases status : middle.status with
      | running =>
          obtain ⟨leading, next, positive, bound, run, nextRelated⟩ :=
            safe_progress valid runtime machine base holes state related access (first ▸ status)
          rw [first] at nextRelated
          obtain ⟨trailing, finalState, trailingPositive, trailingBound, tailRun, returned, core⟩ := ih next nextRelated halted slot
          refine ⟨leading + trailing, finalState, by omega, by omega, ?_, returned, core⟩
          rw [byte_run_add, run]
          exact tailRun
      | trapped fault =>
          have same := rest.steps.run_eq
          rw [run_of_not_running _ _ _ _ (by simp [status])] at same
          rw [← same, status] at halted
          contradiction
      | halted value =>
          have middleHalted : (step runtime checked machine).status = .halted value := first ▸ status
          obtain ⟨block, found, position, term, returns, coreEqual⟩ := halting_shape runtime machine related.running middleHalted
          have absent : block.instructions[machine.pc.offset.toNat]? = none := by simp [position]
          have fixedBefore : ∀ mask, holeStep checked.program machine mask = mask := by
            simp [holeStep, found, absent, term, terminatorHoles]
          have pcSame : middle.pc = machine.pc := by
            rw [← first, source_terminator runtime machine related.running found position]
            simp [term, executeTerminator, returns]
          have fixedMiddle : ∀ mask, holeStep checked.program middle mask = mask := by
            simp [holeStep, pcSame, found, absent, term, terminatorHoles]
          obtain ⟨same, maskSame⟩ := rest.finished (by simp [status]) fixedMiddle
          have maskSame : finalHoles = holes := maskSame.trans (fixedBefore holes)
          obtain ⟨finalState, last, returned, core⟩ := final_ret valid runtime machine base holes state related access
            middleHalted (by simpa [first, same] using slot)
          refine ⟨1, finalState, by decide, by omega, by simp [ByteEval.run, last, bind, Except.bind], returned, ?_⟩
          simpa only [first, same, maskSame] using core

end IxCC.X86.Stream

namespace IxCC.X86.ObjectEval

theorem run_safeSteps {checked : Checked} {input : ELF.Input} {bytes : ByteArray}
    (stream : Stream.Valid checked.program input.encoded) (object : ELF.Valid input bytes)
    (entry : input.entryBlock = checked.program.entry)
    {runtime : Runtime} {count : Nat} (base : Word) (core : Core) (flags : ByteEval.Flags)
    {after : Machine} {holes : Stream.Holes} {result returnAddress : Word}
    (steps : Stream.SafeSteps runtime checked count (fun _ => False) (Machine.initial checked core) holes after)
    (halted : after.status = .halted result)
    (slot : after.core.memory.read64? (after.core.readReg .rsp) = .ok returnAddress) :
    ∃ byteCount finalState, 0 < byteCount ∧ byteCount ≤ 3 * count ∧
      run bytes input.exportName base byteCount core flags = .ok finalState ∧ finalState.rip = returnAddress ∧
      Stream.CoreRelated checked.program base holes []
        (after.core.setReg .rsp (after.core.readReg .rsp + 8)) finalState.core := by
  obtain ⟨byteCount, finalState, positive, bound, executed, returned, related⟩ :=
    steps.run_with_calls stream base _ (Stream.initial_related checked base core flags) halted slot
  have selected := object.entry
  rw [entry, stream.entryOffset] at selected
  refine ⟨byteCount, finalState, positive, bound, ?_, returned, related⟩
  simp [run, object.text, selected, executed, Except.mapError]

end IxCC.X86.ObjectEval

namespace IxCC.X86

/-- A step that halts the typed machine is a top-level `ret`, which reports
`rax`. -/
theorem step_halted_rax {runtime : Runtime} {checked : Checked} {machine : Machine}
    (running : machine.status = .running) {result : Word}
    (halted : (step runtime checked machine).status = .halted result) :
    result = (step runtime checked machine).core.readReg .rax := by
  obtain ⟨block, found, position, term, returns, coreEqual⟩ := Stream.halting_shape runtime machine running halted
  have one := Stream.source_terminator runtime machine running found position
  rw [one, term] at halted ⊢
  simp only [executeTerminator, returns, Status.halted.injEq] at halted ⊢
  exact halted.symm

theorem Steps.of_not_running {runtime : Runtime} {checked : Checked} {count : Nat} {before after : Machine}
    (steps : Steps runtime checked count before after) (finished : before.status ≠ .running) : after = before := by
  have same := steps.run_eq
  rw [run_of_not_running _ _ _ _ finished] at same
  exact same.symm

/-- A halted run's status is the `rax` of its final core. -/
theorem Steps.halted_rax {runtime : Runtime} {checked : Checked} {count : Nat} {before after : Machine}
    (steps : Steps runtime checked count before after) (running : before.status = .running) {result : Word}
    (halted : after.status = .halted result) : result = after.core.readReg .rax := by
  induction steps with
  | refl => rw [running] at halted; cases halted
  | @cons before middle after count first rest ih =>
      cases status : middle.status with
      | running => exact ih status halted
      | halted value =>
          have same := rest.of_not_running (by simp [status])
          subst same
          rw [← first] at status halted ⊢
          exact step_halted_rax running halted
      | trapped fault =>
          have same := rest.of_not_running (by simp [status])
          subst same
          rw [status] at halted
          cases halted

/-- How an export ends: halted with status `st` in `rax` and
value `val` in `rdx`, the caller's callee-saved registers and stack pointer
restored, and the caller's return address in its slot. -/
structure Exit (core₀ : Core) (retAddr st val : Word) (after : Machine) : Prop where
  halted : after.status = .halted st
  value : after.core.readReg .rdx = val
  saved : ∀ register ∈ SysV.calleeSaved, after.core.readReg register = core₀.readReg register
  rsp : after.core.readReg .rsp = core₀.readReg .rsp
  slot : after.core.memory.read64? (after.core.readReg .rsp) = .ok retAddr

theorem rsp_not_calleeSaved {register : GPR} (member : register ∈ SysV.calleeSaved) : register ≠ .rsp := by
  intro equal
  subst equal
  simp [SysV.calleeSaved] at member

end IxCC.X86

namespace IxCC.X86.ObjectEval

/-- A certified run that ends as an export does (successfully or through the
failure exit) runs the same way from the parsed object: the physical `ret`
reaches the caller with the status and value in `rax:rdx`, the caller's
callee-saved registers, and `rsp` past the return address. -/
theorem run_exit {checked : Checked} {input : ELF.Input} {bytes : ByteArray}
    (stream : Stream.Valid checked.program input.encoded) (object : ELF.Valid input bytes)
    (entry : input.entryBlock = checked.program.entry)
    {runtime : Runtime} {count : Nat} (base : Word) (core₀ : Core) (flags : ByteEval.Flags)
    {after : Machine} {holes : Stream.Holes} {retAddr st val : Word}
    (steps : Stream.SafeSteps runtime checked count (fun _ => False) (Machine.initial checked core₀) holes after)
    (exit : Exit core₀ retAddr st val after) :
    ∃ byteCount s, 0 < byteCount ∧ byteCount ≤ 3 * count ∧
      run bytes input.exportName base byteCount core₀ flags = .ok s ∧
      s.rip = retAddr ∧ s.core.readReg .rax = st ∧ s.core.readReg .rdx = val ∧
      s.core.readReg .rsp = core₀.readReg .rsp + 8 ∧
      (∀ register ∈ SysV.calleeSaved, s.core.readReg register = core₀.readReg register) ∧
      Stream.MemoryRelated holes after.core.memory s.core.memory := by
  obtain ⟨byteCount, s, positive, bound, executed, returned, related⟩ :=
    run_safeSteps stream object entry base core₀ flags steps exit.halted exit.slot
  have rax := steps.steps.halted_rax rfl exit.halted
  have register (target : GPR) (other : target ≠ .rsp) : s.core.readReg target = after.core.readReg target := by
    rw [← related.readReg target]
    simp [Core.readReg, Core.setReg, Registers.set, other]
  refine ⟨byteCount, s, positive, bound, executed, returned, ?_, ?_, ?_, ?_, related.memory⟩
  · rw [register .rax (by decide), rax]
  · rw [register .rdx (by decide), exit.value]
  · rw [← related.readReg .rsp, exit.rsp]
    simp [Core.readReg, Core.setReg, Registers.set]
  · intro target member
    rw [register target (rsp_not_calleeSaved member), exit.saved target member]

end IxCC.X86.ObjectEval
