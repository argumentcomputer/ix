import Ix.Compiler.X86.SafeSteps
import Ix.Compiler.X86.ObjectExecution

namespace Ix.Compiler.X86.Stream

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
          have fixedBefore : ∀ mask, holeStep checked.program machine mask = mask := by simp [holeStep, found, absent]
          have pcSame : middle.pc = machine.pc := by
            rw [← first, source_terminator runtime machine related.running found position]
            simp [term, executeTerminator, returns]
          have fixedMiddle : ∀ mask, holeStep checked.program middle mask = mask := by simp [holeStep, pcSame, found, absent]
          obtain ⟨same, maskSame⟩ := rest.finished (by simp [status]) fixedMiddle
          have maskSame : finalHoles = holes := maskSame.trans (fixedBefore holes)
          obtain ⟨finalState, last, returned, core⟩ := final_ret valid runtime machine base holes state related access
            middleHalted (by simpa [first, same] using slot)
          refine ⟨1, finalState, by decide, by omega, by simp [ByteEval.run, last, bind, Except.bind], returned, ?_⟩
          simpa only [first, same, maskSame] using core

end Ix.Compiler.X86.Stream

namespace Ix.Compiler.X86.ObjectEval

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

end Ix.Compiler.X86.ObjectEval
