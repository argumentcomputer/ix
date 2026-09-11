import Ix.Compiler.X86.ELFLink

/-! Execution starts from the independently parsed object text and its
exported symbol. The initial RIP is therefore selected by actual ELF bytes,
rather than supplied as an unchecked address in a theorem premise. -/

namespace Ix.Compiler.X86.Stream

theorem checked_entry_bound (checked : Checked) : checked.program.entry.toNat < checked.program.blocks.size := by
  have fields := checked.valid
  simp only [Program.wellFormed, Bool.and_eq_true, and_assoc] at fields
  simpa [Program.hasBlock] using fields.2.2.1

theorem blockOffsets_get {program : Program} {index : Nat} (bound : index < program.blocks.size) :
    (blockOffsets program)[index]? = some (blockOffset program index) := by
  simp [blockOffsets, bound]

theorem Valid.entryOffset {checked : Checked} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid checked.program output externals) :
    output.blockOffsets[checked.program.entry.toNat]? = some (blockOffset checked.program checked.program.entry.toNat) := by
  rw [valid.offsets]
  exact blockOffsets_get (checked_entry_bound checked)

theorem initial_running (checked : Checked) (base : Word) (core : Core) (flags : ByteEval.Flags) :
    RunningAt checked.program base (Machine.initial checked core)
      ⟨core, base + UInt64.ofNat (blockOffset checked.program checked.program.entry.toNat), flags⟩ :=
  ⟨rfl, rfl, rfl, _, target_entry (checked_entry_bound checked), rfl⟩

theorem initial_related (checked : Checked) (base : Word) (core : Core) (flags : ByteEval.Flags) :
    Related checked.program base (fun _ => False) (Machine.initial checked core)
      ⟨core, base + UInt64.ofNat (blockOffset checked.program checked.program.entry.toNat), flags⟩ :=
  ⟨⟨rfl, MemoryRelated.refl _, by simp [FramesMapped, Machine.initial]⟩,
    rfl, _, target_entry (checked_entry_bound checked), rfl⟩

end Ix.Compiler.X86.Stream

namespace Ix.Compiler.X86.ObjectEval

inductive Fault where
  | object
  | entry
  | machine (fault : ByteEval.Fault)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def run (bytes : ByteArray) (name : String) (base : Word) (fuel : Nat) (core : Core) (flags : ByteEval.Flags := {}) :
    Except Fault ByteEval.State := do
  let some text := ELFRead.text? bytes | throw .object
  let some offset := ELF.entry? bytes name | throw .entry
  (ByteEval.run text base fuel ⟨core, base + UInt64.ofNat offset, flags⟩).mapError Fault.machine

/-- Whole-object execution for every terminating call-free typed run. Both
text fetch and entry selection are obtained from the actual serialized file. -/
theorem run_from_typed {checked : Checked} {input : ELF.Input} {bytes : ByteArray}
    (stream : Stream.Valid checked.program input.encoded) (object : ELF.Valid input bytes)
    (entry : input.entryBlock = checked.program.entry) (free : Stream.CallFree checked.program)
    (runtime : Runtime) (base : Word) (fuel : Nat) (core : Core) (flags : ByteEval.Flags)
    {after : Machine} {result returnAddress : Word}
    (execution : X86.runFrom runtime checked fuel core = after) (halted : after.status = .halted result)
    (slot : after.core.memory.read64? (after.core.readReg .rsp) = .ok returnAddress) :
    ∃ count finalState, 0 < count ∧ count ≤ 3 * fuel ∧
      run bytes input.exportName base count core flags = .ok finalState ∧ Stream.Returned after.core returnAddress finalState := by
  obtain ⟨count, finalState, positive, bound, executed, returned⟩ :=
    Stream.run_to_return stream free runtime base fuel (Machine.initial checked core) _
      (Stream.initial_running checked base core flags) execution halted slot
  have selected := object.entry
  rw [entry, stream.entryOffset] at selected
  refine ⟨count, finalState, positive, bound, ?_, returned⟩
  simp [run, object.text, selected, executed, Except.mapError]

/-- The same actual-object entry point composes nested internal calls under
the explicit stack/data-access conditions of `SafeTrace`. -/
theorem run_with_calls {checked : Checked} {input : ELF.Input} {bytes : ByteArray}
    (stream : Stream.Valid checked.program input.encoded) (object : ELF.Valid input bytes)
    (entry : input.entryBlock = checked.program.entry)
    (runtime : Runtime) (base : Word) (fuel : Nat) (core : Core) (flags : ByteEval.Flags)
    (safe : Stream.SafeTrace runtime checked fuel (fun _ => False) (Machine.initial checked core))
    {after : Machine} {result returnAddress : Word}
    (execution : X86.runFrom runtime checked fuel core = after) (halted : after.status = .halted result)
    (slot : after.core.memory.read64? (after.core.readReg .rsp) = .ok returnAddress) :
    ∃ count holes finalState, 0 < count ∧ count ≤ 3 * fuel ∧
      run bytes input.exportName base count core flags = .ok finalState ∧ finalState.rip = returnAddress ∧
      Stream.CoreRelated checked.program base holes []
        (after.core.setReg .rsp (after.core.readReg .rsp + 8)) finalState.core := by
  obtain ⟨count, holes, finalState, positive, bound, executed, returned, related⟩ :=
    Stream.run_with_calls stream runtime base fuel (fun _ => False) (Machine.initial checked core) _
      (Stream.initial_related checked base core flags) safe execution halted slot
  have selected := object.entry
  rw [entry, stream.entryOffset] at selected
  refine ⟨count, holes, finalState, positive, bound, ?_, returned, related⟩
  simp [run, object.text, selected, executed, Except.mapError]

end Ix.Compiler.X86.ObjectEval
