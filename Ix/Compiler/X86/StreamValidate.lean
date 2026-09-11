import Ix.Compiler.X86.StreamLayout

/-! Fail-closed validation of complete emitted text. This checks decoded
operations, canonical positions, all internal targets, and the exact external
relocation inventory. Certificates contain these concrete facts, never a
caller-supplied execution or simulation function. -/

namespace Ix.Compiler.X86.Stream

/-- External code positions relative to the text base; negative positions
allow a linker to place a procedure before the current text segment. -/
abbrev ExternalTargets := Intrinsic → Option Int
def unresolved : ExternalTargets := fun _ => none

def displacement (next target : Nat) : Imm32 := (Int32.ofInt ((target : Int) - next)).toUInt32
def externalDisplacement (next : Nat) (target : Int) : Imm32 := (Int32.ofInt (target - next)).toUInt32

def decodes (text : ByteArray) (offset : Nat) (operation : Decode.Operation) (length : Nat) : Bool :=
  Decode.decodeAt text offset == some ⟨operation, length⟩

def targets (program : Program) (text : ByteArray) (offset : Nat)
    (operation : Imm32 → Decode.Operation) (length : Nat) (target : BlockId) : Bool :=
  decide (target.toNat < program.blocks.size) &&
    Encode.fitsSigned32 ((blockOffset program target.toNat : Int) - (offset + length)) &&
    decodes text offset (operation (displacement (offset + length) (blockOffset program target.toNat))) length

def instructionMatches (program : Program) (text : ByteArray) (externals : ExternalTargets)
    (offset : Nat) (instruction : Instr) : Bool :=
  match instruction with
  | .call target => targets program text offset .call 5 target
  | .callRuntime intrinsic =>
      match externals intrinsic with
      | none => decodes text offset (.call 0) 5
      | some target => Encode.fitsSigned32 (target - (offset + 5)) &&
          decodes text offset (.call (externalDisplacement (offset + 5) target)) 5
  | _ => decodes text offset (Encode.instructionOperation instruction) (instructionSize instruction)

def terminatorMatches (program : Program) (text : ByteArray) (offset : Nat) : Terminator → Bool
  | .jump target | .tailCall target => targets program text offset .jump 5 target
  | .ret => decodes text offset .ret 1
  | .branch comparison condition yes no =>
      let size := (Encode.encodeCompare comparison).size
      decodes text offset (.compare comparison.width comparison.left (Encode.aluOperand comparison.width comparison.right)) size &&
        targets program text (offset + size) (.branch condition) 6 yes &&
        targets program text (offset + size + 6) .jump 5 no

def expectedRelocations (program : Program) : Array Encode.Relocation :=
  ((program.blocks.toList.zipIdx).flatMap fun (block, blockIndex) =>
    block.instructions.toList.zipIdx.filterMap fun (instruction, instructionIndex) =>
      match instruction with
      | .callRuntime intrinsic => some {
          offset := blockOffset program blockIndex + instructionOffset block instructionIndex + 1
          symbol := Encode.intrinsicSymbol intrinsic, addend := -4 }
      | _ => none).toArray

def blockMatches (program : Program) (output : Encode.Output) (externals : ExternalTargets)
    (blockIndex : Nat) : Bool :=
  match program.blocks[blockIndex]? with
  | none => false
  | some block =>
      (List.range block.instructions.size).all (fun index =>
        match block.instructions[index]? with
        | none => false
        | some instruction => instructionMatches program output.text externals
            (blockOffset program blockIndex + instructionOffset block index) instruction) &&
      terminatorMatches program output.text
        (blockOffset program blockIndex + instructionOffset block block.instructions.size) block.terminator

def check (program : Program) (output : Encode.Output) (externals : ExternalTargets := unresolved) : Bool :=
  decide (textSize program < UInt64.size) && output.text.size == textSize program &&
    output.blockOffsets == blockOffsets program && output.relocations == expectedRelocations program &&
    (List.range program.blocks.size).all (blockMatches program output externals)

structure Valid (program : Program) (output : Encode.Output) (externals : ExternalTargets := unresolved) : Prop where
  textBound : textSize program < UInt64.size
  textLength : output.text.size = textSize program
  offsets : output.blockOffsets = blockOffsets program
  relocations : output.relocations = expectedRelocations program
  instruction : ∀ blockIndex block, program.blocks[blockIndex]? = some block →
    ∀ index instruction, block.instructions[index]? = some instruction →
      instructionMatches program output.text externals
        (blockOffset program blockIndex + instructionOffset block index) instruction = true
  terminator : ∀ blockIndex block, program.blocks[blockIndex]? = some block →
    terminatorMatches program output.text
      (blockOffset program blockIndex + instructionOffset block block.instructions.size) block.terminator = true

theorem check_sound {program : Program} {output : Encode.Output} {externals : ExternalTargets}
    (accepted : check program output externals = true) : Valid program output externals := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at accepted
  obtain ⟨bound, length, offsets, relocations, blocks⟩ := accepted
  refine ⟨bound, length, offsets, relocations, ?_, ?_⟩
  · intro blockIndex block found index instruction foundInstruction
    have blockBound : blockIndex < program.blocks.size := (Array.getElem?_eq_some_iff.mp found).1
    have row := List.all_eq_true.mp blocks blockIndex (List.mem_range.mpr blockBound)
    simp only [blockMatches, found, Bool.and_eq_true] at row
    have indexBound : index < block.instructions.size := (Array.getElem?_eq_some_iff.mp foundInstruction).1
    have cell := List.all_eq_true.mp row.1 index (List.mem_range.mpr indexBound)
    simpa [foundInstruction] using cell
  · intro blockIndex block found
    have blockBound : blockIndex < program.blocks.size := (Array.getElem?_eq_some_iff.mp found).1
    have row := List.all_eq_true.mp blocks blockIndex (List.mem_range.mpr blockBound)
    simp only [blockMatches, found, Bool.and_eq_true] at row
    exact row.2

structure Certified (checked : Checked) where
  output : Encode.Output
  valid : Valid checked.program output

inductive Error where
  | encoder (error : Encode.Error)
  | invalidStream
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- The compiler returns a stream only with a checked concrete certificate.
The ordinary encoder remains available for isolated encoding tests. -/
def encode (checked : Checked) : Except Error (Certified checked) := do
  let output ← (Encode.encode checked).mapError Error.encoder
  if accepted : check checked.program output = true then
    return ⟨output, check_sound accepted⟩
  else throw .invalidStream

theorem Valid.decode_linear {program : Program} {output : Encode.Output} {externals : ExternalTargets}
    (valid : Valid program output externals) {blockIndex index : Nat} {block : Block} {instruction : Instr}
    (found : program.blocks[blockIndex]? = some block) (foundInstruction : block.instructions[index]? = some instruction)
    (linear : Encode.linearInstruction instruction = true) :
    Decode.decodeAt output.text (blockOffset program blockIndex + instructionOffset block index) =
      some ⟨Encode.instructionOperation instruction, instructionSize instruction⟩ := by
  have accepted := valid.instruction blockIndex block found index instruction foundInstruction
  cases instruction <;> simp_all [instructionMatches, Encode.linearInstruction, decodes, beq_iff_eq]

end Ix.Compiler.X86.Stream
