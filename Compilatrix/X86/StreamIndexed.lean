import Compilatrix.X86.StreamSpec
import Compilatrix.X86.StreamIndex
import Compilatrix.X86.DecodeWindow

/-! Complete stream validation using canonical cached positions and bounded
instruction windows. Exact agreement with the reference checker preserves
both its rejection behavior and all existing stream/object certificates. -/

namespace Compilatrix.X86.Stream

/-- A reusable layout tied to the exact source program. Its equality proof
is erased; constructing it computes the canonical index once. -/
abbrev PreparedLayout (program : Program) := { index : Index // index = buildIndex program }

def prepareLayout (program : Program) : PreparedLayout program := ⟨buildIndex program, rfl⟩

private def decodesIndexed (text : ByteArray) (offset : Nat) (operation : Decode.Operation) (length : Nat) : Bool :=
  Decode.decodeWindowAt text offset == some ⟨operation, length⟩

private def targetsIndexed (program : Program) (layout : Index) (text : ByteArray) (offset : Nat)
    (operation : Imm32 → Decode.Operation) (length : Nat) (target : BlockId) : Bool :=
  let targetOffset := layout.starts[target.toNat]?.getD 0
  decide (target.toNat < program.blocks.size) &&
    Encode.fitsSigned32 ((targetOffset : Int) - (offset + length)) &&
    decodesIndexed text offset (operation (displacement (offset + length) targetOffset)) length

private def instructionIndexed (program : Program) (layout : Index) (text : ByteArray)
    (externals : ExternalTargets) (offset : Nat) (instruction : Instr) : Bool :=
  match instruction with
  | .call target => targetsIndexed program layout text offset .call 5 target
  | .callRuntime intrinsic =>
      match externals intrinsic with
      | none => decodesIndexed text offset (.call 0) 5
      | some target => Encode.fitsSigned32 (target - (offset + 5)) &&
          decodesIndexed text offset (.call (externalDisplacement (offset + 5) target)) 5
  | _ => decodesIndexed text offset (Encode.instructionOperation instruction) (instructionSize instruction)

private def terminatorIndexed (program : Program) (layout : Index) (text : ByteArray) (offset : Nat) : Terminator → Bool
  | .jump target | .tailCall target => targetsIndexed program layout text offset .jump 5 target
  | .ret => decodesIndexed text offset .ret 1
  | .branch comparison condition yes no =>
      let size := (Encode.encodeCompare comparison).size
      decodesIndexed text offset (.compare comparison.width comparison.left (Encode.aluOperand comparison.width comparison.right)) size &&
        targetsIndexed program layout text (offset + size) (.branch condition) 6 yes &&
        targetsIndexed program layout text (offset + size + 6) .jump 5 no

private def relocationsIndexed (program : Program) (layout : Index) : Array Encode.Relocation :=
  ((program.blocks.toList.zipIdx).flatMap fun (block, blockIndex) =>
    let start := layout.starts[blockIndex]?.getD 0
    let positions := (layout.blocks[blockIndex]?.getD default).positions
    block.instructions.toList.zipIdx.filterMap fun (instruction, instructionIndex) =>
      match instruction with
      | .callRuntime intrinsic => some {
          offset := start + positions[instructionIndex]?.getD 0 + 1
          symbol := Encode.intrinsicSymbol intrinsic, addend := -4 }
      | _ => none).toArray

private def blockIndexed (program : Program) (layout : Index) (output : Encode.Output)
    (externals : ExternalTargets) (blockIndex : Nat) : Bool :=
  match program.blocks[blockIndex]? with
  | none => false
  | some block =>
      let start := layout.starts[blockIndex]?.getD 0
      let indexedBlock := layout.blocks[blockIndex]?.getD default
      (List.range block.instructions.size).all (fun index =>
        match block.instructions[index]? with
        | none => false
        | some instruction => instructionIndexed program layout output.text externals
            (start + indexedBlock.positions[index]?.getD 0) instruction) &&
      terminatorIndexed program layout output.text (start + indexedBlock.bodyBytes) block.terminator

/-- Validation with an already prepared, proof-associated layout. -/
def checkPrepared {program : Program} (layout : PreparedLayout program) (output : Encode.Output)
    (externals : ExternalTargets := unresolved) : Bool :=
  decide (layout.val.textBytes < UInt64.size) && output.text.size == layout.val.textBytes &&
    output.blockOffsets == layout.val.starts && output.relocations == relocationsIndexed program layout.val &&
    (List.range program.blocks.size).all (blockIndexed program layout.val output externals)

def checkIndexed (program : Program) (output : Encode.Output) (externals : ExternalTargets := unresolved) : Bool :=
  checkPrepared (prepareLayout program) output externals

private theorem decodesIndexed_eq : decodesIndexed text offset operation length = decodes text offset operation length := by
  simp [decodesIndexed, decodes, Decode.decodeWindowAt_eq]

private theorem targetsIndexed_eq :
    targetsIndexed program (buildIndex program) text offset operation length target =
      targets program text offset operation length target := by
  by_cases bound : target.toNat < program.blocks.size
  · simp [targetsIndexed, targets, buildIndex_start program bound, decodesIndexed_eq]
  · simp [targetsIndexed, targets, bound]

private theorem instructionIndexed_eq :
    instructionIndexed program (buildIndex program) text externals offset instruction =
      instructionMatches program text externals offset instruction := by
  cases instruction <;> simp [instructionIndexed, instructionMatches, targetsIndexed_eq, decodesIndexed_eq] <;> rfl

private theorem terminatorIndexed_eq :
    terminatorIndexed program (buildIndex program) text offset terminator =
      terminatorMatches program text offset terminator := by
  cases terminator <;> simp [terminatorIndexed, terminatorMatches, targetsIndexed_eq, decodesIndexed_eq]

private theorem block_position {program : Program} {block : Block} {blockIndex index : Nat}
    (found : program.blocks[blockIndex]? = some block) (bound : index ≤ block.instructions.size) :
    ((buildIndex program).blocks[blockIndex]?.getD default).positions[index]? = some (instructionOffset block index) := by
  simp only [buildIndex_blocks, Array.getElem?_map, found, Option.map_some, Option.getD_some]
  exact indexBlock_position block bound

private theorem filterMap_congr_mem {items : List α} {left right : α → Option β}
    (same : ∀ item ∈ items, left item = right item) : items.filterMap left = items.filterMap right := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.filterMap_cons, same head (by simp)]
    rw [ih (fun item member => same item (by simp [member]))]

private theorem all_congr_mem {items : List α} {left right : α → Bool}
    (same : ∀ item ∈ items, left item = right item) : items.all left = items.all right := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.all_cons, same head (by simp)]
    rw [ih (fun item member => same item (by simp [member]))]

private theorem relocationsIndexed_eq :
    relocationsIndexed program (buildIndex program) = expectedRelocations program := by
  unfold relocationsIndexed expectedRelocations
  congr 1
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro pair member
  rcases pair with ⟨block, blockIndex⟩
  have found : program.blocks[blockIndex]? = some block := by
    simpa only [Array.getElem?_toList] using List.mk_mem_zipIdx_iff_getElem?.mp member
  have bound := (Array.getElem?_eq_some_iff.mp found).1
  simp only [buildIndex_start program bound, Option.getD_some]
  apply filterMap_congr_mem
  intro item member
  rcases item with ⟨instruction, instructionIndex⟩
  have instructionAt : block.instructions[instructionIndex]? = some instruction := by
    simpa only [Array.getElem?_toList] using List.mk_mem_zipIdx_iff_getElem?.mp member
  have inner := (Array.getElem?_eq_some_iff.mp instructionAt).1
  have position := block_position found (Nat.le_of_lt inner)
  cases instruction <;> simp [position]

private theorem blockIndexed_eq :
    blockIndexed program (buildIndex program) output externals blockIndex =
      blockMatches program output externals blockIndex := by
  unfold blockIndexed blockMatches
  cases found : program.blocks[blockIndex]? with
  | none => rfl
  | some block =>
    have bound := (Array.getElem?_eq_some_iff.mp found).1
    have body : ((buildIndex program).blocks[blockIndex]?.getD default).bodyBytes =
        instructionOffset block block.instructions.size := by
      simp [buildIndex_blocks, found, indexBlock_body]
    simp only [buildIndex_start program bound, Option.getD_some, body, terminatorIndexed_eq]
    congr 1
    apply all_congr_mem
    intro index member
    have small : index < block.instructions.size := List.mem_range.mp member
    rw [block_position found (Nat.le_of_lt small)]
    cases block.instructions[index]? <;> simp [instructionIndexed_eq]

/-- Exact acceptance and rejection agreement for every output, including
externally resolved calls and malformed offset/relocation inventories. -/
theorem checkPrepared_eq {program : Program} (layout : PreparedLayout program) (output : Encode.Output)
    (externals : ExternalTargets := unresolved) : checkPrepared layout output externals = check program output externals := by
  have blocks : blockIndexed program (buildIndex program) output externals = blockMatches program output externals :=
    funext (fun _ => blockIndexed_eq)
  simp only [checkPrepared, layout.property, buildIndex_text, buildIndex_starts, relocationsIndexed_eq, blocks, check]

theorem checkIndexed_eq (program : Program) (output : Encode.Output) (externals : ExternalTargets := unresolved) :
    checkIndexed program output externals = check program output externals :=
  checkPrepared_eq (prepareLayout program) output externals

theorem checkIndexed_sound {program output externals}
    (accepted : checkIndexed program output externals = true) : Valid program output externals :=
  check_sound ((checkIndexed_eq program output externals).symm.trans accepted)

end Compilatrix.X86.Stream
