import Ix.Compiler.X86.ByteBranch
import Ix.Compiler.X86.ByteCall

/-! Canonical byte positions for complete typed text worlds. Positions count
the actual emitted lengths, include each terminator, and are independent of
the encoder's layout/fixup implementation. The stream validator checks that
the emitted text and block-offset table realize these positions. -/

namespace Ix.Compiler.X86.Stream

def prefixSize (sizes : List Nat) (count : Nat) : Nat := (sizes.take count).sum

theorem prefix_zero (sizes : List Nat) : prefixSize sizes 0 = 0 := by simp [prefixSize]

theorem prefix_succ (sizes : List Nat) (index : Nat) :
    prefixSize sizes (index + 1) = prefixSize sizes index + (sizes[index]?.getD 0) := by
  simp [prefixSize, List.take_add_one]
  cases sizes[index]? <;> simp

theorem prefix_mono (sizes : List Nat) {first second : Nat} (bound : first ≤ second) :
    prefixSize sizes first ≤ prefixSize sizes second := by
  induction second with
  | zero =>
      have equal : first = 0 := by omega
      subst first
      exact Nat.le_refl _
  | succ second ih =>
      by_cases before : first ≤ second
      · have earlier := ih before
        rw [prefix_succ]
        omega
      · have equal : first = second + 1 := by omega
        subst first
        exact Nat.le_refl _

theorem prefix_le_sum (sizes : List Nat) (index : Nat) : prefixSize sizes index ≤ sizes.sum := by
  have split := List.take_append_drop index sizes
  have total := congrArg List.sum split
  simp only [List.sum_append] at total
  unfold prefixSize
  omega

theorem prefix_strict (sizes : List Nat) (positive : ∀ size ∈ sizes, 0 < size)
    {first second : Nat} (less : first < second) (bound : second ≤ sizes.length) :
    prefixSize sizes first < prefixSize sizes second := by
  have member : sizes[first] ∈ sizes := List.getElem_mem (by omega)
  have nonzero := positive _ member
  have next := prefix_succ sizes first
  rw [List.getElem?_eq_getElem (by omega)] at next
  simp only [Option.getD_some] at next
  have later := prefix_mono sizes (show first + 1 ≤ second by omega)
  omega

def instructionSize (instruction : Instr) : Nat := (Encode.encodeInstr instruction).bytes.size

def terminatorSize : Terminator → Nat
  | .jump _ | .tailCall _ => 5
  | .branch comparison _ _ _ => (Encode.encodeCompare comparison).size + 11
  | .ret => 1

def instructionSizes (block : Block) : List Nat := block.instructions.toList.map instructionSize
def blockSize (block : Block) : Nat := (instructionSizes block).sum + terminatorSize block.terminator
def blockSizes (program : Program) : List Nat := program.blocks.toList.map blockSize
def textSize (program : Program) : Nat := (blockSizes program).sum
def blockOffset (program : Program) (index : Nat) : Nat := prefixSize (blockSizes program) index
def instructionOffset (block : Block) (index : Nat) : Nat := prefixSize (instructionSizes block) index

def blockOffsets (program : Program) : Array Nat :=
  (List.range program.blocks.size).toArray.map (blockOffset program)

def pcOffset? (program : Program) (pc : PC) : Option Nat := do
  let block ← program.blocks[pc.block.toNat]?
  if pc.offset.toNat ≤ block.instructions.size then
    some (blockOffset program pc.block.toNat + instructionOffset block pc.offset.toNat)
  else none

theorem instructionSize_pos (instruction : Instr) : 0 < instructionSize instruction :=
  (Encode.instruction_size instruction).1

theorem terminatorSize_pos (terminator : Terminator) : 0 < terminatorSize terminator := by
  cases terminator <;> simp [terminatorSize]

theorem blockSize_pos (block : Block) : 0 < blockSize block := by
  have := terminatorSize_pos block.terminator
  unfold blockSize
  omega

theorem instructionOffset_zero (block : Block) : instructionOffset block 0 = 0 := prefix_zero _
theorem blockOffset_zero (program : Program) : blockOffset program 0 = 0 := prefix_zero _

theorem instructionOffset_end (block : Block) :
    instructionOffset block block.instructions.size = (instructionSizes block).sum := by
  unfold instructionOffset prefixSize
  rw [List.take_of_length_le (by simp [instructionSizes])]

theorem instructionOffset_next {block : Block} {index : Nat} {instruction : Instr}
    (found : block.instructions[index]? = some instruction) :
    instructionOffset block (index + 1) = instructionOffset block index + instructionSize instruction := by
  rw [instructionOffset, prefix_succ]
  simp [instructionSizes, found, instructionOffset]

theorem instructionOffset_lt (block : Block) (index : Nat) : instructionOffset block index < blockSize block := by
  have prefixSize := prefix_le_sum (instructionSizes block) index
  have positive := terminatorSize_pos block.terminator
  unfold instructionOffset blockSize
  omega

theorem blockOffset_next {program : Program} {index : Nat} {block : Block}
    (found : program.blocks[index]? = some block) :
    blockOffset program (index + 1) = blockOffset program index + blockSize block := by
  rw [blockOffset, prefix_succ]
  simp [blockSizes, found, blockOffset]

theorem blockOffset_end (program : Program) : blockOffset program program.blocks.size = textSize program := by
  unfold blockOffset prefixSize
  rw [List.take_of_length_le (by simp [blockSizes])]
  rfl

theorem block_end_le {program : Program} {index : Nat} {block : Block}
    (found : program.blocks[index]? = some block) :
    blockOffset program index + blockSize block ≤ textSize program := by
  rw [← blockOffset_next found]
  exact prefix_le_sum _ _

theorem pcOffset_small {program : Program} {pc : PC} {offset : Nat}
    (found : pcOffset? program pc = some offset) : offset < textSize program := by
  unfold pcOffset? at found
  cases blockFound : program.blocks[pc.block.toNat]? with
  | none => simp [blockFound] at found
  | some block =>
      simp only [blockFound, bind, Option.bind] at found
      split at found
      · have equal := Option.some.inj found
        have blockBound := block_end_le blockFound
        have inner := instructionOffset_lt block pc.offset.toNat
        omega
      · contradiction

theorem block_entry {program : Program} {block : Block} {id : BlockId}
    (found : program.blocks[id.toNat]? = some block) :
    pcOffset? program ⟨id, 0⟩ = some (blockOffset program id.toNat) := by
  simp [pcOffset?, found, instructionOffset_zero]

theorem rip_offset (base : Word) (offset : Nat) (bound : offset < UInt64.size) :
    (base + UInt64.ofNat offset - base).toNat = offset := Encode.offset_after base offset bound

theorem instructionOffset_strict (block : Block) {first second : Nat}
    (less : first < second) (bound : second ≤ block.instructions.size) :
    instructionOffset block first < instructionOffset block second := by
  apply prefix_strict
  · intro size member
    obtain ⟨instruction, _, rfl⟩ := List.mem_map.mp member
    exact instructionSize_pos instruction
  · exact less
  · simpa [instructionSizes] using bound

theorem block_before {program : Program} {index later : Nat} {block : Block}
    (found : program.blocks[index]? = some block) (less : index < later) :
    blockOffset program index + blockSize block ≤ blockOffset program later := by
  rw [← blockOffset_next found]
  exact prefix_mono _ (by omega)

theorem pcOffset_info {program : Program} {pc : PC} {offset : Nat}
    (found : pcOffset? program pc = some offset) :
    ∃ block, program.blocks[pc.block.toNat]? = some block ∧ pc.offset.toNat ≤ block.instructions.size ∧
      offset = blockOffset program pc.block.toNat + instructionOffset block pc.offset.toNat := by
  unfold pcOffset? at found
  cases blockFound : program.blocks[pc.block.toNat]? with
  | none => simp [blockFound] at found
  | some block =>
      simp only [blockFound, bind, Option.bind] at found
      split at found
      · exact ⟨block, rfl, by assumption, (Option.some.inj found).symm⟩
      · contradiction

/-- Distinct symbolic instruction/terminator positions cannot alias. Branch
macro interior positions are introduced only by the checked CMP/Jcc/JMP recipe. -/
theorem pcOffset_injective {program : Program} {first second : PC} {offset : Nat}
    (firstFound : pcOffset? program first = some offset) (secondFound : pcOffset? program second = some offset) :
    first = second := by
  obtain ⟨left, leftFound, leftBound, leftOffset⟩ := pcOffset_info firstFound
  obtain ⟨right, rightFound, rightBound, rightOffset⟩ := pcOffset_info secondFound
  have blocksEqual : first.block = second.block := by
    apply UInt32.toNat_inj.mp
    have insideLeft := instructionOffset_lt left first.offset.toNat
    have insideRight := instructionOffset_lt right second.offset.toNat
    have orderedLeft := fun h => block_before leftFound (later := second.block.toNat) h
    have orderedRight := fun h => block_before rightFound (later := first.block.toNat) h
    omega
  have equalBlocks : left = right := by
    rw [blocksEqual, rightFound] at leftFound
    exact Option.some.inj leftFound.symm
  subst right
  have offsetsEqual : first.offset = second.offset := by
    apply UInt32.toNat_inj.mp
    have orderedLeft := fun (h : first.offset.toNat < second.offset.toNat) => instructionOffset_strict left h rightBound
    have orderedRight := fun (h : second.offset.toNat < first.offset.toNat) => instructionOffset_strict left h leftBound
    rw [blocksEqual] at leftOffset
    omega
  cases first
  cases second
  simp_all

theorem checked_block_bound {checked : Checked} {index : Nat} {block : Block}
    (found : checked.program.blocks[index]? = some block) : block.instructions.size < UInt32.size := by
  have valid := checked.valid
  simp only [Program.wellFormed, Bool.and_eq_true, and_assoc] at valid
  obtain ⟨bound, equal⟩ := Array.getElem?_eq_some_iff.mp found
  have fields := Array.all_eq_true.mp valid.2.2.2 index bound
  rw [equal] at fields
  simp only [Bool.and_eq_true] at fields
  simpa [Block.offsetsFit, UInt32.size] using fields.1

theorem pc_next {checked : Checked} {block : Block} {pc : PC} {instruction : Instr}
    (found : checked.program.blocks[pc.block.toNat]? = some block)
    (foundInstruction : block.instructions[pc.offset.toNat]? = some instruction) :
    pc.next? = some { pc with offset := pc.offset + 1 } ∧
      (pc.offset + 1).toNat = pc.offset.toNat + 1 := by
  have blockBound := checked_block_bound found
  have indexBound := (Array.getElem?_eq_some_iff.mp foundInstruction).1
  have nextBound : pc.offset.toNat + 1 < UInt32.size := by omega
  have notLast : pc.offset ≠ 0xffffffff := by
    intro equal
    simp [equal, UInt32.size] at nextBound
  constructor
  · simp [PC.next?, notLast]
  · simp [UInt32.toNat_add, Nat.mod_eq_of_lt nextBound]

theorem pcOffset_next {checked : Checked} {block : Block} {pc : PC} {instruction : Instr}
    (found : checked.program.blocks[pc.block.toNat]? = some block)
    (foundInstruction : block.instructions[pc.offset.toNat]? = some instruction) :
    pcOffset? checked.program { pc with offset := pc.offset + 1 } =
      some (blockOffset checked.program pc.block.toNat + instructionOffset block pc.offset.toNat + instructionSize instruction) := by
  have next := pc_next found foundInstruction
  have indexBound := (Array.getElem?_eq_some_iff.mp foundInstruction).1
  simp [pcOffset?, found, next.2, show pc.offset.toNat + 1 ≤ block.instructions.size by omega,
    instructionOffset_next foundInstruction, Nat.add_assoc]

end Ix.Compiler.X86.Stream
