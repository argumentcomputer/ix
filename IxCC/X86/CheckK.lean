import IxCC.X86.Basic

/-!
# `Program.check` in kernel-evaluable style

`Program.checkK` is `Program.check` over the blocks' and instructions'
lists, with the block count computed once: `Array.all` runs a loop by
well-founded recursion, which the kernel unfolds through `Acc` proofs
(design note 00, kernel-evaluable style; M1.K1). `checkK_eq` proves it is
`Program.check`, so the recheck path (`Backend.finish`) runs it in place of
the original without changing a result or a statement about `Checked`.
-/

namespace IxCC.X86

/-- `Instr.targetsValid` against a block count. -/
def Instr.targetsValidK (n : Nat) : Instr → Bool
  | .call target => decide (target.toNat < n)
  | _ => true

/-- `Terminator.targetsValid` against a block count. -/
def Terminator.targetsValidK (n : Nat) : Terminator → Bool
  | .jump target | .tailCall target => decide (target.toNat < n)
  | .branch _ _ _ ifTrue ifFalse _ => decide (ifTrue.toNat < n) && decide (ifFalse.toNat < n)
  | .ret => true

/-- `Block.instructionsValid` over the instructions' list. -/
def Block.instructionsValidK (block : Block) : Bool :=
  block.instructions.toList.all Instr.wellFormed

/-- A block's part of `Program.wellFormed`, in a program of `n` blocks. -/
def Block.wellFormedK (n : Nat) (block : Block) : Bool :=
  decide (block.instructions.toList.length < 2 ^ 32) &&
    (block.instructions.toList.all (Instr.targetsValidK n) && block.terminator.targetsValidK n) &&
    block.instructionsValidK && block.terminator.wellFormed

/-- `Program.wellFormed` over the blocks' list. -/
def Program.wellFormedK (program : Program) : Bool :=
  let blocks := program.blocks.toList
  let n := blocks.length
  !blocks.isEmpty && decide (n < 2 ^ 32) && decide (program.entry.toNat < n) &&
    blocks.all (Block.wellFormedK n)

theorem Instr.targetsValidK_eq (program : Program) (instruction : Instr) :
    instruction.targetsValidK program.blocks.size = instruction.targetsValid program := by
  cases instruction <;> rfl

theorem Terminator.targetsValidK_eq (program : Program) (terminator : Terminator) :
    terminator.targetsValidK program.blocks.size = terminator.targetsValid program := by
  cases terminator <;> rfl

theorem Block.instructionsValidK_eq (block : Block) :
    block.instructionsValidK = block.instructionsValid := by
  simp [Block.instructionsValidK, Block.instructionsValid]

theorem Block.wellFormedK_eq (program : Program) (block : Block) :
    block.wellFormedK program.blocks.size =
      (block.offsetsFit && block.targetsValid program && block.instructionsValid &&
        block.terminator.wellFormed) := by
  have targets : (Instr.targetsValidK program.blocks.size) = Instr.targetsValid program :=
    funext (Instr.targetsValidK_eq program)
  simp only [Block.wellFormedK, Block.offsetsFit, Block.targetsValid, Block.instructionsValidK_eq,
    Terminator.targetsValidK_eq, targets, Array.all_toList, Array.length_toList]

theorem Program.wellFormedK_eq (program : Program) : program.wellFormedK = program.wellFormed := by
  have blocks : Block.wellFormedK program.blocks.size =
      fun block => block.offsetsFit && block.targetsValid program && block.instructionsValid &&
        block.terminator.wellFormed :=
    funext (Block.wellFormedK_eq program)
  simp only [Program.wellFormedK, Program.wellFormed, Program.hasBlock, Array.all_toList,
    Array.isEmpty_toList, Array.length_toList]
  rw [blocks]

/-- `Program.check` in kernel-evaluable style (`checkK_eq`). -/
def Program.checkK (program : Program) : Except ValidationError Checked :=
  if valid : program.wellFormedK = true then
    .ok ⟨program, program.wellFormedK_eq ▸ valid⟩
  else if program.blocks.toList.all Block.instructionsValidK then
    .error .malformedControl
  else
    .error .malformedInstruction

theorem Program.checkK_eq (program : Program) : program.checkK = program.check := by
  have valid : Block.instructionsValidK = Block.instructionsValid := funext Block.instructionsValidK_eq
  unfold Program.checkK Program.check
  simp only [Program.wellFormedK_eq, valid, Array.all_toList]

end IxCC.X86
