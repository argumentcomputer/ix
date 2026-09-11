import Ix.Compiler.X86.UniqueInvariant

/-! Complete-block execution for the selected leaf programs. These lemmas
compose instruction traces with the actual evaluator's jumps, branches, and
return, preserving the byte-memory realization at every block boundary. -/

namespace Ix.Compiler.X86.UniqueExecution

open UniqueABI UniqueTarget

theorem State.compare_core (state : State) (memory : Memory) (comparison : Compare)
    (condition : Condition) :
    comparison.holds condition (state.core memory) =
      comparison.holds condition (state.core Memory.unmapped) := by
  cases comparison.right <;> rfl

theorem Trace.jump {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (outside memory : Memory)
    (represented : Realizes layout outside before.words memory) (runtime : Runtime) (checked : Checked)
    (block target : BlockId) (code : BlockCode checked block instructions (.jump target))
    (valid : checked.program.hasBlock target = true) :
    ∃ nextMemory, Realizes layout outside after.words nextMemory ∧
      Steps runtime checked (instructions.length + 1) (leaf (before.core memory) block 0)
        (leaf (after.core nextMemory) target 0) := by
  obtain ⟨nextMemory, finalView, first⟩ := trace.steps outside memory represented runtime checked block 0
    code.segment (by simpa using code.fits)
  simp only [Nat.zero_add] at first
  exact ⟨nextMemory, finalView, first.append (Steps.single (code.jump valid runtime _))⟩

theorem Trace.branch {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (outside memory : Memory)
    (represented : Realizes layout outside before.words memory) (runtime : Runtime) (checked : Checked)
    (block yes no : BlockId) (comparison : Compare) (condition : Condition)
    (code : BlockCode checked block instructions (.branch comparison condition yes no)) (answer : Bool)
    (holds : comparison.holds condition (after.core Memory.unmapped) = answer)
    (valid : checked.program.hasBlock (if answer then yes else no) = true) :
    ∃ nextMemory, Realizes layout outside after.words nextMemory ∧
      Steps runtime checked (instructions.length + 1) (leaf (before.core memory) block 0)
        (leaf (after.core nextMemory) (if answer then yes else no) 0) := by
  obtain ⟨nextMemory, finalView, first⟩ := trace.steps outside memory represented runtime checked block 0
    code.segment (by simpa using code.fits)
  simp only [Nat.zero_add] at first
  exact ⟨nextMemory, finalView, first.append (Steps.single (code.branch runtime _ answer
    ((after.compare_core nextMemory comparison condition).trans holds) valid))⟩

theorem Trace.ret {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (outside memory : Memory)
    (represented : Realizes layout outside before.words memory) (runtime : Runtime) (checked : Checked)
    (block : BlockId) (code : BlockCode checked block instructions .ret) :
    ∃ nextMemory, Realizes layout outside after.words nextMemory ∧
      Steps runtime checked (instructions.length + 1) (leaf (before.core memory) block 0)
        (haltedLeaf (after.core nextMemory) block instructions.length) := by
  obtain ⟨nextMemory, finalView, first⟩ := trace.steps outside memory represented runtime checked block 0
    code.segment (by simpa using code.fits)
  simp only [Nat.zero_add] at first
  exact ⟨nextMemory, finalView, first.append (Steps.single (code.ret runtime _))⟩

def tagInstructions (pointer : GPR) : List Instr := [.load .w64 .rcx (memoryOperand pointer 0)]
def tagCompare : Compare := { width := .w64, left := .rcx, right := .imm 0 }
def tagState (state : State) (index : Nat) : State := state.setReg .rcx (state.words (cellSlot index 0))

theorem tagTrace (layout : Layout) (state : State) (pointer : GPR) (index : Nat)
    (bound : index < layout.capacity) (root : state.registers pointer = layout.cell index) :
    Trace layout (tagInstructions pointer) state (tagState state index) :=
  .cons (loadField layout state pointer .rcx index 0 bound (by decide) root) (.nil _)

theorem tagState_test (state : State) (index : Nat) (tag : Word)
    (tagAt : state.words (cellSlot index 0) = tag) :
    tagCompare.holds .eq ((tagState state index).core Memory.unmapped) = (tag == 0) := by
  simp [tagCompare, Compare.holds, Condition.holds, Core.readReg, State.core, AluSource.eval,
    tagState, tagAt, signExtend32]

theorem main_hasBlock (values : List Word) (checked : Checked) (produced : checked.program = program values)
    (block : BlockId) (bound : block.toNat < 7) : checked.program.hasBlock block = true := by
  simp [Program.hasBlock, produced, program, bound]

theorem main_tagCode (values : List Word) (checked : Checked) (produced : checked.program = program values) :
    BlockCode checked 3 (tagInstructions .rdx) (.branch tagCompare .eq 4 5) :=
  ⟨by rw [produced]; rfl, by decide⟩

theorem main_consCode (values : List Word) (checked : Checked) (produced : checked.program = program values) :
    BlockCode checked 5 consInstructions (.jump 3) :=
  ⟨by rw [produced]; rfl, by decide⟩

theorem main_retCode (values : List Word) (checked : Checked) (produced : checked.program = program values) :
    BlockCode checked 4 (releaseCell .rdx ++ [Instr.mov .w64 .rax (.reg .rsi)]) .ret :=
  ⟨by rw [produced]; rfl, by decide⟩

/-- The reversal loop can be reached from either a closed builder or a
checked runtime-input prologue. A replacement cons block supplies its own
instruction-effect proof to the loop composition theorem. -/
structure LoopCode (checked : Checked) (body : List Instr := consInstructions) : Prop where
  tag : BlockCode checked 3 (tagInstructions .rdx) (.branch tagCompare .eq 4 5)
  cons : BlockCode checked 5 body (.jump 3)
  finish : BlockCode checked 4 (releaseCell .rdx ++ [Instr.mov .w64 .rax (.reg .rsi)]) .ret
  hasTag : checked.program.hasBlock 3 = true
  hasCons : checked.program.hasBlock 5 = true
  hasFinish : checked.program.hasBlock 4 = true

theorem main_loopCode (values : List Word) (checked : Checked) (produced : checked.program = program values) :
    LoopCode checked :=
  ⟨main_tagCode values checked produced, main_consCode values checked produced, main_retCode values checked produced,
    main_hasBlock values checked produced 3 (by decide), main_hasBlock values checked produced 5 (by decide),
    main_hasBlock values checked produced 4 (by decide)⟩

theorem main_inputCode (values : List Word) (checked : Checked) (produced : checked.program = program values)
    (bound : values.length ≤ maxLength) : BlockCode checked 2 (inputInstructions values) (.jump 3) := by
  refine ⟨by rw [produced]; rfl, ?_⟩
  simp only [inputInstructions_length, UInt32.size]
  change values.length ≤ 64 at bound
  omega

theorem release_hasBlock (checked : Checked) (produced : checked.program = releaseProgram)
    (block : BlockId) (bound : block.toNat < 3) : checked.program.hasBlock block = true := by
  simp [Program.hasBlock, produced, releaseProgram, bound]

theorem release_tagCode (checked : Checked) (produced : checked.program = releaseProgram) :
    BlockCode checked 0 (tagInstructions .rsi) (.branch tagCompare .eq 2 1) :=
  ⟨by rw [produced]; rfl, by decide⟩

theorem release_consCode (checked : Checked) (produced : checked.program = releaseProgram) :
    BlockCode checked 1 ([Instr.load .w64 .rdx (memoryOperand .rsi 16)] ++ releaseCell .rsi ++
      [Instr.mov .w64 .rsi (.reg .rdx)]) (.jump 0) :=
  ⟨by rw [produced]; rfl, by decide⟩

theorem release_retCode (checked : Checked) (produced : checked.program = releaseProgram) :
    BlockCode checked 2 (releaseCell .rsi ++ [Instr.mov .w64 .rax (.imm 0)]) .ret :=
  ⟨by rw [produced]; rfl, by decide⟩

end Ix.Compiler.X86.UniqueExecution
