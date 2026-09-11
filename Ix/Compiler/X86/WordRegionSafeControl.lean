import Ix.Compiler.X86.WordRegionSafeTrace
import Ix.Compiler.X86.SafeControl

namespace Ix.Compiler.X86.WordRegion

theorem State.compare_core (state : State) (memory : Memory) (comparison : Compare) (condition : Condition) :
    comparison.holds condition (state.core memory) = comparison.holds condition (state.core Memory.unmapped) := by
  cases comparison.right <;> rfl

theorem SafeTrace.jump {layout : Layout} {returns : List ReturnFrame} {instructions : List Instr}
    {before after : State} {holes finalHoles : Stream.Holes}
    (trace : SafeTrace layout returns instructions before holes after finalHoles)
    (outside memory : Memory) (represented : Realizes layout outside before.words memory)
    (checked : Checked) (block target : BlockId) (code : BlockCode checked block instructions (.jump target))
    (valid : checked.program.hasBlock target = true) :
    ∃ nextMemory, Realizes layout outside after.words nextMemory ∧
      Stream.SafeSteps Runtime.rejecting checked (instructions.length + 1)
        holes (inFrame (before.core memory) block 0 returns)
        finalHoles (inFrame (after.core nextMemory) target 0 returns) := by
  obtain ⟨nextMemory, nextView, executed⟩ := trace.steps outside memory represented Runtime.rejecting checked block 0
    code.segment (by simpa using code.fits)
  simp only [Nat.zero_add] at executed
  refine ⟨nextMemory, nextView, ?_⟩
  exact executed.append (code.safe_jump valid Runtime.rejecting (after.core nextMemory) returns finalHoles)

theorem SafeTrace.branch {layout : Layout} {returns : List ReturnFrame} {instructions : List Instr}
    {before after : State} {holes finalHoles : Stream.Holes}
    (trace : SafeTrace layout returns instructions before holes after finalHoles)
    (outside memory : Memory) (represented : Realizes layout outside before.words memory)
    (checked : Checked) (block yes no : BlockId) (comparison : Compare) (condition : Condition)
    (code : BlockCode checked block instructions (.branch comparison condition yes no))
    (answer : Bool) (holds : comparison.holds condition (after.core Memory.unmapped) = answer)
    (valid : checked.program.hasBlock (if answer then yes else no) = true) :
    ∃ nextMemory, Realizes layout outside after.words nextMemory ∧
      Stream.SafeSteps Runtime.rejecting checked (instructions.length + 1)
        holes (inFrame (before.core memory) block 0 returns)
        finalHoles (inFrame (after.core nextMemory) (if answer then yes else no) 0 returns) := by
  obtain ⟨nextMemory, nextView, executed⟩ := trace.steps outside memory represented Runtime.rejecting checked block 0
    code.segment (by simpa using code.fits)
  simp only [Nat.zero_add] at executed
  refine ⟨nextMemory, nextView, ?_⟩
  exact executed.append (code.safe_branch Runtime.rejecting (after.core nextMemory) returns finalHoles answer
    ((after.compare_core nextMemory comparison condition).trans holds) valid)

end Ix.Compiler.X86.WordRegion
