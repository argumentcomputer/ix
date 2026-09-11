import Ix.Compiler.X86.SafeSteps

namespace Ix.Compiler.X86

theorem BlockCode.hasBlock {checked : Checked} {block : BlockId} {instructions : List Instr}
    {terminator : Terminator} (code : BlockCode checked block instructions terminator) :
    checked.program.hasBlock block = true := by
  have := Array.getElem?_eq_some_iff.mp code.found
  exact decide_eq_true this.1

theorem BlockCode.holeStep {checked : Checked} {block : BlockId} {instructions : List Instr}
    {terminator : Terminator} (code : BlockCode checked block instructions terminator)
    (core : Core) (returns : List ReturnFrame) (holes : Stream.Holes) :
    Stream.holeStep checked.program (inFrame core block instructions.length returns) holes = holes := by
  simp [Stream.holeStep, inFrame, UInt32.toNat_ofNat_of_lt' code.fits, code.found]

theorem BlockCode.safe_jump {checked : Checked} {block target : BlockId} {instructions : List Instr}
    (code : BlockCode checked block instructions (.jump target))
    (valid : checked.program.hasBlock target = true)
    (runtime : Runtime) (core : Core) (returns : List ReturnFrame) (holes : Stream.Holes) :
    Stream.SafeSteps runtime checked 1 holes (inFrame core block instructions.length returns)
      holes (inFrame core target 0 returns) := by
  have safe : Stream.SafeAt checked.program holes (inFrame core block instructions.length returns) := by
    simp [Stream.SafeAt, inFrame, UInt32.toNat_ofNat_of_lt' code.fits, code.found]
  have one := Stream.SafeSteps.single safe (code.jump_inFrame valid runtime core returns)
  simpa only [code.holeStep] using one

theorem BlockCode.safe_branch {checked : Checked} {block yes no : BlockId} {instructions : List Instr}
    {comparison : Compare} {condition : Condition}
    (code : BlockCode checked block instructions (.branch comparison condition yes no))
    (runtime : Runtime) (core : Core) (returns : List ReturnFrame) (holes : Stream.Holes) (answer : Bool)
    (holds : comparison.holds condition core = answer)
    (valid : checked.program.hasBlock (if answer then yes else no) = true) :
    Stream.SafeSteps runtime checked 1 holes (inFrame core block instructions.length returns)
      holes (inFrame core (if answer then yes else no) 0 returns) := by
  have safe : Stream.SafeAt checked.program holes (inFrame core block instructions.length returns) := by
    simp [Stream.SafeAt, inFrame, UInt32.toNat_ofNat_of_lt' code.fits, code.found]
  have one := Stream.SafeSteps.single safe (code.branch_inFrame runtime core returns answer holds valid)
  simpa only [code.holeStep] using one

theorem BlockCode.safe_ret {checked : Checked} {block : BlockId} {instructions : List Instr}
    (code : BlockCode checked block instructions .ret)
    (runtime : Runtime) (core : Core) (frame : ReturnFrame) (returns : List ReturnFrame) (holes : Stream.Holes)
    (stack : core.readReg .rsp = frame.returnSlot)
    (readable : core.memory.read64? frame.returnSlot = .ok frame.continuation.encode)
    (saved : core.calleeSavedMatch frame.calleeSaved = true) :
    Stream.SafeSteps runtime checked 1 holes (inFrame core block instructions.length (frame :: returns))
      holes { core := core.setReg .rsp (frame.returnSlot + 8), pc := frame.continuation, returns, status := .running } := by
  have safe : Stream.SafeAt checked.program holes (inFrame core block instructions.length (frame :: returns)) := by
    simpa [Stream.SafeAt, inFrame, UInt32.toNat_ofNat_of_lt' code.fits, code.found] using ⟨stack, readable, saved⟩
  have one := Stream.SafeSteps.single safe (code.ret_inFrame runtime core frame returns stack readable saved)
  simpa only [code.holeStep] using one

end Ix.Compiler.X86
