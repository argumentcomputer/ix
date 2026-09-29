import Compilatrix.X86.SafeSteps

namespace Compilatrix.X86

theorem BlockCode.hasBlock {checked : Checked} {block : BlockId} {instructions : List Instr}
    {terminator : Terminator} (code : BlockCode checked block instructions terminator) :
    checked.program.hasBlock block = true := by
  have := Array.getElem?_eq_some_iff.mp code.found
  exact decide_eq_true this.1

theorem BlockCode.holeStep {checked : Checked} {block : BlockId} {instructions : List Instr}
    {terminator : Terminator} (code : BlockCode checked block instructions terminator)
    (core : Core) (returns : List ReturnFrame) (holes : Stream.Holes) :
    Stream.holeStep checked.program (inFrame core block instructions.length returns) holes =
      Stream.terminatorHoles holes terminator core := by
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
  simpa only [code.holeStep, Stream.terminatorHoles] using one

/-- A branch is one checked step: its producer's footprint is safe, and the
mask clears what the producer writes. -/
theorem BlockCode.safe_branch {checked : Checked} {block yes no : BlockId} {instructions : List Instr}
    {producer : Op} {args : List Arg} {condition : Condition}
    (code : BlockCode checked block instructions (.branch producer args condition yes no))
    (runtime : Runtime) (core : Core) (returns : List ReturnFrame) (holes : Stream.Holes)
    (access : Stream.OperationSafe holes returns (.op producer args) core)
    {after : Core} {flags : ByteEval.Flags} (produced : producer.exec args core {} = .ok (after, flags))
    {answer : Bool} (tested : flags.test condition = some answer)
    (valid : checked.program.hasBlock (if answer then yes else no) = true) :
    Stream.SafeSteps runtime checked 1 holes (inFrame core block instructions.length returns)
      (Stream.nextHoles holes (.op producer args) core) (inFrame after (if answer then yes else no) 0 returns) := by
  have safe : Stream.SafeAt checked.program holes (inFrame core block instructions.length returns) := by
    simpa [Stream.SafeAt, inFrame, UInt32.toNat_ofNat_of_lt' code.fits, code.found] using access
  have one := Stream.SafeSteps.single safe (code.branch_inFrame runtime core returns produced tested valid)
  simpa only [code.holeStep, Stream.terminatorHoles] using one

/-- A compare-and-branch touches no memory, so the mask is unchanged. -/
theorem BlockCode.safe_compare {checked : Checked} {block yes no : BlockId} {instructions : List Instr}
    {comparison : Compare} {condition : Condition}
    (code : BlockCode checked block instructions (.compare comparison condition yes no))
    (runtime : Runtime) (core : Core) (returns : List ReturnFrame) (holes : Stream.Holes) (answer : Bool)
    (holds : comparison.holds condition core = answer)
    (valid : checked.program.hasBlock (if answer then yes else no) = true) :
    Stream.SafeSteps runtime checked 1 holes (inFrame core block instructions.length returns)
      holes (inFrame core (if answer then yes else no) 0 returns) := by
  have footprint := Stream.footprint_compare comparison core
  have access : Stream.OperationSafe holes returns (.op comparison.row.1 comparison.row.2) core := by
    simp [Stream.OperationSafe, footprint.1, footprint.2]
  have tested : (comparison.flags core).test condition = some answer := by
    rw [Compare.flags_test, holds]
  have produced : comparison.row.1.exec comparison.row.2 core {} = .ok (core, comparison.flags core) := by
    rw [Compare.exec_eq, Compare.flags_eq]
  have one := code.safe_branch runtime core returns holes access produced tested valid
  have unchanged : Stream.nextHoles holes (.op comparison.row.1 comparison.row.2) core = holes := by
    simp [Stream.nextHoles, footprint.2, Stream.clearAccesses]
  rwa [unchanged] at one

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
  simpa only [code.holeStep, Stream.terminatorHoles] using one

end Compilatrix.X86
