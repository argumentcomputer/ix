import Ix.Compiler.X86.Execution

/-! Instruction and block contracts inside an arbitrary caller continuation.
Unlike leaf execution, these contracts retain the active return frames. -/

namespace Ix.Compiler.X86

def inFrame (core : Core) (block : BlockId) (offset : Nat) (returns : List ReturnFrame) : Machine :=
  { core, pc := { block, offset := UInt32.ofNat offset }, returns, status := .running }

theorem inFrame_advance (core after : Core) (block : BlockId) (returns : List ReturnFrame)
    {offset : Nat} (fits : offset + 1 < UInt32.size) :
    (inFrame core block offset returns).advanceWith after = inFrame after block (offset + 1) returns := by
  have notLast : UInt32.ofNat offset ≠ 0xffffffff := by
    intro equal
    have equal := congrArg UInt32.toNat equal
    rw [UInt32.toNat_ofNat_of_lt' (by omega)] at equal
    change offset = 4294967295 at equal
    simp only [UInt32.size] at fits
    omega
  simp [inFrame, Machine.advanceWith, PC.next?, notLast, UInt32.ofNat_add]

theorem BlockCode.terminator_inFrame {checked : Checked} {block : BlockId}
    {instructions : List Instr} {terminator : Terminator}
    (code : BlockCode checked block instructions terminator)
    (runtime : Runtime) (core : Core) (returns : List ReturnFrame) :
    step runtime checked (inFrame core block instructions.length returns) =
      executeTerminator checked terminator (inFrame core block instructions.length returns) := by
  simp [step, inFrame, UInt32.toNat_ofNat_of_lt' code.fits, code.found]

theorem BlockCode.jump_inFrame {checked : Checked} {block target : BlockId} {instructions : List Instr}
    (code : BlockCode checked block instructions (.jump target))
    (valid : checked.program.hasBlock target = true)
    (runtime : Runtime) (core : Core) (returns : List ReturnFrame) :
    step runtime checked (inFrame core block instructions.length returns) = inFrame core target 0 returns := by
  rw [code.terminator_inFrame]
  simp [executeTerminator, Machine.goto, valid, inFrame]

theorem BlockCode.branch_inFrame {checked : Checked} {block yes no : BlockId} {instructions : List Instr}
    {comparison : Compare} {condition : Condition}
    (code : BlockCode checked block instructions (.branch comparison condition yes no))
    (runtime : Runtime) (core : Core) (returns : List ReturnFrame) (answer : Bool)
    (holds : comparison.holds condition core = answer)
    (valid : checked.program.hasBlock (if answer then yes else no) = true) :
    step runtime checked (inFrame core block instructions.length returns) =
      inFrame core (if answer then yes else no) 0 returns := by
  rw [code.terminator_inFrame]
  simp [executeTerminator, inFrame, holds, Machine.goto, valid]

theorem Straight.Sequence.steps_inFrame {instructions : List Instr} {before after : Core}
    (sequence : Straight.Sequence instructions before after) (runtime : Runtime) (checked : Checked)
    (block : BlockId) (offset : Nat) (returns : List ReturnFrame)
    (segment : Straight.Segment checked block offset instructions)
    (fits : offset + instructions.length < UInt32.size) :
    Steps runtime checked instructions.length (inFrame before block offset returns)
      (inFrame after block (offset + instructions.length) returns) := by
  induction sequence generalizing offset with
  | nil core => simpa using Steps.refl (runtime := runtime) (checked := checked) (inFrame core block offset returns)
  | @cons instruction instructions before middle after first rest ih =>
      obtain ⟨code, found, reads⟩ := segment
      have offsetBound : offset < UInt32.size := by simp only [List.length_cons] at fits; omega
      have head := reads 0 (by simp)
      simp only [Nat.add_zero, List.getElem?_cons_zero] at head
      have one : step runtime checked (inFrame before block offset returns) =
          inFrame middle block (offset + 1) returns := by
        simp only [step, inFrame, UInt32.toNat_ofNat_of_lt' offsetBound, found, head]
        rw [first runtime checked _ rfl]
        exact inFrame_advance _ _ _ _ (by simp only [List.length_cons] at fits; omega)
      have next := ih (offset + 1) (Straight.Segment.tail ⟨code, found, reads⟩) (by
        simp only [List.length_cons] at fits
        omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Steps.cons one next

namespace Straight.Effect

theorem push (core : Core) (source : GPR)
    (allowed : Memory.rangeAllowed core.memory.writable (core.readReg .rsp - 8) 8 = true) :
    Effect (.push source) core
      { core.setReg .rsp (core.readReg .rsp - 8) with
        memory := core.memory.write64 (core.readReg .rsp - 8) (core.readReg source) } := by
  intro runtime checked machine equal
  simp [executeInstr, equal, Memory.write64?, Memory.write?, Width.bytes, allowed, Memory.write64]

theorem pop (core : Core) (destination : GPR) (value : Word)
    (allowed : Memory.rangeAllowed core.memory.readable (core.readReg .rsp) 8 = true)
    (loaded : core.memory.read64 (core.readReg .rsp) = value) :
    Effect (.pop destination) core ((core.setReg .rsp (core.readReg .rsp + 8)).setReg destination value) := by
  intro runtime checked machine equal
  simp [executeInstr, equal, Memory.read64?, Memory.read?, Width.bytes, allowed, Memory.read64] at *
  exact congrArg machine.advanceWith (by rw [loaded])

theorem allocFrame (core : Core) (size : FrameSize) :
    Effect (.allocFrame size) core (core.setReg .rsp (core.readReg .rsp - size.bytes)) := by
  intro runtime checked machine equal
  simp [executeInstr, equal]

theorem freeFrame (core : Core) (size : FrameSize) :
    Effect (.freeFrame size) core (core.setReg .rsp (core.readReg .rsp + size.bytes)) := by
  intro runtime checked machine equal
  simp [executeInstr, equal]

theorem spill (core : Core) (slot : StackSlot) (source : GPR)
    (allowed : Memory.rangeAllowed core.memory.writable (core.readReg .rbp - slot.displacement) 8 = true) :
    Effect (.spill slot source) core
      { core with memory := core.memory.write64 (core.readReg .rbp - slot.displacement) (core.readReg source) } := by
  intro runtime checked machine equal
  simp [executeInstr, equal, Core.storeReg?, Memory.write?, Width.bytes, allowed, Memory.write64] <;> rfl

theorem reload (core : Core) (destination : GPR) (slot : StackSlot) (value : Word)
    (allowed : Memory.rangeAllowed core.memory.readable (core.readReg .rbp - slot.displacement) 8 = true)
    (loaded : core.memory.read64 (core.readReg .rbp - slot.displacement) = value) :
    Effect (.reload destination slot) core (core.setReg destination value) := by
  intro runtime checked machine equal
  change core.memory.read .w64 (core.readReg .rbp - slot.displacement) = value at loaded
  simp [executeInstr, equal, Core.loadReg?, Memory.read?, Width.bytes, allowed,
    loaded] <;> rfl

end Straight.Effect
end Ix.Compiler.X86
