import Ix.Compiler.X86.FrameExecution

namespace Ix.Compiler.X86

theorem PC.next_ofNat (block : BlockId) {offset : Nat} (fits : offset + 1 < UInt32.size) :
    (PC.mk block (UInt32.ofNat offset)).next? = some ⟨block, UInt32.ofNat (offset + 1)⟩ := by
  have notLast : UInt32.ofNat offset ≠ 0xffffffff := by
    intro equal
    have equal := congrArg UInt32.toNat equal
    rw [UInt32.toNat_ofNat_of_lt' (by omega)] at equal
    change offset = 4294967295 at equal
    simp only [UInt32.size] at fits
    omega
  simp [PC.next?, notLast, UInt32.ofNat_add]

theorem Straight.Segment.instruction_inFrame {checked : Checked} {block : BlockId}
    {offset : Nat} {instruction : Instr}
    (segment : Straight.Segment checked block offset [instruction])
    (fits : offset < UInt32.size) (runtime : Runtime) (core : Core) (returns : List ReturnFrame) :
    step runtime checked (inFrame core block offset returns) =
      executeInstr runtime checked instruction (inFrame core block offset returns) := by
  obtain ⟨code, found, reads⟩ := segment
  have head := reads 0 (by simp)
  simp only [Nat.add_zero, List.getElem?_cons_zero] at head
  simp [step, inFrame, UInt32.toNat_ofNat_of_lt' fits, found, head]

def callFrame (core : Core) (block : BlockId) (offset : Nat) : ReturnFrame := {
  continuation := ⟨block, UInt32.ofNat (offset + 1)⟩
  returnSlot := core.readReg .rsp - 8
  calleeSaved := core.calleeSavedSnapshot }

def callCore (core : Core) (block : BlockId) (offset : Nat) : Core :=
  { core.setReg .rsp (core.readReg .rsp - 8) with
    memory := core.memory.write64 (core.readReg .rsp - 8) (callFrame core block offset).continuation.encode }

/-- CALL's complete typed effect, including the real stack write and saved
register snapshot. The caller supplies finite memory capacity and alignment. -/
theorem call_inFrame {checked : Checked} {block target : BlockId} {offset : Nat}
    (segment : Straight.Segment checked block offset [.call target])
    (fits : offset + 1 < UInt32.size) (valid : checked.program.hasBlock target = true)
    (runtime : Runtime) (core : Core) (returns : List ReturnFrame)
    (aligned : SysV.callSiteAligned (core.readReg .rsp) = true)
    (writable : Memory.rangeAllowed core.memory.writable (core.readReg .rsp - 8) 8 = true) :
    step runtime checked (inFrame core block offset returns) =
      inFrame (callCore core block offset) target 0 (callFrame core block offset :: returns) := by
  rw [segment.instruction_inFrame (by omega)]
  simp only [executeInstr, inFrame, aligned, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    valid, PC.next_ofNat block fits]
  simp [Memory.write64?, Memory.write?, Width.bytes, writable, callCore, callFrame, Memory.write64]

/-- A callee returns to the actual stored continuation after restoring its
entry stack pointer and the System V saved-register set. -/
theorem BlockCode.ret_inFrame {checked : Checked} {block : BlockId} {instructions : List Instr}
    (code : BlockCode checked block instructions .ret)
    (runtime : Runtime) (core : Core) (frame : ReturnFrame) (returns : List ReturnFrame)
    (stack : core.readReg .rsp = frame.returnSlot)
    (readable : core.memory.read64? frame.returnSlot = .ok frame.continuation.encode)
    (saved : core.calleeSavedMatch frame.calleeSaved = true) :
    step runtime checked (inFrame core block instructions.length (frame :: returns)) =
      { core := core.setReg .rsp (frame.returnSlot + 8), pc := frame.continuation,
        returns, status := .running } := by
  rw [code.terminator_inFrame]
  simp [executeTerminator, inFrame, stack, readable, saved]

end Ix.Compiler.X86
