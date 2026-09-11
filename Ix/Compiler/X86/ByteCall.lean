import Ix.Compiler.X86.ByteControl

/-! Paired local CALL/RET effects. Return slots contain the typed continuation
token on one side and the physical byte RIP on the other. E2 must compose this
explicit difference through callees; neither equality nor an opaque step
simulation is assumed here. ABI diagnostics remain typed contracts. -/

namespace Ix.Compiler.X86.Encode

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

def typedCallState (machine : Machine) (target : BlockId) (continuation : PC) : Machine :=
  let stack := machine.core.readReg .rsp - 8
  { machine with
    core := { machine.core.setReg .rsp stack with memory := machine.core.memory.write64 stack continuation.encode }
    pc := ⟨target, 0⟩
    returns := ⟨continuation, stack, machine.core.calleeSavedSnapshot⟩ :: machine.returns }

def byteCallState (core : Core) (rip : Word) (flags : ByteEval.Flags) (displacement : Imm32) : ByteEval.State :=
  let stack := core.readReg .rsp - 8
  { core := { core.setReg .rsp stack with memory := core.memory.write64 stack (rip + 5) }
    rip := ByteEval.relative (rip + 5) displacement
    flags }

/-- Both models push an eight-byte return slot and update the same registers.
The values in that slot are stated separately, without conflating PCs. -/
theorem call_pair (runtime : Runtime) (checked : Checked) (machine : Machine)
    (target : BlockId) (continuation : PC) (rip : Word) (flags : ByteEval.Flags) (displacement : Imm32)
    (aligned : SysV.callSiteAligned (machine.core.readReg .rsp) = true)
    (valid : checked.program.hasBlock target = true) (next : machine.pc.next? = some continuation)
    (writable : Memory.rangeAllowed machine.core.memory.writable (machine.core.readReg .rsp - 8) 8 = true) :
    executeInstr runtime checked (.call target) machine = typedCallState machine target continuation ∧
    ByteEval.step (byte 0xe8 ++ imm32Bytes displacement) rip ⟨machine.core, rip, flags⟩ =
      .ok (byteCallState machine.core rip flags displacement) ∧
    (typedCallState machine target continuation).core.registers =
      (byteCallState machine.core rip flags displacement).core.registers ∧
    (typedCallState machine target continuation).core.memory.read64 (machine.core.readReg .rsp - 8) = continuation.encode ∧
    (byteCallState machine.core rip flags displacement).core.memory.read64 (machine.core.readReg .rsp - 8) = rip + 5 := by
  rw [call_bytes_execution displacement ⟨machine.core, rip, flags⟩]
  simp [executeInstr, aligned, valid, next, Memory.write64?, Memory.write?, Width.bytes,
    writable, typedCallState, byteCallState, Memory.read64_write64]
  exact ⟨rfl, rfl⟩

theorem call_fault (runtime : Runtime) (checked : Checked) (machine : Machine)
    (target : BlockId) (continuation : PC) (rip : Word) (flags : ByteEval.Flags) (displacement : Imm32)
    (aligned : SysV.callSiteAligned (machine.core.readReg .rsp) = true)
    (valid : checked.program.hasBlock target = true) (next : machine.pc.next? = some continuation)
    (denied : Memory.rangeAllowed machine.core.memory.writable (machine.core.readReg .rsp - 8) 8 = false) :
    let fault : MemoryFault := ⟨.write, machine.core.readReg .rsp - 8, 8⟩
    executeInstr runtime checked (.call target) machine = machine.trap (.memoryFault fault) ∧
    ByteEval.step (byte 0xe8 ++ imm32Bytes displacement) rip ⟨machine.core, rip, flags⟩ = .error (.memory fault) := by
  rw [call_bytes_execution displacement ⟨machine.core, rip, flags⟩]
  simp [executeInstr, aligned, valid, next, Memory.write64?, Memory.write?, Width.bytes, denied]

/-- A matched pair of concrete return-slot reads suffices for local return
agreement. Establishing those reads across a complete callee is the stream
simulation's responsibility. The caller's memory may store physical RIPs. -/
theorem ret_pair (checked : Checked) (machine : Machine) (frame : ReturnFrame) (rest : List ReturnFrame)
    (physicalMemory : Memory) (rip target : Word) (flags : ByteEval.Flags)
    (returns : machine.returns = frame :: rest)
    (stack : machine.core.readReg .rsp = frame.returnSlot)
    (typedRead : machine.core.memory.read64? frame.returnSlot = .ok frame.continuation.encode)
    (physicalRead : physicalMemory.read64? frame.returnSlot = .ok target)
    (saved : machine.core.calleeSavedMatch frame.calleeSaved = true) :
    executeTerminator checked .ret machine =
      { machine with core := machine.core.setReg .rsp (frame.returnSlot + 8), pc := frame.continuation, returns := rest } ∧
    ByteEval.step (byte 0xc3) rip ⟨{ machine.core with memory := physicalMemory }, rip, flags⟩ =
      .ok ⟨({ machine.core with memory := physicalMemory } : Core).setReg .rsp (frame.returnSlot + 8), target, flags⟩ := by
  constructor
  · simp [executeTerminator, returns, stack, typedRead, saved]
  · rw [ret_bytes_execution ⟨{ machine.core with memory := physicalMemory }, rip, flags⟩]
    change (match physicalMemory.read64? (machine.core.readReg .rsp) with
      | .error fault => _ | .ok target => _) = _
    rw [stack, physicalRead]
    change Except.ok ({
      core := ({ machine.core with memory := physicalMemory } : Core).setReg .rsp (machine.core.readReg .rsp + 8)
      rip := target, flags } : ByteEval.State) = _
    rw [stack]

/-- Named runtime calls use the same physical CALL form. Their typed atomic
invocation is still an external procedure contract, outside local encoding. -/
theorem runtime_call_form (intrinsic : Intrinsic) :
    (encodeInstr (.callRuntime intrinsic)).bytes = byte 0xe8 ++ imm32Bytes 0 := by
  simp [encodeInstr, rel32, imm32_zero_bytes]

end Ix.Compiler.X86.Encode
