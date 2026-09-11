import Ix.Compiler.X86.Basic

/-!
# Executable local semantics for the typed x86-64 v0 fragment

The model is intentionally architectural where the first encoder bridge needs
it to be: fixed-width registers, little-endian byte memory, observable `rsp`
effects, call return slots, and normal/trap outcomes.  A PC is still a symbolic
block/operation pair.  Calls store its stable 64-bit structural token in the
modeled stack; the later layout proof relates that token to the encoded return
RIP.

Runtime intrinsics are supplied as an explicit semantic parameter.  Their
result type can mutate memory and caller-saved registers only, so preservation
of the System V callee-saved set and `rsp` is structural rather than a promise
made by an opaque callback.

`misalignedCall`, `stackMismatch`, `corruptReturn`, and
`calleeSavedClobber` are compiler/ABI contract failures, not claims that the
processor raises corresponding architectural exceptions. A native refinement
must prove those cases unreachable. Likewise, a top-level `ret` is observed as
halt rather than executing the surrounding harness's return instruction.
-/

namespace Ix.Compiler.X86

abbrev Registers := GPR → Word

inductive AccessKind where
  | read | write
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure MemoryFault where
  access : AccessKind
  address : Word
  bytes : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Byte memory with explicit read/write mappings.  Permissions are checked
for every byte touched, including call return slots and spill accesses. -/
structure Memory where
  bytes : Word → UInt8
  readable : Word → Bool
  writable : Word → Bool

namespace Registers

def zero : Registers := fun _ => 0

def set (registers : Registers) (register : GPR) (value : Word) : Registers :=
  fun candidate => if candidate == register then value else registers candidate

end Registers

namespace Memory

def flat : Memory :=
  { bytes := fun _ => 0
    readable := fun _ => true
    writable := fun _ => true }

def unmapped : Memory :=
  { bytes := fun _ => 0
    readable := fun _ => false
    writable := fun _ => false }

def writeByte (memory : Memory) (address : Word) (value : UInt8) : Memory :=
  { memory with
    bytes := fun candidate =>
      if candidate == address then value else memory.bytes candidate }

def rangeAllowed (permission : Word → Bool) (address : Word) : Nat → Bool
  | 0 => true
  | count + 1 =>
      rangeAllowed permission address count &&
        permission (address + UInt64.ofNat count)

def readLittle (memory : Memory) (address : Word) : Nat → Word
  | 0 => 0
  | count + 1 =>
      memory.readLittle address count |||
        (memory.bytes (address + UInt64.ofNat count)).toUInt64 <<<
          UInt64.ofNat (8 * count)

def writeLittle (memory : Memory) (address value : Word) : Nat → Memory
  | 0 => memory
  | count + 1 =>
      (memory.writeLittle address value count).writeByte
        (address + UInt64.ofNat count)
        ((value >>> UInt64.ofNat (8 * count)).toUInt8)

def read (memory : Memory) (width : Width) (address : Word) : Word :=
  memory.readLittle address width.bytes

def write (memory : Memory) (width : Width) (address value : Word) : Memory :=
  memory.writeLittle address value width.bytes

def read64 (memory : Memory) (address : Word) : Word :=
  memory.read .w64 address

def write64 (memory : Memory) (address value : Word) : Memory :=
  memory.write .w64 address value

def read? (memory : Memory) (width : Width) (address : Word) :
    Except MemoryFault Word :=
  if Memory.rangeAllowed memory.readable address width.bytes then
    .ok (memory.read width address)
  else
    .error { access := .read, address, bytes := width.bytes }

def write? (memory : Memory) (width : Width) (address value : Word) :
    Except MemoryFault Memory :=
  if Memory.rangeAllowed memory.writable address width.bytes then
    .ok (memory.write width address value)
  else
    .error { access := .write, address, bytes := width.bytes }

def read64? (memory : Memory) (address : Word) : Except MemoryFault Word :=
  memory.read? .w64 address

def write64? (memory : Memory) (address value : Word) :
    Except MemoryFault Memory :=
  memory.write? .w64 address value

end Memory

def signExtend32 (value : Imm32) : Word :=
  let raw := value.toUInt64
  if value < 0x80000000 then raw else raw ||| 0xffffffff00000000

def Width.truncate (width : Width) (value : Word) : Word :=
  value &&& width.mask

/-- Signed mathematical interpretation of the low `width` bits. -/
def Width.signedValue (width : Width) (value : Word) : Int :=
  let unsigned := (width.truncate value).toNat
  let sign := 2 ^ (width.bits - 1)
  let modulus := 2 ^ width.bits
  if unsigned < sign then
    Int.ofNat unsigned
  else
    Int.ofNat unsigned - Int.ofNat modulus

structure Core where
  registers : Registers
  memory : Memory

namespace Core

def empty (stackTop : Word := 0) : Core :=
  { registers := Registers.zero.set .rsp stackTop
    memory := Memory.flat }

def readReg (core : Core) (register : GPR) : Word :=
  core.registers register

def setReg (core : Core) (register : GPR) (value : Word) : Core :=
  { core with registers := core.registers.set register value }

/-- Architectural low-register writes: 32-bit destinations clear their upper
half, while 8/16-bit destinations preserve it. -/
def writeReg (core : Core) (width : Width) (register : GPR)
    (value : Word) : Core :=
  match width with
  | .w64 => core.setReg register value
  | .w32 => core.setReg register (width.truncate value)
  | .w8 | .w16 =>
      let old := core.readReg register
      let highMask := 0xffffffffffffffff ^^^ width.mask
      core.setReg register
        ((old &&& highMask) ||| width.truncate value)

def loadReg? (core : Core) (width : Width) (register : GPR)
    (address : Word) : Except MemoryFault Core := do
  let value ← core.memory.read? width address
  return core.setReg register (width.truncate value)

def storeReg? (core : Core) (width : Width) (address : Word)
    (register : GPR) : Except MemoryFault Core := do
  let memory ← core.memory.write? width address (core.readReg register)
  return { core with memory }

end Core

def MemAddr.eval (address : MemAddr) (core : Core) : Word :=
  let base := match address.base with
    | none => 0
    | some register => core.readReg register
  let index := match address.index with
    | none => 0
    | some register => core.readReg register.gpr * address.scale.word
  base + index + signExtend32 address.displacement

def MoveSource.eval (source : MoveSource) (core : Core) : Word :=
  match source with
  | .reg register => core.readReg register
  | .imm value => value

def AluSource.eval (source : AluSource) (core : Core) : Word :=
  match source with
  | .reg register => core.readReg register
  | .imm value => signExtend32 value

def AluOp.eval (operation : AluOp) (left right : Word) : Word :=
  match operation with
  | .add => left + right
  | .sub => left - right
  | .and => left &&& right
  | .or => left ||| right
  | .xor => left ^^^ right

def Condition.holds (condition : Condition) (width : Width)
    (left right : Word) : Bool :=
  let leftUnsigned := width.truncate left
  let rightUnsigned := width.truncate right
  match condition with
  | .eq => leftUnsigned == rightUnsigned
  | .ne => leftUnsigned != rightUnsigned
  | .unsignedLt => decide (leftUnsigned < rightUnsigned)
  | .unsignedLe => decide (leftUnsigned ≤ rightUnsigned)
  | .unsignedGt => decide (leftUnsigned > rightUnsigned)
  | .unsignedGe => decide (leftUnsigned ≥ rightUnsigned)
  | .signedLt => decide (width.signedValue left < width.signedValue right)
  | .signedLe => decide (width.signedValue left ≤ width.signedValue right)
  | .signedGt => decide (width.signedValue left > width.signedValue right)
  | .signedGe => decide (width.signedValue left ≥ width.signedValue right)

def Compare.holds (comparison : Compare) (condition : Condition)
    (core : Core) : Bool :=
  condition.holds comparison.width (core.readReg comparison.left)
    (comparison.right.eval core)

/-- Symbolic instruction position.  Its encoding is a stable stack token, not
an emitted byte address; encoder correctness will relate the two. -/
structure PC where
  block : BlockId
  offset : UInt32
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def PC.encode (pc : PC) : Word :=
  (pc.block.toUInt64 <<< 32) ||| pc.offset.toUInt64

def PC.decode (word : Word) : PC :=
  { block := (word >>> 32).toUInt32
    offset := word.toUInt32 }

def PC.next? (pc : PC) : Option PC :=
  if pc.offset == (0xffffffff : UInt32) then
    none
  else
    some { pc with offset := pc.offset + 1 }

structure ReturnFrame where
  continuation : PC
  returnSlot : Word
  calleeSaved : Array Word
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive Trap where
  | invalidBlock (block : BlockId)
  | invalidOffset (pc : PC)
  | pcOverflow (pc : PC)
  | memoryFault (fault : MemoryFault)
  | misalignedCall (stack : Word)
  | stackMismatch (expected actual : Word)
  | corruptReturn (expected actual : Word)
  | calleeSavedClobber
  | intrinsicFailure (intrinsic : Intrinsic) (code : Nat)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive Status where
  | running
  | halted (result : Word)
  | trapped (fault : Trap)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Machine where
  core : Core
  pc : PC
  returns : List ReturnFrame
  status : Status

/-- An intrinsic can change memory, the result register, and caller-saved
registers.  There is no field through which it can mutate `rsp` or a
callee-saved register. -/
structure IntrinsicResult where
  memory : Memory
  result : Word
  clobber : GPR → Word

structure Runtime where
  invoke : Intrinsic → Array Word → Memory →
    Except Nat IntrinsicResult

def Runtime.rejecting : Runtime where
  invoke intrinsic _ _ := .error intrinsic.arity

def Core.calleeSavedSnapshot (core : Core) : Array Word :=
  SysV.calleeSaved.map core.readReg

def Core.calleeSavedMatch (core : Core) (snapshot : Array Word) : Bool :=
  core.calleeSavedSnapshot == snapshot

def Core.intrinsicArguments (core : Core) (intrinsic : Intrinsic) : Array Word :=
  (List.range intrinsic.arity).toArray.map fun index =>
    match SysV.argumentRegister? index with
    | some register => core.readReg register
    | none => 0

def Core.applyIntrinsicResult (core : Core)
    (result : IntrinsicResult) : Core :=
  { memory := result.memory
    registers := fun register =>
      if register == SysV.resultRegister then
        result.result
      else if SysV.isCallerSaved register then
        result.clobber register
      else
        core.readReg register }

/-- An atomic runtime call cannot change the architectural stack pointer. -/
@[simp] theorem Core.applyIntrinsicResult_rsp (core : Core)
    (result : IntrinsicResult) :
    (core.applyIntrinsicResult result).readReg .rsp = core.readReg .rsp := by
  simp [Core.applyIntrinsicResult, Core.readReg, SysV.isCallerSaved,
    SysV.callerSaved, SysV.resultRegister]

/-- An atomic runtime call preserves the complete System V callee-saved
snapshot by construction. -/
@[simp] theorem Core.applyIntrinsicResult_calleeSaved (core : Core)
    (result : IntrinsicResult) :
    (core.applyIntrinsicResult result).calleeSavedSnapshot =
      core.calleeSavedSnapshot := by
  simp [Core.calleeSavedSnapshot, SysV.calleeSaved,
    Core.applyIntrinsicResult, Core.readReg, SysV.isCallerSaved,
    SysV.callerSaved, SysV.resultRegister]

def Machine.trap (machine : Machine) (fault : Trap) : Machine :=
  { machine with status := .trapped fault }

def Machine.advanceWith (machine : Machine) (core : Core) : Machine :=
  match machine.pc.next? with
  | none => machine.trap (.pcOverflow machine.pc)
  | some next => { machine with core, pc := next }

def Machine.goto (checked : Checked) (machine : Machine)
    (target : BlockId) : Machine :=
  if checked.program.hasBlock target then
    { machine with pc := { block := target, offset := 0 } }
  else
    machine.trap (.invalidBlock target)

def executeInstr (runtime : Runtime) (checked : Checked)
    (instruction : Instr) (machine : Machine) : Machine :=
  let core := machine.core
  match instruction with
  | .mov width destination source =>
      machine.advanceWith (core.writeReg width destination (source.eval core))
  | .load width destination source =>
      match core.loadReg? width destination (source.eval core) with
      | .error fault => machine.trap (.memoryFault fault)
      | .ok loaded => machine.advanceWith loaded
  | .store width destination source =>
      match core.storeReg? width (destination.eval core) source with
      | .error fault => machine.trap (.memoryFault fault)
      | .ok stored => machine.advanceWith stored
  | .lea destination source =>
      machine.advanceWith (core.setReg destination (source.eval core))
  | .alu operation width destination source =>
      machine.advanceWith
        (core.writeReg width destination
          (operation.eval (core.readReg destination) (source.eval core)))
  | .imul width destination source =>
      machine.advanceWith
        (core.writeReg width.width destination
          (core.readReg destination * core.readReg source))
  | .push source =>
      let stack := core.readReg .rsp - 8
      match core.memory.write64? stack (core.readReg source) with
      | .error fault => machine.trap (.memoryFault fault)
      | .ok memory =>
          machine.advanceWith { core.setReg .rsp stack with memory }
  | .pop destination =>
      let stack := core.readReg .rsp
      match core.memory.read64? stack with
      | .error fault => machine.trap (.memoryFault fault)
      | .ok value =>
          let popped := (core.setReg .rsp (stack + 8)).setReg destination value
          machine.advanceWith popped
  | .allocFrame size =>
      machine.advanceWith
        (core.setReg .rsp (core.readReg .rsp - size.bytes))
  | .freeFrame size =>
      machine.advanceWith
        (core.setReg .rsp (core.readReg .rsp + size.bytes))
  | .spill slot source =>
      let address := core.readReg .rbp - slot.displacement
      match core.storeReg? .w64 address source with
      | .error fault => machine.trap (.memoryFault fault)
      | .ok stored => machine.advanceWith stored
  | .reload destination slot =>
      let address := core.readReg .rbp - slot.displacement
      match core.loadReg? .w64 destination address with
      | .error fault => machine.trap (.memoryFault fault)
      | .ok loaded => machine.advanceWith loaded
  | .call target =>
      if !SysV.callSiteAligned (core.readReg .rsp) then
        machine.trap (.misalignedCall (core.readReg .rsp))
      else if checked.program.hasBlock target then
        match machine.pc.next? with
        | none => machine.trap (.pcOverflow machine.pc)
        | some continuation =>
            let stack := core.readReg .rsp - 8
            match core.memory.write64? stack continuation.encode with
            | .error fault => machine.trap (.memoryFault fault)
            | .ok memory =>
                let frame : ReturnFrame :=
                  { continuation
                    returnSlot := stack
                    calleeSaved := core.calleeSavedSnapshot }
                let called := { core.setReg .rsp stack with memory }
                { machine with
                  core := called
                  pc := { block := target, offset := 0 }
                  returns := frame :: machine.returns }
      else
        machine.trap (.invalidBlock target)
  | .callRuntime intrinsic =>
      if !SysV.callSiteAligned (core.readReg .rsp) then
        machine.trap (.misalignedCall (core.readReg .rsp))
      else
        match runtime.invoke intrinsic (core.intrinsicArguments intrinsic)
            core.memory with
        | .error code => machine.trap (.intrinsicFailure intrinsic code)
        | .ok result => machine.advanceWith (core.applyIntrinsicResult result)

def executeTerminator (checked : Checked) (terminator : Terminator)
    (machine : Machine) : Machine :=
  let core := machine.core
  match terminator with
  | .jump target => machine.goto checked target
  | .branch comparison condition ifTrue ifFalse =>
      machine.goto checked
        (if comparison.holds condition core then ifTrue else ifFalse)
  | .tailCall target => machine.goto checked target
  | .ret =>
      match machine.returns with
      | [] => { machine with status := .halted (core.readReg .rax) }
      | frame :: returns =>
          let stack := core.readReg .rsp
          if stack != frame.returnSlot then
            machine.trap (.stackMismatch frame.returnSlot stack)
          else
            match core.memory.read64? stack with
            | .error fault => machine.trap (.memoryFault fault)
            | .ok actual =>
                let expected := frame.continuation.encode
                if actual != expected then
                  machine.trap (.corruptReturn expected actual)
                else if !core.calleeSavedMatch frame.calleeSaved then
                  machine.trap .calleeSavedClobber
                else
                  { machine with
                    core := core.setReg .rsp (stack + 8)
                    pc := frame.continuation
                    returns }

def Machine.initial (checked : Checked) (core : Core) : Machine :=
  { core
    pc := { block := checked.program.entry, offset := 0 }
    returns := []
    status := .running }

/-- One target step.  A block's terminator occupies the position immediately
after its instruction array. -/
def step (runtime : Runtime) (checked : Checked)
    (machine : Machine) : Machine :=
  match machine.status with
  | .halted _ | .trapped _ => machine
  | .running =>
      match checked.program.blocks[machine.pc.block.toNat]? with
      | none => machine.trap (.invalidBlock machine.pc.block)
      | some block =>
          match block.instructions[machine.pc.offset.toNat]? with
          | some instruction => executeInstr runtime checked instruction machine
          | none =>
              if machine.pc.offset.toNat == block.instructions.size then
                executeTerminator checked block.terminator machine
              else
                machine.trap (.invalidOffset machine.pc)

def run (runtime : Runtime) (checked : Checked) : Nat → Machine → Machine
  | 0, machine => machine
  | fuel + 1, machine =>
      let next := step runtime checked machine
      match next.status with
      | .running => run runtime checked fuel next
      | .halted _ | .trapped _ => next

def runFrom (runtime : Runtime) (checked : Checked) (fuel : Nat)
    (core : Core) : Machine :=
  run runtime checked fuel (Machine.initial checked core)

/-- Finished target states are stable under a further local step. -/
theorem step_of_not_running (runtime : Runtime) (checked : Checked)
    (machine : Machine) (notRunning : machine.status ≠ .running) :
    step runtime checked machine = machine := by
  cases status : machine.status with
  | running => exact False.elim (notRunning status)
  | halted result => simp [step, status]
  | trapped fault => simp [step, status]

end Ix.Compiler.X86
