import Compilatrix.X86.Types

/-!
# Architectural machine state

Fixed-width registers and little-endian byte memory with explicit per-byte
read/write permissions. The instruction table executes its rows over this
state, and both the typed machine (`Eval`) and the byte machine (`ByteEval`)
share it. Permissions are checked for every byte touched, including call
return slots and spill accesses.
-/

namespace Compilatrix.X86

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

end Compilatrix.X86
