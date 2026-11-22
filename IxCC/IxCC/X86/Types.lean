import Std

/-!
# Primitive x86-64 target vocabulary

Registers, widths, addresses, conditions and the System V register
convention. The instruction table (`X86.Table`), the typed program syntax
(`X86.Basic`) and both machines build on these types. Memory operands
separate index registers from general registers, excluding the x86
`rsp`-as-index encoding hole by type.
-/

namespace IxCC.X86

abbrev Word := UInt64
abbrev Imm32 := UInt32
abbrev BlockId := UInt32

/-- The sixteen integer registers in 64-bit mode. -/
inductive GPR where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Registers accepted in the SIB index position.  `rsp` has no constructor:
the corresponding encoding means "no index" on x86-64. -/
inductive IndexReg where
  | rax | rcx | rdx | rbx | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def IndexReg.gpr : IndexReg → GPR
  | .rax => .rax
  | .rcx => .rcx
  | .rdx => .rdx
  | .rbx => .rbx
  | .rbp => .rbp
  | .rsi => .rsi
  | .rdi => .rdi
  | .r8 => .r8
  | .r9 => .r9
  | .r10 => .r10
  | .r11 => .r11
  | .r12 => .r12
  | .r13 => .r13
  | .r14 => .r14
  | .r15 => .r15

inductive Width where
  | w8 | w16 | w32 | w64
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Width.bits : Width → Nat
  | .w8 => 8
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64

def Width.bytes : Width → Nat
  | .w8 => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8

def Width.mask : Width → Word
  | .w8 => 0xff
  | .w16 => 0xffff
  | .w32 => 0xffffffff
  | .w64 => 0xffffffffffffffff

/-- Widths with a two-operand integer `imul` encoding.  Byte multiplication
has a different implicit-register shape and is outside this AST form. -/
inductive MulWidth where
  | w16 | w32 | w64
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def MulWidth.width : MulWidth → Width
  | .w16 => .w16
  | .w32 => .w32
  | .w64 => .w64

inductive Scale where
  | one | two | four | eight
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Scale.word : Scale → Word
  | .one => 1
  | .two => 2
  | .four => 4
  | .eight => 8

/-- An encodable x86 base/index/scale/signed-disp32 address.  `displacement`
is the two's-complement bit pattern of the signed 32-bit displacement. -/
structure MemAddr where
  base : Option GPR := none
  index : Option IndexReg := none
  scale : Scale := .one
  displacement : Imm32 := 0
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Stack allocation is intrinsically 16-byte aligned and bounded. -/
structure FrameSize where
  units16 : UInt16
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def FrameSize.bytes (size : FrameSize) : Word :=
  size.units16.toUInt64 * 16

/-- A spill slot is an eight-byte cell below `rbp`.  The `UInt16` index keeps
its negative displacement well inside the signed-disp32 encoding range. -/
structure StackSlot where
  index : UInt16
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def StackSlot.displacement (slot : StackSlot) : Word :=
  (slot.index.toUInt64 + 1) * 8

inductive MoveSource where
  | reg (source : GPR)
  | imm (value : Word)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive AluSource where
  | reg (source : GPR)
  /-- A sign-extended imm32 when used at width 64. -/
  | imm (value : Imm32)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive AluOp where
  | add | sub | and | or | xor
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive Condition where
  | eq | ne
  | unsignedLt | unsignedLe | unsignedGt | unsignedGe
  | signedLt | signedLe | signedGt | signedGe
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Compare where
  width : Width
  left : GPR
  right : AluSource
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- The named runtime surface reachable from v0 target code. `unsignedDiv`
predates the table's `div` row; runtime calls retire with D10. -/
inductive Intrinsic where
  | allocate
  | reserve
  | reuse
  | releaseReservation
  | retainShared
  | releaseShared
  | memcpy
  | unsignedDiv
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Intrinsic.arity : Intrinsic → Nat
  | .allocate => 2
  | .reserve => 2
  | .reuse => 3
  | .releaseReservation => 1
  | .retainShared => 1
  | .releaseShared => 1
  | .memcpy => 3
  | .unsignedDiv => 2

/-! ## System V register convention -/

namespace SysV

def argumentRegisters : Array GPR :=
  #[.rdi, .rsi, .rdx, .rcx, .r8, .r9]

def resultRegister : GPR := .rax
def stackPointer : GPR := .rsp
def framePointer : GPR := .rbp

/-- System V function entry observes the return address already pushed. -/
def functionEntryAligned (stack : Word) : Bool := stack % 16 == 8

/-- Immediately before `call`, the caller has restored 16-byte alignment. -/
def callSiteAligned (stack : Word) : Bool := stack % 16 == 0

def calleeSaved : Array GPR :=
  #[.rbx, .rbp, .r12, .r13, .r14, .r15]

def callerSaved : Array GPR :=
  #[.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

def argumentRegister? (index : Nat) : Option GPR :=
  argumentRegisters[index]?

def isCallerSaved (register : GPR) : Bool :=
  callerSaved.contains register

end SysV

end IxCC.X86
