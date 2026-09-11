import Std

/-!
# Typed x86-64 v0 target syntax

This is the proof-facing target boundary for the first native wedge.  It is
deliberately not an encoder: branch and call destinations are bounded symbolic
block identifiers, and every constructor denotes only an instruction form in
the reviewed sequential System V subset.  Byte layout and relocation belong
to the later encoder/object layer.

The AST combines compare-and-branch into one target operation.  This keeps
EFLAGS local by construction while still allowing the encoder to emit the
usual `cmp`/`jcc` pair.  Memory operands also separate index registers from
general registers, excluding the x86 `rsp`-as-index encoding hole by type.
-/

namespace Ix.Compiler.X86

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

/-- The named runtime surface reachable from v0 target code.  General division
is deliberately a runtime call rather than an x86 `div` instruction. -/
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

/-- Non-control target operations.  Operand restrictions are represented by
the constructors: there is no memory-to-memory ALU form, no arbitrary runtime
symbol, no indirect call, and no raw byte escape hatch. -/
inductive Instr where
  | mov (width : Width) (destination : GPR) (source : MoveSource)
  /-- Narrow loads are zero-extending (`movzx`); w32 follows the architectural
  zero-extension rule and w64 is a normal move. -/
  | load (width : Width) (destination : GPR) (source : MemAddr)
  | store (width : Width) (destination : MemAddr) (source : GPR)
  | lea (destination : GPR) (source : MemAddr)
  | alu (operation : AluOp) (width : Width) (destination : GPR)
      (source : AluSource)
  | imul (width : MulWidth) (destination source : GPR)
  | push (source : GPR)
  | pop (destination : GPR)
  | allocFrame (size : FrameSize)
  | freeFrame (size : FrameSize)
  | spill (slot : StackSlot) (source : GPR)
  | reload (destination : GPR) (slot : StackSlot)
  | call (target : BlockId)
  | callRuntime (intrinsic : Intrinsic)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Control operations close a target block.  A conditional branch owns its
comparison, so no later operation can consume stale EFLAGS. -/
inductive Terminator where
  | jump (target : BlockId)
  | branch (comparison : Compare) (condition : Condition)
      (ifTrue ifFalse : BlockId)
  | tailCall (target : BlockId)
  | ret
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Block where
  instructions : Array Instr
  terminator : Terminator
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Blocks form one linked target text world.  Function symbols and local
labels both resolve to block IDs before this semantics, but byte offsets do
not: instruction encoding remains a separate pass. -/
structure Program where
  blocks : Array Block
  entry : BlockId
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

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

/-! ## Closed-fragment theorem -/

/-- A vocabulary wider than the v0 AST, used to state what remains excluded. -/
inductive Form where
  | move | load | store | address | arithmetic | multiply
  | stack | spill | reload | directCall | runtimeCall
  | jump | compareBranch | tailCall | ret
  | scalarDivision | float | simd | atomic | indirectCall | syscall | tls
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- The reviewed sequential v0 emitted fragment. -/
def Form.InV0 : Form → Prop
  | .move | .load | .store | .address | .arithmetic | .multiply
  | .stack | .spill | .reload | .directCall | .runtimeCall
  | .jump | .compareBranch | .tailCall | .ret => True
  | .scalarDivision | .float | .simd | .atomic | .indirectCall | .syscall
  | .tls => False

def Instr.form : Instr → Form
  | .mov .. => .move
  | .load .. => .load
  | .store .. => .store
  | .lea .. => .address
  | .alu .. => .arithmetic
  | .imul .. => .multiply
  | .push .. | .pop .. | .allocFrame .. | .freeFrame .. => .stack
  | .spill .. => .spill
  | .reload .. => .reload
  | .call .. => .directCall
  | .callRuntime .. => .runtimeCall

def Terminator.form : Terminator → Form
  | .jump .. => .jump
  | .branch .. => .compareBranch
  | .tailCall .. => .tailCall
  | .ret => .ret

/-- Unsupported ISA forms cannot be constructed as v0 instructions. -/
theorem Instr.inV0 (instruction : Instr) : instruction.form.InV0 := by
  cases instruction <;> trivial

/-- Unsupported ISA forms cannot be constructed as v0 terminators. -/
theorem Terminator.inV0 (terminator : Terminator) : terminator.form.InV0 := by
  cases terminator <;> trivial

def Block.InV0 (block : Block) : Prop :=
  (∀ instruction ∈ block.instructions, instruction.form.InV0) ∧
    block.terminator.form.InV0

def Program.InV0 (program : Program) : Prop :=
  ∀ block ∈ program.blocks, block.InV0

/-- Fragment containment is structural: validation cannot widen the emitted
ISA because the target AST has no constructor for an excluded form. -/
theorem Program.inV0 (program : Program) : program.InV0 := by
  intro block blockMember
  constructor
  · intro instruction instructionMember
    exact instruction.inV0
  · exact block.terminator.inV0

/-! ## Bounded control validation -/

def Program.hasBlock (program : Program) (target : BlockId) : Bool :=
  decide (target.toNat < program.blocks.size)

def Instr.targetsValid (program : Program) : Instr → Bool
  | .call target => program.hasBlock target
  | _ => true

def Terminator.targetsValid (program : Program) : Terminator → Bool
  | .jump target | .tailCall target => program.hasBlock target
  | .branch _ _ ifTrue ifFalse =>
      program.hasBlock ifTrue && program.hasBlock ifFalse
  | .ret => true

def Block.targetsValid (program : Program) (block : Block) : Bool :=
  block.instructions.all (Instr.targetsValid program) &&
    block.terminator.targetsValid program

def Block.offsetsFit (block : Block) : Bool :=
  decide (block.instructions.size < 2 ^ 32)

def Program.wellFormed (program : Program) : Bool :=
  !program.blocks.isEmpty &&
    decide (program.blocks.size < 2 ^ 32) &&
    program.hasBlock program.entry &&
    program.blocks.all fun block =>
      block.offsetsFit && block.targetsValid program

structure Checked where
  program : Program
  valid : program.wellFormed = true

inductive ValidationError where
  | malformedControl
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Program.check (program : Program) : Except ValidationError Checked :=
  if valid : program.wellFormed = true then
    .ok ⟨program, valid⟩
  else
    .error .malformedControl

/-- Validation adds control-bounds evidence but cannot change the closed ISA
fragment established by the typed program. -/
theorem Checked.inV0 (checked : Checked) : checked.program.InV0 :=
  checked.program.inV0

end Ix.Compiler.X86
