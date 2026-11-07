import IxCC.X86.State

/-!
# Instruction-table vocabulary

One row of the x86 table is an `Op`: a mnemonic, an operand width, an SDM
encoding class ("Op/En") and, for zero-extending moves, a source width.
`desc : Op → OpDesc` (in `Table.Rows`) gives each row its operand slots, its
single semantic function, its flag effects and its encoding descriptor. The
typed machine, the byte machine, the encoder and the decoder all read these
rows; none of them enumerates instruction forms.

Flags are the four the model reads (CF, ZF, SF, OF). Each row declares, per
flag, whether it sets it, leaves it undefined or leaves it unchanged, and
which flags its semantics may read (`flagsIn`). PF and AF are unmodelled and
never read. A `set` flag whose value the semantics leaves `none` is
undefined after that execution (a shift's OF for counts other than one).

Besides its slots, a row may name implicit register operands (`div`'s
`rax`/`rdx`, a shift's `cl`) and implicit stack traffic through `rsp`
(`push`, `pop`, `call`, `ret`).
-/

namespace IxCC.X86

/-! ## Rows -/

inductive Mnemonic where
  | add | or | and | sub | xor | cmp | test
  | shl | shr | sar
  | mov | movzx | lea | imul | div
  | setcc (condition : Condition) | cmovcc (condition : Condition)
  | push | pop
  | call | jmp | jcc (condition : Condition) | ret
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- SDM "Op/En" encoding classes: which operand lives in ModRM.rm, ModRM.reg,
the opcode's low three bits, or the immediate. -/
inductive OpEn where
  /-- `op r/m, r` -/
  | MR
  /-- `op r, r/m` -/
  | RM
  /-- `op r/m, imm` with ModRM.reg an opcode extension -/
  | MI
  /-- `op r/m, imm8` (sign-extended) with ModRM.reg an opcode extension -/
  | MI8
  /-- `op r/m` with ModRM.reg an opcode extension -/
  | M
  /-- `op r/m, cl` with ModRM.reg an opcode extension; `cl` is implicit -/
  | MC
  /-- `op r, imm` with the register in the opcode -/
  | OI
  /-- `op r` with the register in the opcode -/
  | O
  /-- `op r, r/m, imm` -/
  | RMI
  /-- `op r, r/m, imm8` (sign-extended) -/
  | RMI8
  /-- `op rel32` -/
  | D32
  /-- no operands -/
  | ZO
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- One table row: one opcode at one operand size. -/
structure Op where
  mn : Mnemonic
  w : Width
  form : OpEn
  src : Width := w
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Rows that transfer control have dedicated typed constructors and byte
effects. -/
def Op.control (o : Op) : Bool :=
  match o.mn with
  | .call | .jmp | .jcc _ | .ret => true
  | _ => false

/-- Rows that read flags as data (`setcc`, `cmovcc`). The typed machine has
no flags, so they run only as the consumer of a fused pair. -/
def Op.consumer (o : Op) : Bool :=
  match o.mn with
  | .setcc _ | .cmovcc _ => true
  | _ => false

/-- Rows the typed machine runs alone: neither control nor flag consumers. -/
def Op.linear (o : Op) : Bool :=
  match o.mn with
  | .call | .jmp | .jcc _ | .ret | .setcc _ | .cmovcc _ => false
  | _ => true

/-! ## Operands -/

/-- A machine operand. Immediates are stored in their canonical 64-bit form:
the sign extension of the bits the encoding carries. -/
inductive Arg where
  | reg (register : GPR)
  | mem (address : MemAddr)
  | imm (value : Word)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- As byte registers, codes 4–7 name AH–BH unless a REX prefix is present;
with REX they name SPL, BPL, SIL and DIL. -/
def GPR.highByteCode : GPR → Bool
  | .rsp | .rbp | .rsi | .rdi => true
  | _ => false

inductive ImmKind where
  | none | imm8 | imm16 | imm32 | imm64
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def ImmKind.bytes : ImmKind → Nat
  | .none => 0
  | .imm8 => 1
  | .imm16 => 2
  | .imm32 => 4
  | .imm64 => 8

def signExtend8 (value : UInt8) : Word :=
  let raw := value.toUInt64
  if value < 0x80 then raw else raw ||| 0xffffffffffffff00

def signExtend16 (value : UInt16) : Word :=
  let raw := value.toUInt64
  if value < 0x8000 then raw else raw ||| 0xffffffffffff0000

/-- The 64-bit value an immediate field of this kind denotes. -/
def ImmKind.norm : ImmKind → Word → Word
  | .none, value => value
  | .imm8, value => signExtend8 value.toUInt8
  | .imm16, value => signExtend16 value.toUInt16
  | .imm32, value => signExtend32 value.toUInt32
  | .imm64, value => value

inductive ArgKind where
  | reg | mem | imm8 | imm16 | imm32 | imm64 | rel32
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Scale bits have no effect without an index; the canonical address
records scale one. -/
def MemAddr.canonical (address : MemAddr) : Bool :=
  address.index.isSome || address.scale == .one

def ArgKind.accepts : ArgKind → Arg → Bool
  | .reg, .reg _ => true
  | .mem, .mem address => address.canonical
  | .imm8, .imm value => ImmKind.imm8.norm value == value
  | .imm16, .imm value => ImmKind.imm16.norm value == value
  | .imm32, .imm value | .rel32, .imm value => ImmKind.imm32.norm value == value
  | .imm64, .imm _ => true
  | _, _ => false

inductive Role where
  | read | write | readWrite
  /-- The slot contributes its effective address, not its contents (`lea`). -/
  | address
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Slot where
  kinds : List ArgKind
  width : Width
  role : Role
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Implicit stack traffic through `rsp`. -/
inductive StackEffect where
  | none | push | pop
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- An implicit register operand: `div`'s `rax`/`rdx`, or a shift's `cl`.
Reads see the full register (the semantics truncates); writes follow the
width's partial-register rule, like explicit register slots. -/
structure Implicit where
  reg : GPR
  width : Width
  role : Role
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Role.reads : Role → Bool
  | .read | .readWrite => true
  | .write | .address => false

def Role.writes : Role → Bool
  | .write | .readWrite => true
  | .read | .address => false

/-! ## Flags -/

inductive Flag where
  | cf | zf | sf | of
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive FlagEffect where
  | set | undefined | unchanged
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- The value of one flag after a row with this effect. -/
def FlagEffect.pick : FlagEffect → Option Bool → Option Bool → Option Bool
  | .set, _, computed => computed
  | .unchanged, before, _ => before
  | .undefined, _, _ => none

namespace ByteEval

/-- The four condition flags read by emitted branches. `none` is undefined;
reading an undefined flag is a fault, never a guess. -/
structure Flags where
  carry : Option Bool := none
  zero : Option Bool := none
  sign : Option Bool := none
  overflow : Option Bool := none
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Flags.test (flags : Flags) : Condition → Option Bool
  | .eq => flags.zero
  | .ne => flags.zero.map not
  | .unsignedLt => flags.carry
  | .unsignedLe => do return (← flags.carry) || (← flags.zero)
  | .unsignedGt => do return !((← flags.carry) || (← flags.zero))
  | .unsignedGe => flags.carry.map not
  | .signedLt => do return (← flags.sign) ^^ (← flags.overflow)
  | .signedLe => do return ((← flags.sign) ^^ (← flags.overflow)) || (← flags.zero)
  | .signedGt => do return !(((← flags.sign) ^^ (← flags.overflow)) || (← flags.zero))
  | .signedGe => do return !((← flags.sign) ^^ (← flags.overflow))

def Flags.get (flags : Flags) : Flag → Option Bool
  | .cf => flags.carry
  | .zf => flags.zero
  | .sf => flags.sign
  | .of => flags.overflow

/-- What a row's semantics may observe: only the flags it declares. -/
def Flags.restrict (reads : List Flag) (flags : Flags) : Flags :=
  { carry := if reads.contains .cf then flags.carry else none
    zero := if reads.contains .zf then flags.zero else none
    sign := if reads.contains .sf then flags.sign else none
    overflow := if reads.contains .of then flags.overflow else none }

/-- Flags after a row: `set` flags from the semantics, `unchanged` flags
from before, `undefined` flags unknown. -/
def Flags.merge (effect : Flag → FlagEffect) (before computed : Flags) : Flags :=
  { carry := (effect .cf).pick before.carry computed.carry
    zero := (effect .zf).pick before.zero computed.zero
    sign := (effect .sf).pick before.sign computed.sign
    overflow := (effect .of).pick before.overflow computed.overflow }

def resultFlags (result : BitVec bits) (carry overflow : Bool) : Flags :=
  ⟨some carry, some (result == 0), some result.msb, some overflow⟩

def addFlags (left right : BitVec bits) : Flags :=
  resultFlags (left + right) (BitVec.uaddOverflow left right) (BitVec.saddOverflow left right)

def subFlags (left right : BitVec bits) : Flags :=
  resultFlags (left - right) (BitVec.usubOverflow left right) (BitVec.ssubOverflow left right)

def aluFlags (operation : AluOp) (width : Width) (left right : Word) : Flags :=
  let left := left.toBitVec.setWidth width.bits
  let right := right.toBitVec.setWidth width.bits
  match operation with
  | .add => addFlags left right
  | .sub => subFlags left right
  | .and => resultFlags (left &&& right) false false
  | .or => resultFlags (left ||| right) false false
  | .xor => resultFlags (left ^^^ right) false false

/-- Two- and three-operand IMUL set CF = OF = signed overflow; SF and ZF
are undefined. -/
def mulFlags (width : Width) (left right : Word) : Flags :=
  let overflow := BitVec.smulOverflow
    (left.toBitVec.setWidth width.bits) (right.toBitVec.setWidth width.bits)
  { carry := some overflow, overflow := some overflow }

end ByteEval

inductive ShiftOp where
  | shl | shr | sar
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- The count a shift uses: the low five bits, or six at width 64. -/
def shiftCount (width : Width) (count : Word) : Nat :=
  (count &&& (if width == .w64 then 63 else 31)).toNat

/-- The shifted low `width` bits. A count at or above the width (possible at
widths 8 and 16) shifts every bit out. -/
def ShiftOp.apply (operation : ShiftOp) (width : Width) (value : Word) (count : Nat) : BitVec width.bits :=
  let bits := value.toBitVec.setWidth width.bits
  match operation with
  | .shl => bits <<< count
  | .shr => bits >>> count
  | .sar => bits.sshiftRight count

namespace ByteEval

/-- SHL/SHR/SAR flags (SDM, SAL/SAR/SHL/SHR) for a masked count. For a
nonzero count CF is the last bit shifted out, SF and ZF follow the result,
and OF is defined only for a one-bit shift. CF is left undefined once the
count reaches the width (the SDM leaves it undefined for SHL and SHR; the
model does so for SAR too). A zero count leaves every flag unchanged on
the processor; the model makes them undefined, which removes behaviours
but adds none, since reading an undefined flag faults. -/
def shiftFlags (operation : ShiftOp) (width : Width) (value : Word) (count : Nat) : Flags :=
  if count == 0 then {}
  else
    let bits := value.toBitVec.setWidth width.bits
    let result := operation.apply width value count
    let carry : Option Bool :=
      if count < width.bits then
        some (match operation with
          | .shl => bits.getLsbD (width.bits - count)
          | .shr | .sar => bits.getLsbD (count - 1))
      else none
    let overflow : Option Bool :=
      if count == 1 then
        match operation with
        | .shl => carry.map (result.msb ^^ ·)
        | .shr => some bits.msb
        | .sar => some false
      else none
    { carry, zero := some (result == 0), sign := some result.msb, overflow }

end ByteEval

def Condition.reads : Condition → List Flag
  | .eq | .ne => [.zf]
  | .unsignedLt | .unsignedGe => [.cf]
  | .unsignedLe | .unsignedGt => [.cf, .zf]
  | .signedLt | .signedGe => [.sf, .of]
  | .signedLe | .signedGt => [.sf, .of, .zf]

/-! ## Semantics and encoding descriptors -/

def AluOp.eval (operation : AluOp) (left right : Word) : Word :=
  match operation with
  | .add => left + right
  | .sub => left - right
  | .and => left &&& right
  | .or => left ||| right
  | .xor => left ^^^ right

inductive SemFault where
  | undefinedCondition (condition : Condition)
  /-- `#DE`: a zero divisor or a quotient that does not fit. -/
  | divideError
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure SemIn where
  /-- Values of the read slots in order, then the implicit registers read,
  then an implicit popped word. -/
  args : List Word
  /-- The flags the row declares in `flagsIn`; the rest are undefined. -/
  flags : ByteEval.Flags

structure SemOut where
  /-- Values for the written slots in order (or the pushed word). -/
  results : List Word
  /-- Values for the implicit registers written, in order. -/
  implicit : List Word := []
  /-- Values of the flags the row sets; the rest are ignored. -/
  flags : ByteEval.Flags := {}
  /-- For conditional control rows: whether the branch is taken. -/
  taken : Option Bool := none

inductive OpMap where
  | legacy | x0F
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive ModRMUse where
  | none
  /-- ModRM.reg holds a register operand. -/
  | reg
  /-- ModRM.reg holds an opcode extension `/d`. -/
  | digit (value : Nat)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive Emb where
  | none
  /-- The register operand lives in the opcode's low three bits. -/
  | regLow3
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure EncDesc where
  p66 : Bool := false
  rexW : Bool := false
  map : OpMap := .legacy
  opcode : UInt8
  modrm : ModRMUse := .none
  emb : Emb := .none
  imm : ImmKind := .none
  /-- The ModRM.reg or opcode register is a byte register: without REX,
  codes 4–7 would name AH–BH, so REX is emitted for SPL–DIL. -/
  byteReg : Bool := false
  /-- The ModRM.rm register (when mod = 3) is a byte register. -/
  byteRM : Bool := false
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure OpDesc where
  slots : List Slot
  /-- Implicit register operands, read after the slots and written after
  them. -/
  implicit : List Implicit := []
  stack : StackEffect := .none
  /-- The one semantic function, shared by the typed and byte machines. -/
  sem : SemIn → Except SemFault SemOut
  flagsOut : Flag → FlagEffect := fun _ => .unchanged
  flagsIn : List Flag := []
  /-- A decidable precondition under which `sem` cannot fault. -/
  safe : SemIn → Bool := fun _ => true
  enc : EncDesc
  /-- The Intel-syntax mnemonic LLVM prints for the row. -/
  mnemonic : String

end IxCC.X86
