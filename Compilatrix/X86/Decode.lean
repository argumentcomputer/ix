import Compilatrix.X86.Table.Index

/-! Independent decoding of emitted x86-64 instructions. The parser reads
the actual legacy prefix, REX, opcode map, opcode, ModRM, SIB, displacement
and immediate fields, finds the row in the table's decoder index, and checks
the operands against the row's slot kinds. It imports neither the encoder
nor the typed evaluator. Unsupported, non-canonical-prefix or truncated
forms reject. -/

namespace Compilatrix.X86.Decode

/-- A decoded instruction: one table row and its operands. -/
inductive Operation where
  | op (o : Op) (args : List Arg)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- A byte parser. Every choice it makes depends only on bytes it has
already consumed, so a decoded prefix is independent of what follows. -/
abbrev Parser := StateT (List UInt8) Option

def byte : Parser UInt8 := fun
  | head :: tail => some (head, tail)
  | [] => none

def fail : Parser α := fun _ => none

/-- A little-endian unsigned field of `count` bytes. -/
def readLE : Nat → Parser Nat
  | 0 => pure 0
  | count + 1 => do
      let head ← byte
      let value ← readLE count
      pure (head.toNat + 256 * value)

def register (extended : Bool) : Nat → Option GPR
  | 0 => some (if extended then .r8 else .rax)
  | 1 => some (if extended then .r9 else .rcx)
  | 2 => some (if extended then .r10 else .rdx)
  | 3 => some (if extended then .r11 else .rbx)
  | 4 => some (if extended then .r12 else .rsp)
  | 5 => some (if extended then .r13 else .rbp)
  | 6 => some (if extended then .r14 else .rsi)
  | 7 => some (if extended then .r15 else .rdi)
  | _ => none

def asIndex : GPR → Option IndexReg
  | .rax => some .rax | .rcx => some .rcx | .rdx => some .rdx
  | .rbx => some .rbx | .rsp => none | .rbp => some .rbp
  | .rsi => some .rsi | .rdi => some .rdi
  | .r8 => some .r8 | .r9 => some .r9 | .r10 => some .r10 | .r11 => some .r11
  | .r12 => some .r12 | .r13 => some .r13 | .r14 => some .r14 | .r15 => some .r15

def index (extended : Bool) (low : Nat) : Option (Option IndexReg) :=
  if low == 4 && !extended then some none else do
    let register ← register extended low
    let index ← asIndex register
    return some index

def scale : Nat → Option Scale
  | 0 => some .one | 1 => some .two | 2 => some .four | 3 => some .eight
  | _ => none

def lift : Option α → Parser α
  | some value => pure value
  | none => fail

structure Rex where
  w : Bool
  r : Bool
  x : Bool
  b : Bool
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def rex? (byte : UInt8) : Option Rex :=
  if 0x40 ≤ byte.toNat && byte.toNat < 0x50 then
    some ⟨byte.toNat / 8 % 2 == 1, byte.toNat / 4 % 2 == 1, byte.toNat / 2 % 2 == 1,
      byte.toNat % 2 == 1⟩
  else none

/-- REX bits of an optional prefix; absent means all clear. -/
def Rex.bits (rex : Option Rex) : Rex := rex.getD ⟨false, false, false, false⟩

def modMode (byte : UInt8) : Nat := byte.toNat / 64
def modReg (byte : UInt8) : Nat := byte.toNat / 8 % 8
def modRM (byte : UInt8) : Nat := byte.toNat % 8

/-- Displacement of ModRM mode 0 (none), 1 (disp8) or 2 (disp32), as the
32-bit two's-complement pattern of `MemAddr`. -/
def displacement (mode : Nat) : Parser Imm32 :=
  if mode == 0 then pure 0
  else if mode == 1 then do
    let value ← readLE 1
    pure (signExtend8 (UInt8.ofNat value)).toUInt32
  else if mode == 2 then do
    let value ← readLE 4
    pure (UInt32.ofNat value)
  else fail

/-- A memory operand after its ModRM byte. RIP-relative addressing (mode 0,
rm 5 without SIB) and the mode-0 R13 base hole are rejected. -/
def memory (rex : Rex) (modrm : UInt8) : Parser MemAddr := do
  let mode := modMode modrm
  if mode == 3 then fail
  else if modRM modrm == 4 then
    let sib ← byte
    let index ← lift (index rex.x (modReg sib))
    let scale ← lift (scale (modMode sib))
    let scale := if index.isSome then scale else .one
    if mode == 0 && modRM sib == 5 then
      if rex.b then fail
      else do
        let value ← readLE 4
        pure { base := none, index, scale, displacement := UInt32.ofNat value }
    else do
      let base ← lift (register rex.b (modRM sib))
      let displacement ← displacement mode
      pure { base := some base, index, scale, displacement }
  else if rex.x then fail
  else if mode == 0 && modRM modrm == 5 then fail
  else do
    let base ← lift (register rex.b (modRM modrm))
    let displacement ← displacement mode
    pure { base := some base, displacement }

/-- An immediate field, sign-extended to its canonical 64-bit value. -/
def immediate : ImmKind → Parser (Option Word)
  | .none => pure none
  | kind => do
      let value ← readLE kind.bytes
      pure (some (kind.norm (UInt64.ofNat value)))

/-- Operands in slot order from the fields the class places them in. -/
def assemble (form : OpEn) (reg : Option GPR) (rm : Option Arg) (imm : Option Word) : Option (List Arg) :=
  match form, reg, rm, imm with
  | .MR, some reg, some rm, none => some [rm, .reg reg]
  | .RM, some reg, some rm, none => some [.reg reg, rm]
  | .MI, none, some rm, some imm | .MI8, none, some rm, some imm => some [rm, .imm imm]
  | .OI, some reg, none, some imm => some [.reg reg, .imm imm]
  | .O, some reg, none, none => some [.reg reg]
  | .RMI, some reg, some rm, some imm | .RMI8, some reg, some rm, some imm =>
      some [.reg reg, rm, .imm imm]
  | .D32, none, none, some imm => some [.imm imm]
  | .ZO, none, none, none => some []
  | _, _, _, _ => none

def byteRegistersOk (enc : EncDesc) (rexPresent : Bool) (reg : Option GPR) (rm : Option Arg) : Bool :=
  rexPresent ||
    (!(enc.byteReg && reg.any GPR.highByteCode) &&
      !(enc.byteRM && match rm with | some (.reg register) => register.highByteCode | _ => false))

/-- The ModRM.rm operand: a register (mode 3) or a memory address. -/
def rmOperand (rex : Rex) (modrm : UInt8) : Parser Arg :=
  if modMode modrm == 3 then
    if rex.x then fail
    else do
      let register ← lift (register rex.b (modRM modrm))
      pure (.reg register)
  else do
    let address ← memory rex modrm
    pure (.mem address)

/-- Register and r/m fields of a row with a ModRM byte. The REX.R bit must
be clear when ModRM.reg is an opcode extension. -/
def modrmFields (use : ModRMUse) (rex : Rex) (modrm : UInt8) : Parser (Option GPR × Option Arg) := do
  let reg ← match use with
    | .reg => do
        let register ← lift (register rex.r (modReg modrm))
        pure (some register)
    | .none | .digit _ => if rex.r then fail else pure none
  let rm ← rmOperand rex modrm
  pure (reg, some rm)

/-- Register field of a row without ModRM: the opcode's low bits when the
row embeds a register. Unused REX bits reject. -/
def opcodeFields (emb : Emb) (rex : Rex) (opcode : UInt8) : Parser (Option GPR × Option Arg) :=
  if rex.r || rex.x then fail
  else match emb with
    | .regLow3 => do
        let register ← lift (register rex.b (opcode.toNat % 8))
        pure (some register, none)
    | .none => if rex.b then fail else pure (none, none)

/-- Parse a row's operands. `preread` is the ModRM byte when the digit
lookup already consumed it. -/
def operands (o : Op) (rexByte : Option Rex) (opcode : UInt8) (preread : Option UInt8) : Parser Operation := do
  let enc := (desc o).enc
  let rex := Rex.bits rexByte
  let fields ← match enc.modrm with
    | .none => opcodeFields enc.emb rex opcode
    | .reg | .digit _ => do
        let modrm ← match preread with
          | some modrm => pure modrm
          | none => byte
        modrmFields enc.modrm rex modrm
  let imm ← immediate enc.imm
  let args ← lift (assemble o.form fields.1 fields.2 imm)
  if o.argsOk args && byteRegistersOk enc rexByte.isSome fields.1 fields.2 then pure (.op o args) else fail

/-- Find the row from the parsed prefix, map and opcode (and, for group
opcodes, the ModRM digit), then parse its operands. -/
def body (p66 : Bool) (rexByte : Option Rex) (map : OpMap) (opcode : UInt8) : Parser Operation :=
  match Table.lookup (Table.key p66 (Rex.bits rexByte).w map opcode 8) with
  | some o => operands o rexByte opcode none
  | none => do
      let modrm ← byte
      let o ← lift (Table.lookup (Table.key p66 (Rex.bits rexByte).w map opcode (modReg modrm)))
      operands o rexByte opcode (some modrm)

/-- The opcode map escape, given the first byte after the prefixes. -/
def opcodeStage (p66 : Bool) (rexByte : Option Rex) (first : UInt8) : Parser Operation :=
  if first == 0x0f then do
    let opcode ← byte
    body p66 rexByte .x0F opcode
  else body p66 rexByte .legacy first

/-- An optional REX prefix, given the first byte after `66`. -/
def rexStage (p66 : Bool) (first : UInt8) : Parser Operation :=
  match rex? first with
  | some rex => do
      let next ← byte
      opcodeStage p66 (some rex) next
  | none => opcodeStage p66 none first

/-- Decode one instruction: `[66] [REX] [0F] opcode ...`. -/
def one : Parser Operation := do
  let first ← byte
  if first == 0x66 then do
    let next ← byte
    rexStage true next
  else rexStage false first

/-- Decode an explicitly bounded instruction recipe, preserving its suffix. -/
def sequence : Nat → List UInt8 → Option (List Operation × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (operation, rest) ← one input
      let (operations, rest) ← sequence count rest
      return (operation :: operations, rest)

structure Decoded where
  operation : Operation
  length : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def decodeAt (text : ByteArray) (offset : Nat) : Option Decoded := do
  if offset ≥ text.size then none else do
    let input := text.data.toList.drop offset
    let (operation, rest) ← one input
    let length := input.length - rest.length
    if 0 < length && length ≤ 15 then some ⟨operation, length⟩ else none

end Compilatrix.X86.Decode
