import Ix.Compiler.X86.Basic

/-! Independent decoding of the emitted x86-64 forms. The parser reads actual
opcode, REX, ModRM, SIB, displacement, and immediate fields. It imports neither
the encoder nor the typed evaluator. Unsupported or truncated forms reject.
Typed pseudo-operations decode to their ordinary machine instructions. -/

namespace Ix.Compiler.X86.Decode

inductive Operand where
  | reg (register : GPR)
  | imm (value : Word)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive Operation where
  | mov (width : Width) (destination : GPR) (source : Operand)
  | load (width : Width) (destination : GPR) (source : MemAddr)
  | store (width : Width) (destination : MemAddr) (source : GPR)
  | lea (destination : GPR) (source : MemAddr)
  | alu (operation : AluOp) (width : Width) (destination : GPR) (source : Operand)
  | imul (width : MulWidth) (destination source : GPR)
  | compare (width : Width) (left : GPR) (right : Operand)
  | push (source : GPR)
  | pop (destination : GPR)
  | call (displacement : Imm32)
  | jump (displacement : Imm32)
  | branch (condition : Condition) (displacement : Imm32)
  | ret
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

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

def readLE : Nat → List UInt8 → Option (Word × List UInt8)
  | 0, input => some (0, input)
  | _ + 1, [] => none
  | count + 1, head :: tail => do
      let (value, rest) ← readLE count tail
      return (head.toUInt64 ||| (value <<< 8), rest)

structure Prefix where
  operand16 : Bool
  w : Bool
  r : Bool
  x : Bool
  b : Bool
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def rex (operand16 : Bool) (byte : UInt8) : Option Prefix :=
  if 0x40 ≤ byte.toNat && byte.toNat < 0x50 then
    some {
      operand16, w := byte.toNat / 8 % 2 == 1
      r := byte.toNat / 4 % 2 == 1, x := byte.toNat / 2 % 2 == 1, b := byte.toNat % 2 == 1 }
  else none

def Prefix.wide (pref : Prefix) : Option Width :=
  if pref.w then if pref.operand16 then none else some .w64
  else some (if pref.operand16 then .w16 else .w32)

def Prefix.width (pref : Prefix) (byte : Bool) : Option Width :=
  if byte then if pref.operand16 || pref.w then none else some .w8
  else pref.wide

def Prefix.mulWidth (pref : Prefix) : Option MulWidth := do
  match ← pref.wide with
  | .w16 => some .w16 | .w32 => some .w32 | .w64 => some .w64 | .w8 => none

def modMode (byte : UInt8) : Nat := byte.toNat / 64
def modReg (byte : UInt8) : Nat := byte.toNat / 8 % 8
def modRM (byte : UInt8) : Nat := byte.toNat % 8

def memory (pref : Prefix) (modrm : UInt8) (input : List UInt8) :
    Option (MemAddr × List UInt8) := do
  let mode := modMode modrm
  let rm := modRM modrm
  if rm == 4 then
    let sib :: tail := input | none
    let index ← index pref.x (modReg sib)
    let scale ← scale (modMode sib)
    let base ← if mode == 0 && modRM sib == 5 && !pref.b then some none
      else if mode == 2 then (register pref.b (modRM sib)).map some
      else none
    let (displacement, rest) ← readLE 4 tail
    return ({
      base, index, scale := if index.isSome then scale else .one
      displacement := displacement.toUInt32 }, rest)
  else
    if mode != 2 || pref.x then none else do
      let base ← register pref.b rm
      let (displacement, rest) ← readLE 4 input
      return ({ base := some base, displacement := displacement.toUInt32 }, rest)

def registers (pref : Prefix) (modrm : UInt8) : Option (GPR × GPR) := do
  if modMode modrm != 3 || pref.x then none else do
    let reg ← register pref.r (modReg modrm)
    let rm ← register pref.b (modRM modrm)
    return (reg, rm)

def memoryOperation (pref : Prefix) (make : GPR → MemAddr → Operation)
    (input : List UInt8) : Option (Operation × List UInt8) := do
  let modrm :: input := input | none
  let register ← register pref.r (modReg modrm)
  let (address, rest) ← memory pref modrm input
  return (make register address, rest)

def immediateBytes : Width → Nat
  | .w8 => 1 | .w16 => 2 | .w32 => 4 | .w64 => 8

def sign32 (value : Word) : Word :=
  if value < 0x80000000 then value else value ||| 0xffffffff00000000

def groupImmediate (width : Width) (input : List UInt8) : Option (Word × List UInt8) := do
  let (value, rest) ← readLE (if width == .w64 then 4 else immediateBytes width) input
  return (if width == .w64 then sign32 value else value, rest)

def aluRegisterOpcode : UInt8 → Option (AluOp × Bool)
  | 0x00 => some (.add, true) | 0x01 => some (.add, false)
  | 0x08 => some (.or, true) | 0x09 => some (.or, false)
  | 0x20 => some (.and, true) | 0x21 => some (.and, false)
  | 0x28 => some (.sub, true) | 0x29 => some (.sub, false)
  | 0x30 => some (.xor, true) | 0x31 => some (.xor, false)
  | _ => none

def aluGroup : Nat → Option AluOp
  | 0 => some .add | 1 => some .or | 4 => some .and | 5 => some .sub | 6 => some .xor
  | _ => none

def nearCondition : UInt8 → Option Condition
  | 0x84 => some .eq | 0x85 => some .ne
  | 0x82 => some .unsignedLt | 0x86 => some .unsignedLe
  | 0x87 => some .unsignedGt | 0x83 => some .unsignedGe
  | 0x8c => some .signedLt | 0x8e => some .signedLe
  | 0x8f => some .signedGt | 0x8d => some .signedGe
  | _ => none

def prefixed (pref : Prefix) (input : List UInt8) : Option (Operation × List UInt8) := do
  let opcode :: input := input | none
  if 0xb0 ≤ opcode.toNat && opcode.toNat < 0xc0 then
    if pref.r || pref.x then none else do
      let narrow := opcode.toNat < 0xb8
      let width ← pref.width narrow
      let destination ← register pref.b (opcode.toNat % 8)
      let (value, rest) ← readLE (immediateBytes width) input
      return (.mov width destination (.imm value), rest)
  else do
    let opcode2 :: input := input | none
    if opcode == 0x0f then
      let modrm :: input := input | none
      if opcode2 == 0xaf then
        let width ← pref.mulWidth
        let (destination, source) ← registers pref modrm
        return (.imul width destination source, input)
      else if (opcode2 == 0xb6 || opcode2 == 0xb7) && pref.w && !pref.operand16 then
        memoryOperation pref (.load (if opcode2 == 0xb6 then .w8 else .w16)) (modrm :: input)
      else none
    else
      let modrm := opcode2
      if opcode == 0x88 || opcode == 0x89 then
        let width ← pref.width (opcode == 0x88)
        if modMode modrm == 3 then
          let (source, destination) ← registers pref modrm
          return (.mov width destination (.reg source), input)
        else
          memoryOperation pref (fun source address => .store width address source) (modrm :: input)
      else if opcode == 0x8b || opcode == 0x8d then
        if pref.operand16 then none else do
          if opcode == 0x8d then
            if pref.w then memoryOperation pref .lea (modrm :: input) else none
          else memoryOperation pref (.load (if pref.w then .w64 else .w32)) (modrm :: input)
      else if opcode == 0x80 || opcode == 0x81 then
        if pref.r then none else do
          let width ← pref.width (opcode == 0x80)
          let (_, destination) ← registers pref modrm
          let (value, rest) ← groupImmediate width input
          if modReg modrm == 7 then some (.compare width destination (.imm value), rest)
          else do
            let operation ← aluGroup (modReg modrm)
            return (.alu operation width destination (.imm value), rest)
      else if opcode == 0x38 || opcode == 0x39 then
        let width ← pref.width (opcode == 0x38)
        let (right, left) ← registers pref modrm
        return (.compare width left (.reg right), input)
      else
        let (operation, narrow) ← aluRegisterOpcode opcode
        let width ← pref.width narrow
        let (source, destination) ← registers pref modrm
        return (.alu operation width destination (.reg source), input)

def stack (extended : Bool) (opcode : UInt8) (rest : List UInt8) : Option (Operation × List UInt8) := do
  let register ← register extended (opcode.toNat % 8)
  if 0x50 ≤ opcode.toNat && opcode.toNat < 0x58 then some (.push register, rest)
  else if 0x58 ≤ opcode.toNat && opcode.toNat < 0x60 then some (.pop register, rest)
  else none

def one : List UInt8 → Option (Operation × List UInt8)
  | [] => none
  | 0xc3 :: rest => some (.ret, rest)
  | 0xe8 :: rest => do
      let (displacement, rest) ← readLE 4 rest
      return (.call displacement.toUInt32, rest)
  | 0xe9 :: rest => do
      let (displacement, rest) ← readLE 4 rest
      return (.jump displacement.toUInt32, rest)
  | 0x0f :: opcode :: rest => do
      let condition ← nearCondition opcode
      let (displacement, rest) ← readLE 4 rest
      return (.branch condition displacement.toUInt32, rest)
  | 0x66 :: pref :: rest => do
      let pref ← rex true pref
      prefixed pref rest
  | head :: tail =>
      if head == 0x41 then
        match tail with
        | opcode :: rest =>
            if 0x50 ≤ opcode.toNat && opcode.toNat < 0x60 then stack true opcode rest
            else do let pref ← rex false head; prefixed pref tail
        | [] => none
      else if 0x50 ≤ head.toNat && head.toNat < 0x60 then stack false head tail
      else do let pref ← rex false head; prefixed pref tail

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

end Ix.Compiler.X86.Decode
