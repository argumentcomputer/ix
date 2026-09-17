module
public import Ix.Ixby.Codec.Encode

/-! Strict current functional codec. Old magic/revision combinations, malformed
LEB128, noncanonical field/UTF-8 payloads, and trailing bytes are rejected. -/

public section
@[expose] section
namespace Ix.Ixby.Codec

namespace Internal

def readField : Decoder Goldilocks := do
  let n := natOfBytesLE (← readBytes 8)
  if h : n < goldilocksModulus then return ⟨n, h⟩
  else throw .nonCanonical

def readScalar (limits : Limits) : Decoder Scalar := do
  match (← readByte).toNat with
  | 0 => return .nat (← readNatural)
  | 1 =>
    let bytes ← readBytes (← readCount limits.stringBytes)
    let some string := String.fromUTF8? ⟨bytes⟩ | throw .nonCanonical
    return .str string
  | 2 =>
    match (← readByte).toNat with
    | 0 => return .bool false
    | 1 => return .bool true
    | _ => throw .nonCanonical
  | 3 => return .word32 (natOfBytesLE (← readBytes 4)).toUInt32
  | 4 => return .field (← readField)
  | 5 =>
    let c0 ← readField
    let c1 ← readField
    return .extField ⟨c0, c1⟩
  | 6 => return .bytes (← readBytes (← readCount limits.byteArrayBytes))
  | tag => throw (.tag tag)

def readCtorId : Decoder CtorId := do
  let block := natOfBytesLE (← readBytes 32)
  let member ← readNatural
  let tag ← readNatural
  if h : block < 2 ^ 256 then return { block := ⟨block, h⟩, member, tag }
  else throw .nonCanonical

def readValue (limits : Limits) : Nat → Decoder Value
  | 0 => throw .depthLimit
  | depth + 1 => do
    readNode
    match (← readByte).toNat with
    | 0 => return .scalar (← readScalar limits)
    | 1 =>
      let id ← readCtorId
      return .ctor id (← readVector limits.operands (readValue limits depth))
    | 2 =>
      let fn ← readNatural
      return .pap fn (← readVector limits.operands (readValue limits depth))
    | 3 => return .erased
    | 4 => return .array (← readVector (min limits.inputNodes (2 ^ 32 - 1))
        (readValue limits depth))
    | tag => throw (.tag tag)

def readOperand (limits : Limits) : Decoder Operand := do
  match (← readByte).toNat with
  | 0 => return .local (← readNatural)
  | 1 => return .literal (← readScalar limits)
  | 2 => return .erased
  | tag => throw (.tag tag)

def readOperands (limits : Limits) : Decoder (List Operand) := do
  return (← readVector limits.operands (readOperand limits)).toList

def readOp (limits : Limits) : Decoder Op := do
  match (← readByte).toNat with
  | 0 => return .copy (← readOperand limits)
  | 1 =>
    let opcode := (← readByte).toNat
    let some primitive := primitives[opcode]? | throw (.tag opcode)
    return .primitive primitive (← readOperands limits)
  | 2 =>
    let ctor ← readNatural
    return .construct ctor (← readOperands limits)
  | 3 =>
    let value ← readOperand limits
    return .project value (← readNatural)
  | 4 =>
    let fn ← readNatural
    return .closure fn (← readOperands limits)
  | 5 =>
    let fn ← readNatural
    return .call fn (← readOperands limits)
  | 6 => return .callSelf (← readOperands limits)
  | 7 =>
    let fn ← readOperand limits
    return .apply fn (← readOperands limits)
  | tag => throw (.tag tag)

def readAlternative : Decoder Alternative := do
  let ctor ← readNatural
  return ⟨ctor, ← readNatural⟩

def readInstr (limits : Limits) : Decoder Instr := do
  match (← readByte).toNat with
  | 0 =>
    let op ← readOp limits
    return .letOp op (← readNatural)
  | 1 => return .ret (← readOperand limits)
  | 2 =>
    let fn ← readNatural
    return .tailCall fn (← readOperands limits)
  | 3 => return .tailCallSelf (← readOperands limits)
  | 4 =>
    let fn ← readOperand limits
    return .tailApply fn (← readOperands limits)
  | 5 =>
    let value ← readOperand limits
    return .caseCtor value (← readVector limits.constructors readAlternative).toList
  | 6 =>
    let value ← readOperand limits
    let ifZero ← readNatural
    return .caseNat value ifZero (← readNatural)
  | 7 =>
    let condition ← readOperand limits
    let yes ← readNatural
    return .branch condition yes (← readNatural)
  | tag => throw (.tag tag)

def readFunction (limits : Limits) : Decoder Function := do
  let arity ← readCount limits.operands
  let entry ← readNatural
  let blocks ← readVector limits.blocks do
    let locals ← readCount limits.locals
    let instruction ← readInstr limits
    return { locals, instruction : Block }
  return { arity, entry, blocks }

def readLimits (read : Decoder Nat) : Decoder Limits := do
  let functions ← read
  let constructors ← read
  let blocks ← read
  let locals ← read
  let operands ← read
  let continuations ← read
  let inputNodes ← read
  let natBits ← read
  let stringBytes ← read
  let byteArrayBytes ← read
  return {
    functions := functions, constructors := constructors, blocks := blocks,
    locals := locals, operands := operands, continuations := continuations,
    inputNodes := inputNodes, natBits := natBits, stringBytes := stringBytes,
    byteArrayBytes := byteArrayBytes }

def readProgram (profile : Profile) : Decoder Program := do
  readHeader "IXBF"
  let limits ← readLimits readNatural
  let maxSteps ← readNatural
  unless limits == profile.limits && maxSteps == profile.maxSteps do throw .nonCanonical
  let entry ← readNatural
  let constructors ← readVector limits.constructors do
    let id ← readCtorId
    let fields ← readCount limits.operands
    return { id, fields : CtorDecl }
  let functions ← readVector limits.functions (readFunction limits)
  return { entry := entry, constructors, functions }

def readProfile : Decoder Profile := do
  unless (← readBytes 4) == "IXFP".toUTF8.data do throw .header
  unless (← readU32) == 0 do throw .version
  unless (← readU32) == wireVersion do throw .version
  unless (← readU32) == semanticVersion do throw .version
  let limits ← readLimits (readNat 16)
  let maxSteps ← readNat 8
  return { limits := limits, maxSteps }

end Internal
open Internal

def decodeProfile (bytes : Bytes) : Except Error (Decoded encodeProfile bytes) := do
  let profile ← decode 184 0 bytes readProfile
  canonicalize encodeProfile bytes profile

def decodeProgram (profile : Profile) (bytes : Bytes) :
    Except Error (Decoded (encodeProgram profile) bytes) := do
  profile.validate |>.mapError .profile
  let program ← decode profile.programBytes 0 bytes (readProgram profile)
  canonicalize (encodeProgram profile) bytes program

def decodeInput (profile : Profile) (program : Program) (bytes : Bytes) :
    Except Error (Decoded (encodeInput profile program) bytes) := do
  profile.validate |>.mapError .profile
  let input ← decode profile.valueBytes profile.limits.inputNodes bytes do
    readHeader "IXFI"
    readVector profile.limits.operands (readValue profile.limits profile.valueDepth)
  canonicalize (encodeInput profile program) bytes input

def decodeOutput (profile : Profile) (program : Program) (bytes : Bytes) :
    Except Error (Decoded (encodeOutput profile program) bytes) := do
  profile.validate |>.mapError .profile
  let output ← decode profile.valueBytes profile.limits.inputNodes bytes do
    readHeader "IXFO"
    readValue profile.limits profile.valueDepth
  canonicalize (encodeOutput profile program) bytes output

end Ix.Ixby.Codec
