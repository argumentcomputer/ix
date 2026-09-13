module
public import Ix.Ixby.Codec.Encode

/-! Strict decoding for the experimental crypto codec: no trailing bytes,
unknown tags, Boolean truthiness, field reduction, or resettable value budgets.
Successful results carry exact re-encoding equations and pass encoder admission. -/

public section
@[expose] section

namespace Ix.Ixby.Codec
namespace Internal

def readField : Decoder Goldilocks := do
  let n ← readNat 8
  if h : n < goldilocksModulus then return ⟨n, h⟩
  else throw .nonCanonical

def readScalar (profile : Profile) : Decoder Scalar := do
  match (← readByte).toNat with
  | 0 =>
    match (← readByte).toNat with
    | 0 => return .bool false
    | 1 => return .bool true
    | _ => throw .nonCanonical
  | 1 => return .word32 (← readU32).toUInt32
  | 2 => return .field (← readField)
  | 3 =>
    let c0 ← readField
    let c1 ← readField
    return .extField ⟨c0, c1⟩
  | 4 => return .bytes (← readBytes (← readCount profile.limits.byteArrayBytes))
  | tag => throw (.tag tag)

def readCtorId : Decoder CtorId := do
  let block ← readNat 32
  let member ← readU32
  let tag ← readU32
  if h : block < 2 ^ 256 then return { block := ⟨block, h⟩, member, tag }
  else throw .integerRange

def readValue (profile : Profile) : Nat → Decoder Value
  | 0 => throw .depthLimit
  | depth + 1 => do
    readNode
    match (← readByte).toNat with
    | 0 => return .scalar (← readScalar profile)
    | 1 =>
      let id ← readCtorId
      let fields ← readVector profile.limits.operands (readValue profile depth)
      return .ctor id fields
    | 2 =>
      let function ← readU32
      let captured ← readVector profile.limits.operands (readValue profile depth)
      return .pap function captured
    | 3 => return .erased
    | tag => throw (.tag tag)

def readOperand (profile : Profile) : Decoder Operand := do
  match (← readByte).toNat with
  | 0 => return .local (← readU32)
  | 1 => return .literal (← readScalar profile)
  | 2 => return .erased
  | tag => throw (.tag tag)

def readOperands (profile : Profile) : Decoder (List Operand) := do
  return (← readVector profile.limits.operands (readOperand profile)).toList

def readOp (profile : Profile) : Decoder Op := do
  match (← readByte).toNat with
  | 0 => return .copy (← readOperand profile)
  | 1 =>
    let opcode := (← readByte).toNat
    let some primitive := cryptoPrimitives[opcode]? | throw (.tag opcode)
    return .primitive primitive (← readOperands profile)
  | 2 =>
    let ctor ← readU32
    return .construct ctor (← readOperands profile)
  | 3 =>
    let value ← readOperand profile
    return .project value (← readU32)
  | 4 =>
    let function ← readU32
    return .closure function (← readOperands profile)
  | 5 =>
    let function ← readU32
    return .call function (← readOperands profile)
  | 6 => return .callSelf (← readOperands profile)
  | 7 =>
    let function ← readOperand profile
    return .apply function (← readOperands profile)
  | tag => throw (.tag tag)

def readAlternative : Decoder Alternative := do
  let ctor ← readU32
  let target ← readU32
  return ⟨ctor, target⟩

def readInstr (profile : Profile) : Decoder Instr := do
  match (← readByte).toNat with
  | 0 =>
    let op ← readOp profile
    return .letOp op (← readU32)
  | 1 => return .ret (← readOperand profile)
  | 2 =>
    let function ← readU32
    return .tailCall function (← readOperands profile)
  | 3 => return .tailCallSelf (← readOperands profile)
  | 4 =>
    let function ← readOperand profile
    return .tailApply function (← readOperands profile)
  | 5 =>
    let value ← readOperand profile
    return .caseCtor value (← readVector profile.limits.constructors readAlternative).toList
  | 6 =>
    let condition ← readOperand profile
    let ifTrue ← readU32
    let ifFalse ← readU32
    return .branch condition ifTrue ifFalse
  | tag => throw (.tag tag)

def readFunction (profile : Profile) : Decoder Function := do
  let arity ← readCount profile.limits.operands
  let entry ← readU32
  let blocks ← readVector profile.limits.blocks do
    let locals ← readCount profile.limits.locals
    let instruction ← readInstr profile
    return ⟨locals, instruction⟩
  return { arity, entry, blocks }

def readProgram (profile : Profile) : Decoder Program := do
  readHeader "IXBY"
  let entry ← readU32
  let constructors ← readVector profile.limits.constructors do
    let id ← readCtorId
    let fields ← readCount profile.limits.operands
    return ⟨id, fields⟩
  let functions ← readVector profile.limits.functions (readFunction profile)
  return { entry, constructors, functions }

def readProfile : Decoder Profile := do
  readHeader "IXBP"
  unless (← readU32) == semanticVersion do throw .version
  let functions ← readU32
  let constructors ← readU32
  let blocks ← readU32
  let locals ← readU32
  let operands ← readU32
  let continuations ← readU32
  let inputNodes ← readU32
  let natBits ← readU32
  let stringBytes ← readU32
  let byteArrayBytes ← readU32
  let programBytes ← readU32
  let valueBytes ← readU32
  let valueDepth ← readU32
  let maxSteps ← readU32
  return {
    limits := {
      functions := functions, constructors := constructors, blocks := blocks,
      locals := locals, operands := operands, continuations := continuations,
      inputNodes := inputNodes, natBits := natBits, stringBytes := stringBytes,
      byteArrayBytes := byteArrayBytes },
    programBytes, valueBytes, valueDepth, maxSteps }

end Internal

open Internal

/-- Decoding a profile does not authorize its resource/security policy. Callers
must select an allowed profile before decoding/executing a large artifact. -/
def decodeProfile (bytes : Bytes) : Except Error (Decoded encodeProfile bytes) := do
  let profile ← decode 68 0 bytes readProfile
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
    readHeader "IXBI"
    readVector profile.limits.operands (readValue profile profile.valueDepth)
  canonicalize (encodeInput profile program) bytes input

def decodeOutput (profile : Profile) (program : Program) (bytes : Bytes) :
    Except Error (Decoded (encodeOutput profile program) bytes) := do
  profile.validate |>.mapError .profile
  let output ← decode profile.valueBytes profile.limits.inputNodes bytes do
    readHeader "IXBO"
    readValue profile profile.valueDepth
  canonicalize (encodeOutput profile program) bytes output

end Ix.Ixby.Codec
