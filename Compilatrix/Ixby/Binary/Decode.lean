import Compilatrix.Ixby.Binary.Encode

namespace Compilatrix.Ixby.Binary

open Ix.Ixby

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

def readArtifact : Decoder Artifact := do
  readHeader "IXBF"
  let functions ← readNatural
  let constructors ← readNatural
  let blocks ← readNatural
  let locals ← readNatural
  let operands ← readNatural
  let continuations ← readNatural
  let inputNodes ← readNatural
  let natBits ← readNatural
  let stringBytes ← readNatural
  let byteArrayBytes ← readNatural
  let limits : Limits := {
    functions := functions, constructors := constructors, blocks := blocks,
    locals := locals, operands := operands, continuations := continuations,
    inputNodes := inputNodes, natBits := natBits, stringBytes := stringBytes,
    byteArrayBytes := byteArrayBytes }
  let maxSteps ← readNatural
  let entry ← readNatural
  let constructors ← readVector limits.constructors do
    let id ← readCtorId
    let fields ← readCount limits.operands
    return { id, fields : CtorDecl }
  let functions ← readVector limits.functions (readFunction limits)
  return { limits, maxSteps, program := { entry, constructors, functions } }

end Internal

def decode (bytes : Bytes) (limits : DecodeLimits := {}) :
    Except Error (Decoded encode bytes) := do
  let artifact ← Internal.decode limits bytes Internal.readArtifact
  Internal.canonicalize encode bytes artifact

def decodeInput (artifact : Artifact) (bytes : Bytes) (limits : DecodeLimits := {}) :
    Except Error (Decoded (encodeInput artifact) bytes) := do
  let values ← Internal.decode limits bytes do
    Internal.readHeader "IXFI"
    Internal.readVector artifact.limits.operands
      (Internal.readValue artifact.limits limits.valueDepth)
  Internal.canonicalize (encodeInput artifact) bytes values

def decodeOutput (artifact : Artifact) (bytes : Bytes) (limits : DecodeLimits := {}) :
    Except Error (Decoded (encodeOutput artifact) bytes) := do
  let value ← Internal.decode limits bytes do
    Internal.readHeader "IXFO"
    Internal.readValue artifact.limits limits.valueDepth
  Internal.canonicalize (encodeOutput artifact) bytes value

end Compilatrix.Ixby.Binary
