import Compilatrix.Ixby.Binary.Common

namespace Compilatrix.Ixby.Binary

open Ix.Ixby

/-- Stable explicit opcodes for every primitive of the pinned reference model.
This table is independent of the smaller proving-profile opcode table. -/
def primitives : Array Primitive := #[
  .natAdd, .natSub, .natMul, .natDiv, .natMod, .natEq, .natLt,
  .strAppend, .strLength, .strEq,
  .word32Add, .word32Sub, .word32Mul, .word32And, .word32Or, .word32Xor,
  .word32Shl, .word32Shr, .word32Rotr, .word32Eq, .word32Lt,
  .word32ToBytes, .bytesToWord32, .word32ToField,
  .fieldAdd, .fieldSub, .fieldMul, .fieldInverse, .fieldEq,
  .fieldToBytes, .bytesToField,
  .extAdd, .extSub, .extMul, .extInverse, .extEq, .extPack, .extFst, .extSnd,
  .bytesLength, .bytesGet, .bytesAppend, .bytesSlice, .bytesEq, .blake3]

def primitiveOpcode (primitive : Primitive) : Nat :=
  primitives.toList.idxOf primitive

theorem primitiveOpcode_decodes (primitive : Primitive) :
    primitives[primitiveOpcode primitive]? = some primitive := by
  cases primitive <;> rfl

namespace Internal

def writeScalar : Scalar → Encoder Unit
  | .nat n => do writeByte 0; writeNatural n
  | .str s => do writeByte 1; writeNatural s.utf8ByteSize; writeBytes s.toUTF8.data
  | .bool b => do writeByte 2; writeByte (if b then 1 else 0)
  | .word32 w => do writeByte 3; writeBytes (bytesLE 4 w.toNat)
  | .field f => do writeByte 4; writeBytes (bytesLE 8 f.val)
  | .extField f => do
    writeByte 5; writeBytes (bytesLE 8 f.c0.val); writeBytes (bytesLE 8 f.c1.val)
  | .bytes b => do writeByte 6; writeNatural b.size; writeBytes b

def writeCtorId (id : CtorId) : Encoder Unit := do
  writeBytes (bytesLE 32 id.block.val)
  writeNatural id.member
  writeNatural id.tag

def writeValue : Nat → Value → Encoder Unit
  | 0, _ => throw .depthLimit
  | fuel + 1, value => match value with
    | .scalar scalar => do writeByte 0; writeScalar scalar
    | .ctor id fields => do
      writeByte 1; writeCtorId id; writeVector (writeValue fuel) fields
    | .pap function captured => do
      writeByte 2; writeNatural function; writeVector (writeValue fuel) captured
    | .erased => writeByte 3

def writeOperand : Operand → Encoder Unit
  | .local slot => do writeByte 0; writeNatural slot
  | .literal scalar => do writeByte 1; writeScalar scalar
  | .erased => writeByte 2

def writeOperands (args : List Operand) : Encoder Unit := writeVector writeOperand args.toArray

def writeOp : Op → Encoder Unit
  | .copy value => do writeByte 0; writeOperand value
  | .primitive primitive args => do
    writeByte 1; writeByte (primitiveOpcode primitive).toUInt8; writeOperands args
  | .construct ctor fields => do writeByte 2; writeNatural ctor; writeOperands fields
  | .project value field => do writeByte 3; writeOperand value; writeNatural field
  | .closure function captured => do writeByte 4; writeNatural function; writeOperands captured
  | .call function args => do writeByte 5; writeNatural function; writeOperands args
  | .callSelf args => do writeByte 6; writeOperands args
  | .apply function args => do writeByte 7; writeOperand function; writeOperands args

def writeAlternative (alternative : Alternative) : Encoder Unit := do
  writeNatural alternative.ctor
  writeNatural alternative.target

def writeInstr : Instr → Encoder Unit
  | .letOp op next => do writeByte 0; writeOp op; writeNatural next
  | .ret value => do writeByte 1; writeOperand value
  | .tailCall function args => do writeByte 2; writeNatural function; writeOperands args
  | .tailCallSelf args => do writeByte 3; writeOperands args
  | .tailApply function args => do writeByte 4; writeOperand function; writeOperands args
  | .caseCtor value alternatives => do
    writeByte 5; writeOperand value; writeVector writeAlternative alternatives.toArray
  | .caseNat value ifZero ifSucc => do
    writeByte 6; writeOperand value; writeNatural ifZero; writeNatural ifSucc
  | .branch condition yes no => do
    writeByte 7; writeOperand condition; writeNatural yes; writeNatural no

def writeFunction (function : Function) : Encoder Unit := do
  writeNatural function.arity
  writeNatural function.entry
  writeVector (fun block => do
    writeNatural block.locals
    writeInstr block.instruction) function.blocks

def writeArtifact (artifact : Artifact) : Encoder Unit := do
  writeHeader "IXBF"
  let l := artifact.limits
  for n in #[l.functions, l.constructors, l.blocks, l.locals, l.operands,
      l.continuations, l.inputNodes, l.natBits, l.stringBytes, l.byteArrayBytes,
      artifact.maxSteps] do writeNatural n
  writeNatural artifact.program.entry
  writeVector (fun ctor => do writeCtorId ctor.id; writeNatural ctor.fields)
    artifact.program.constructors
  writeVector writeFunction artifact.program.functions

end Internal

def encode (artifact : Artifact) : Except Error Bytes := do
  validateProgram artifact.limits artifact.program |>.mapError .reference
  Internal.encode (Internal.writeArtifact artifact)

def validateValues (artifact : Artifact) (values : Array Value) : Except Error Unit := do
  validateProgram artifact.limits artifact.program |>.mapError .reference
  validateInputValues artifact.limits artifact.program artifact.limits.inputNodes values.toList
    |>.mapError .reference

def encodeInput (artifact : Artifact) (values : Array Value) : Except Error Bytes := do
  validateValues artifact values
  let fn ← artifact.program.getFunction artifact.program.entry |>.mapError .reference
  unless values.size == fn.arity do throw (.reference (.arityMismatch fn.arity values.size))
  Internal.encode do
    Internal.writeHeader "IXFI"
    Internal.writeVector (Internal.writeValue artifact.limits.inputNodes) values

def encodeOutput (artifact : Artifact) (value : Value) : Except Error Bytes := do
  validateValues artifact #[value]
  Internal.encode do
    Internal.writeHeader "IXFO"
    Internal.writeValue artifact.limits.inputNodes value

end Compilatrix.Ixby.Binary
