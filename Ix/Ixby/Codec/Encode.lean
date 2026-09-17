module
public import Ix.Ixby.Codec.Common

/-! Canonical current IXBF/IXFI/IXFO encoding. The functional layout follows
Compilatrix's complete codec (18da375), with the revision-two operations and
array value tag. Loader limits remain checked at this public boundary. -/

public section
@[expose] section
namespace Ix.Ixby.Codec

/-- Stable explicit opcodes for every primitive of the pinned reference model.
These wire codes are independent of internal circuit dispatch codes. -/
def primitives : Array Primitive := #[
  .natAdd, .natSub, .natMul, .natDiv, .natMod, .natEq, .natLt,
  .strAppend, .strLength, .strEq,
  .word32Add, .word32Sub, .word32Mul, .word32And, .word32Or, .word32Xor,
  .word32Shl, .word32Shr, .word32Rotr, .word32Eq, .word32Lt,
  .word32ToBytes, .bytesToWord32, .word32ToField,
  .fieldAdd, .fieldSub, .fieldMul, .fieldInverse, .fieldEq,
  .fieldToBytes, .bytesToField,
  .extAdd, .extSub, .extMul, .extInverse, .extEq, .extPack, .extFst, .extSnd,
  .bytesLength, .bytesGet, .bytesAppend, .bytesSlice, .bytesEq, .blake3,
  .natToWord32, .word32ToNat, .fieldToNat, .natToField,
  .arrayEmpty, .arrayLength, .arrayGet, .arraySet, .arrayPush,
  .byteBuilderEmpty, .byteBuilderAppend, .byteBuilderFreeze, .byteBuilderLength]

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
  | fuel + 1, value => do
    writeNode
    match value with
    | .scalar scalar => do writeByte 0; writeScalar scalar
    | .ctor id fields => do
      writeByte 1; writeCtorId id; writeVector (writeValue fuel) fields
    | .pap function captured => do
      writeByte 2; writeNatural function; writeVector (writeValue fuel) captured
    | .erased => writeByte 3
    | .array elements => do writeByte 4; writeVector (writeValue fuel) elements
    | .byteBuilder _ => throw .internalValue

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

def writeProgram (profile : Profile) (program : Program) : Encoder Unit := do
  writeHeader "IXBF"
  for n in profile.parameters do writeNatural n
  writeNatural profile.maxSteps
  writeNatural program.entry
  writeVector (fun ctor => do writeCtorId ctor.id; writeNatural ctor.fields) program.constructors
  writeVector writeFunction program.functions

end Internal
open Internal

/-- IXFP revision 0, current IXBF format/semantics, ten u128 limits, u64 fuel.
The exact 184 bytes match the native prover's FunctionalProfile. -/
def encodeProfile (profile : Profile) : Except Error Bytes := do
  profile.validate |>.mapError .profile
  encode 184 0 do
    writeBytes "IXFP".toUTF8.data
    writeU32 0
    writeU32 wireVersion
    writeU32 semanticVersion
    for parameter in profile.parameters do writeNat 16 parameter
    writeNat 8 profile.maxSteps

def encodeProgram (profile : Profile) (program : Program) : Except Error Bytes := do
  profile.validateProgram program |>.mapError .profile
  encode profile.programBytes 0 (writeProgram profile program)

def validateInput (profile : Profile) (program : Program) (input : Array Value) :
    Except Error Unit := do
  profile.validateProgram program |>.mapError .profile
  let function ← program.getFunction program.entry
    |>.mapError (Error.profile ∘ ProfileError.reference)
  if input.size != function.arity then
    throw (.profile (.reference (.arityMismatch function.arity input.size)))
  profile.validateValues program input |>.mapError .profile

def encodeInput (profile : Profile) (program : Program) (input : Array Value) :
    Except Error Bytes := do
  validateInput profile program input
  encode profile.valueBytes profile.limits.inputNodes do
    writeHeader "IXFI"
    writeVector (writeValue profile.valueDepth) input

def encodeOutput (profile : Profile) (program : Program) (output : Value) :
    Except Error Bytes := do
  profile.validateProgram program |>.mapError .profile
  profile.validateValues program #[output] |>.mapError .profile
  encode profile.valueBytes profile.limits.inputNodes do
    writeHeader "IXFO"
    writeValue profile.valueDepth output

end Ix.Ixby.Codec
