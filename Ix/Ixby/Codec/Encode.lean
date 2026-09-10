module
public import Ix.Ixby.Codec.Common

/-! Canonical encoding for the experimental crypto profile. External values
are inline finite trees: sharing and physical object identifiers are not ABI
values. All code and declarations, including unreachable ones, are encoded. -/

public section
@[expose] section

namespace Ix.Ixby.Codec
namespace Internal

def writeScalar (profile : Profile) (scalar : Scalar) : Encoder Unit := do
  scalar.validate profile.limits |>.mapError (Error.profile ∘ ProfileError.reference)
  match scalar with
  | .bool value => writeByte 0; writeByte (if value then 1 else 0)
  | .word32 value => writeByte 1; writeU32 value.toNat
  | .field value => writeByte 2; writeNat 8 value.val
  | .extField value =>
    writeByte 3; writeNat 8 value.c0.val; writeNat 8 value.c1.val
  | .bytes value => writeByte 4; writeU32 value.size; writeBytes value
  | .nat _ | .str _ => throw (.profile .unsupportedScalar)

def writeCtorId (id : CtorId) : Encoder Unit := do
  writeNat 32 id.block.val
  writeU32 id.member
  writeU32 id.tag

def writeValue (profile : Profile) : Nat → Value → Encoder Unit
  | 0, _ => throw .depthLimit
  | depth + 1, value => do
    writeNode
    match value with
    | .scalar scalar => writeByte 0; writeScalar profile scalar
    | .ctor id fields =>
      writeByte 1; writeCtorId id
      writeVector (writeValue profile depth) fields
    | .pap function captured =>
      writeByte 2; writeU32 function
      writeVector (writeValue profile depth) captured
    | .erased => writeByte 3

def writeOperand (profile : Profile) : Operand → Encoder Unit
  | .local slot => do writeByte 0; writeU32 slot
  | .literal scalar => do writeByte 1; writeScalar profile scalar
  | .erased => writeByte 2

def writeOperands (profile : Profile) (operands : List Operand) : Encoder Unit :=
  writeVector (writeOperand profile) operands.toArray

def writeOp (profile : Profile) : Op → Encoder Unit
  | .copy value => do writeByte 0; writeOperand profile value
  | .primitive primitive args => do
    writeByte 1
    let some opcode := primitive.cryptoOpcode | throw (.profile .unsupportedInstruction)
    writeNat 1 opcode
    writeOperands profile args
  | .construct ctor fields => do writeByte 2; writeU32 ctor; writeOperands profile fields
  | .project value field => do writeByte 3; writeOperand profile value; writeU32 field
  | .closure function captured => do writeByte 4; writeU32 function; writeOperands profile captured
  | .call function args => do writeByte 5; writeU32 function; writeOperands profile args
  | .callSelf args => do writeByte 6; writeOperands profile args
  | .apply function args => do writeByte 7; writeOperand profile function; writeOperands profile args

def writeAlternative (alternative : Alternative) : Encoder Unit := do
  writeU32 alternative.ctor
  writeU32 alternative.target

def writeInstr (profile : Profile) : Instr → Encoder Unit
  | .letOp op next => do writeByte 0; writeOp profile op; writeU32 next
  | .ret value => do writeByte 1; writeOperand profile value
  | .tailCall function args => do writeByte 2; writeU32 function; writeOperands profile args
  | .tailCallSelf args => do writeByte 3; writeOperands profile args
  | .tailApply function args => do writeByte 4; writeOperand profile function; writeOperands profile args
  | .caseCtor value alternatives => do
    writeByte 5; writeOperand profile value
    writeVector writeAlternative alternatives.toArray
  | .caseNat .. => throw (.profile .unsupportedInstruction)
  | .branch condition ifTrue ifFalse => do
    writeByte 6; writeOperand profile condition; writeU32 ifTrue; writeU32 ifFalse

def writeFunction (profile : Profile) (function : Function) : Encoder Unit := do
  writeU32 function.arity
  writeU32 function.entry
  writeVector (fun block => do
    writeU32 block.locals
    writeInstr profile block.instruction) function.blocks

def writeProgram (profile : Profile) (program : Program) : Encoder Unit := do
  writeHeader "IXBY"
  writeU32 program.entry
  writeVector (fun ctor => do writeCtorId ctor.id; writeU32 ctor.fields) program.constructors
  writeVector (writeFunction profile) program.functions

end Internal

open Internal

/-- Fixed-size profile envelope: magic, wire revision, semantic revision,
and the fourteen capacities in `Profile.parameters`, all little-endian u32. -/
def encodeProfile (profile : Profile) : Except Error Bytes := do
  profile.validate |>.mapError .profile
  encode 68 0 do
    writeHeader "IXBP"
    writeU32 semanticVersion
    for parameter in profile.parameters do writeU32 parameter

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
    writeHeader "IXBI"
    writeVector (writeValue profile profile.valueDepth) input

def encodeOutput (profile : Profile) (program : Program) (output : Value) :
    Except Error Bytes := do
  profile.validateProgram program |>.mapError .profile
  profile.validateValues program #[output] |>.mapError .profile
  encode profile.valueBytes profile.limits.inputNodes do
    writeHeader "IXBO"
    writeValue profile profile.valueDepth output

end Ix.Ixby.Codec
