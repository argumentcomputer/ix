module
public import Ix.Ixby.Eval

/-! Explicitly versioned experimental cryptographic profiles. Revision 0 admits
functional control with Bool, Word32, canonical Goldilocks/extension elements,
and bounded bytes. Revision 1 additionally admits exact Nat arithmetic bounded
by `natBits`; String remains excluded. This module supplies admission/reference
execution, not a claim that either native proving backend implements revision 1. -/

public section
@[expose] section

namespace Ix.Ixby

/-- New scalar/opcode families require an explicit revision, not a capacity
change. Revision 0 remains the default and retains its exact existing bytes. -/
inductive ProfileRevision where
  | cryptoV0
  | cryptoNatV1
  deriving BEq, DecidableEq, Repr, Inhabited

def ProfileRevision.number : ProfileRevision → Nat
  | .cryptoV0 => 0
  | .cryptoNatV1 => 1

/-- The codec and commitment modules serialize and bind all these parameters;
this module alone is not a commitment or production Claim/Exec wire version.
`limits.inputNodes` bounds both an input forest and an output value here.
Depth is enforced here; programBytes/valueBytes are enforced at the codec
boundary, not by logical execution alone. These are not object IDs. -/
structure Profile where
  limits : Limits := { natBits := 0, stringBytes := 0 }
  programBytes : Nat := 16777216
  valueBytes : Nat := 16777216
  valueDepth : Nat := 256
  maxSteps : Nat := 1000000
  revision : ProfileRevision := .cryptoV0
  deriving BEq, Repr, Inhabited

inductive ProfileError where
  | reference (error : Error)
  | configuration
  | unsupportedScalar
  | unsupportedInstruction
  | steps
  | depth
  deriving BEq, DecidableEq, Repr, Inhabited

def Profile.parameters (profile : Profile) : Array Nat :=
  let l := profile.limits
  #[l.functions, l.constructors, l.blocks, l.locals, l.operands, l.continuations,
    l.inputNodes, l.natBits, l.stringBytes, l.byteArrayBytes,
    profile.programBytes, profile.valueBytes, profile.valueDepth, profile.maxSteps]

def Profile.validate (profile : Profile) : Except ProfileError Unit := do
  unless profile.parameters.all (· < 2 ^ 32) do throw .configuration
  -- A capacity change alone cannot enable Nat in the revision-0 protocol.
  unless (profile.revision == .cryptoNatV1 || profile.limits.natBits == 0) &&
      profile.limits.stringBytes == 0 do
    throw .configuration

def Scalar.cryptoSupported : Scalar → Bool
  | .nat _ | .str _ => false
  | .bool _ | .word32 _ | .field _ | .extField _ | .bytes _ => true

def Operand.cryptoSupported : Operand → Bool
  | .literal s => s.cryptoSupported
  | _ => true

/-- Explicit ordered opcode table for the experimental crypto v0 codec, starting
at zero. It is not derived from the Lean constructor order; excluded primitives
have no entry. They are not a production protocol; changes must be coordinated
with the experimental codec's wire and semantic revisions. -/
def cryptoPrimitives : Array Primitive := #[
  .word32Add, .word32Sub, .word32Mul, .word32And, .word32Or, .word32Xor,
  .word32Shl, .word32Shr, .word32Rotr, .word32Eq, .word32Lt,
  .word32ToBytes, .bytesToWord32, .word32ToField,
  .fieldAdd, .fieldSub, .fieldMul, .fieldInverse, .fieldEq,
  .fieldToBytes, .bytesToField,
  .extAdd, .extSub, .extMul, .extInverse, .extEq, .extPack, .extFst, .extSnd,
  .bytesLength, .bytesGet, .bytesAppend, .bytesSlice, .bytesEq, .blake3]

def Primitive.cryptoOpcode (op : Primitive) : Option Nat :=
  cryptoPrimitives.toList.findIdx? (· == op)

def Op.cryptoSupported : Op → Bool
  | .copy value | .project value _ => value.cryptoSupported
  | .primitive op args => op.cryptoOpcode.isSome && args.all (·.cryptoSupported)
  | .construct _ args | .closure _ args | .call _ args | .callSelf args =>
    args.all (·.cryptoSupported)
  | .apply value args => value.cryptoSupported && args.all (·.cryptoSupported)

def Instr.cryptoSupported : Instr → Bool
  | .letOp op _ => op.cryptoSupported
  | .ret value | .caseCtor value _ | .branch value _ _ => value.cryptoSupported
  | .tailCall _ args | .tailCallSelf args => args.all (·.cryptoSupported)
  | .tailApply value args => value.cryptoSupported && args.all (·.cryptoSupported)
  | .caseNat .. => false

/-- Revision 1 appends these seven exact-Nat operations at opcodes 35–41.
The pre-existing 0–34 table is unchanged; no implicit Nat/Word32 conversions
are introduced. Subtraction saturates at zero, `n / 0 = 0`, and `n % 0 = n`,
as defined by the reference `Primitive.eval`. -/
def cryptoNatPrimitives : Array Primitive := #[
  .natAdd, .natSub, .natMul, .natDiv, .natMod, .natEq, .natLt]

def Profile.primitives (profile : Profile) : Array Primitive :=
  match profile.revision with
  | .cryptoV0 => cryptoPrimitives
  | .cryptoNatV1 => cryptoPrimitives ++ cryptoNatPrimitives

def Profile.primitiveOpcode (profile : Profile) (op : Primitive) : Option Nat :=
  profile.primitives.toList.findIdx? (· == op)

def Profile.scalarSupported (profile : Profile) : Scalar → Bool
  | .nat _ => profile.revision == .cryptoNatV1
  | scalar => scalar.cryptoSupported

def Profile.operandSupported (profile : Profile) : Operand → Bool
  | .literal scalar => profile.scalarSupported scalar
  | _ => true

def Profile.opSupported (profile : Profile) : Op → Bool
  | .copy value | .project value _ => profile.operandSupported value
  | .primitive op args =>
    (profile.primitiveOpcode op).isSome && args.all profile.operandSupported
  | .construct _ args | .closure _ args | .call _ args | .callSelf args =>
    args.all profile.operandSupported
  | .apply value args => profile.operandSupported value && args.all profile.operandSupported

def Profile.instrSupported (profile : Profile) : Instr → Bool
  | .letOp op _ => profile.opSupported op
  | .ret value | .caseCtor value _ | .branch value _ _ => profile.operandSupported value
  | .tailCall _ args | .tailCallSelf args => args.all profile.operandSupported
  | .tailApply value args => profile.operandSupported value && args.all profile.operandSupported
  | .caseNat value _ _ => profile.revision == .cryptoNatV1 && profile.operandSupported value

def Profile.validateProgram (profile : Profile) (program : Program) :
    Except ProfileError Unit := do
  profile.validate
  Ix.Ixby.validateProgram profile.limits program |>.mapError .reference
  unless program.functions.all (fun f => f.blocks.all (fun b => profile.instrSupported b.instruction)) do
    throw .unsupportedInstruction

/-- A shared work list carries each node's remaining depth. Neither the node
budget nor the depth budget resets when traversing siblings. -/
def Profile.valuesSupported (profile : Profile) : Nat → List (Value × Nat) → Except ProfileError Unit
  | _, [] => .ok ()
  | 0, _ :: _ => .error (.reference (.limit .inputNodes))
  | fuel + 1, (value, depth) :: rest => do
    let nextDepth ← match depth with
      | 0 => throw .depth
      | d + 1 => pure d
    let children ← match value with
      | .scalar s =>
        if profile.scalarSupported s then pure #[] else throw .unsupportedScalar
      | .ctor _ fields | .pap _ fields => pure fields
      | .erased => pure #[]
    profile.valuesSupported fuel ((children.toList.map (·, nextDepth)) ++ rest)

/-- Legacy revision-0 admission helper. -/
def cryptoValuesSupported : Nat → List (Value × Nat) → Except ProfileError Unit :=
  Profile.valuesSupported {}

def Profile.validateValues (profile : Profile) (program : Program) (values : Array Value) :
    Except ProfileError Unit := do
  profile.validate
  validateInputValues profile.limits program profile.limits.inputNodes values.toList
    |>.mapError .reference
  profile.valuesSupported profile.limits.inputNodes (values.toList.map (·, profile.valueDepth))

/-- The profiled reference boundary additionally admits the output value.
Wire byte-size limits are enforced by the codecs; this is not byte execution. -/
def Profile.execute (profile : Profile) (program : Program) (input : Array Value) (fuel : Nat) :
    Except ProfileError Value := do
  profile.validateProgram program
  profile.validateValues program input
  if fuel > profile.maxSteps then throw .steps
  let output ← Ix.Ixby.execute profile.limits program input fuel |>.mapError .reference
  profile.validateValues program #[output]
  return output

/-- Profile admission only restricts execution; it does not replace the
functional machine's successful-execution meaning. -/
theorem Profile.execute_refines {profile : Profile} {program : Program}
    {input : Array Value} {fuel : Nat} {output : Value}
    (success : profile.execute program input fuel = .ok output) :
    Ix.Ixby.execute profile.limits program input fuel = .ok output := by
  unfold Profile.execute at success
  simp only [Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] at success
  cases admitted : profile.validateProgram program with
  | error error => simp [admitted] at success
  | ok _ =>
    cases inputs : profile.validateValues program input with
    | error error => simp [admitted, inputs] at success
    | ok _ =>
      by_cases steps : fuel > profile.maxSteps
      · simp [admitted, inputs, steps] at success
      · cases evaluated : Ix.Ixby.execute profile.limits program input fuel with
        | error error => simp [admitted, inputs, steps, evaluated] at success
        | ok value =>
          cases outputs : profile.validateValues program #[value] with
          | error error => simp [admitted, inputs, steps, evaluated, outputs] at success
          | ok _ =>
            simp [admitted, inputs, steps, evaluated, outputs] at success
            exact congrArg Except.ok success

end Ix.Ixby
