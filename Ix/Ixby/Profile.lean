module
public import Ix.Ixby.Eval

/-! The first, explicitly experimental cryptographic target profile. It admits
functional control with Bool, Word32, canonical Goldilocks/extension elements,
and bounded bytes. Arbitrary Nat and String operations remain in the reference
machine but are NOT silently accepted by this initial proving target. This
module supplies admission/reference execution, not an Aiur execution proof. -/

public section
@[expose] section

namespace Ix.Ixby

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
  -- The excluded scalar families cannot be re-enabled by changing capacities.
  unless profile.limits.natBits == 0 && profile.limits.stringBytes == 0 do
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

def Profile.validateProgram (profile : Profile) (program : Program) :
    Except ProfileError Unit := do
  profile.validate
  Ix.Ixby.validateProgram profile.limits program |>.mapError .reference
  unless program.functions.all (fun f => f.blocks.all (·.instruction.cryptoSupported)) do
    throw .unsupportedInstruction

/-- A shared work list carries each node's remaining depth. Neither the node
budget nor the depth budget resets when traversing siblings. -/
def cryptoValuesSupported : Nat → List (Value × Nat) → Except ProfileError Unit
  | _, [] => .ok ()
  | 0, _ :: _ => .error (.reference (.limit .inputNodes))
  | fuel + 1, (value, depth) :: rest => do
    let nextDepth ← match depth with
      | 0 => throw .depth
      | d + 1 => pure d
    let children ← match value with
      | .scalar s =>
        if s.cryptoSupported then pure #[] else throw .unsupportedScalar
      | .ctor _ fields | .pap _ fields => pure fields
      | .erased => pure #[]
    cryptoValuesSupported fuel ((children.toList.map (·, nextDepth)) ++ rest)

def Profile.validateValues (profile : Profile) (program : Program) (values : Array Value) :
    Except ProfileError Unit := do
  profile.validate
  validateInputValues profile.limits program profile.limits.inputNodes values.toList
    |>.mapError .reference
  cryptoValuesSupported profile.limits.inputNodes (values.toList.map (·, profile.valueDepth))

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
