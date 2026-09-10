module
public import Ix.Ixby.Codec.Decode

/-! Byte-oriented reference execution with checked canonical artifacts. This
is an experimental executable contract for proving backends, not a new
production Claim variant or a cryptographic proof of an execution. -/

public section
@[expose] section

namespace Ix.Ixby.Codec

/-- A successful host/reference run retains the exact decoded images and
kernel-checked equations for both execution and output encoding. -/
structure Execution (profile : Profile) (programBytes inputBytes : Bytes) where
  program : Decoded (encodeProgram profile) programBytes
  input : Decoded (encodeInput profile program.value) inputBytes
  output : Value
  outputBytes : Bytes
  encoded : encodeOutput profile program.value output = .ok outputBytes
  fuel : Nat
  evaluated : profile.execute program.value input.value fuel = .ok output

def execute (profile : Profile) (programBytes inputBytes : Bytes) (fuel : Nat) :
    Except Error (Execution profile programBytes inputBytes) := do
  let program ← decodeProgram profile programBytes
  let input ← decodeInput profile program.value inputBytes
  match evaluated : profile.execute program.value input.value fuel with
  | .error error => throw (.profile error)
  | .ok output =>
    match encoded : encodeOutput profile program.value output with
    | .error error => throw error
    | .ok outputBytes =>
      return { program := program, input, output, outputBytes, encoded, fuel, evaluated }

/-- The target byte-execution proposition: a finite, fully admitted run of
this exact image/input yields these exact output bytes. -/
def Evaluates (profile : Profile) (programBytes inputBytes outputBytes : Bytes) : Prop :=
  ∃ fuel, (execute profile programBytes inputBytes fuel).map (·.outputBytes) = .ok outputBytes

/-- The byte boundary connects to the original functional execution relation,
without treating serialization or profiled execution as an arbitrary oracle. -/
theorem Execution.reference_evaluates {profile : Profile} {programBytes inputBytes : Bytes}
    (execution : Execution profile programBytes inputBytes) :
    Ix.Ixby.Evaluates profile.limits execution.program.value execution.input.value execution.output :=
  ⟨execution.fuel, Profile.execute_refines execution.evaluated⟩

end Ix.Ixby.Codec
