import Compilatrix.Ixby.Certificate

/-! Exact upstream revision-0 program/profile/input/output bytes. The current
codec excludes Nat/String; the general reference machine remains available. -/

namespace Compilatrix.Ixby

open Ix.Ixby (Profile)
open Ix.Ixby.Codec (Bytes)

deriving instance DecidableEq for Ix.Ixby.Limits
deriving instance DecidableEq for Ix.Ixby.Function
deriving instance DecidableEq for Ix.Ixby.Program

def Config.crypto (profile : Profile := {}) : Config :=
  { limits := profile.limits, proving := true }

/-- Exact image and limit binding, established by compiling, encoding, and
decoding with the unmodified upstream implementation. -/
structure Exported {source config} (compiled : Compiled source config) (profile : Profile) where
  profileBytes : Bytes
  profileEncoded : Ix.Ixby.Codec.encodeProfile profile = .ok profileBytes
  programBytes : Bytes
  encoded : Ix.Ixby.Codec.encodeProgram profile compiled.program = .ok programBytes
  program : Ix.Ixby.Codec.Decoded (Ix.Ixby.Codec.encodeProgram profile) programBytes
  readProgram : Ix.Ixby.Codec.decodeProgram profile programBytes = .ok program
  exactProgram : program.value = compiled.program
  exactLimits : profile.limits = config.limits

def Compiled.export {source config} (compiled : Compiled source config) (profile : Profile := {}) :
    Except String (Exported compiled profile) := do
  if exactLimits : profile.limits = config.limits then
    match profileEncoded : Ix.Ixby.Codec.encodeProfile profile with
    | .error error => throw s!"Ixby profile encoding: {reprStr error}"
    | .ok profileBytes =>
      match encoded : Ix.Ixby.Codec.encodeProgram profile compiled.program with
      | .error error => throw s!"Ixby program encoding: {reprStr error}"
      | .ok programBytes =>
        match readProgram : Ix.Ixby.Codec.decodeProgram profile programBytes with
        | .error error => throw s!"Ixby program decoding: {reprStr error}"
        | .ok program =>
          if exactProgram : program.value = compiled.program then
            return { profileBytes, profileEncoded, programBytes, encoded, program, readProgram, exactProgram, exactLimits }
          else throw "Ixby decoded program differs from the compiler image"
  else throw "Ixby export profile limits differ from the compiled limits"

/-- A checked run binds source data, the actual compiler image, and all four
canonical byte artifacts. The retained reference execution is not a SNARK. -/
structure ByteCertificate {source config compiled profile}
    (exported : @Exported source config compiled profile) (input : Array Data) (decodeFuel : Nat) where
  reference : RunCertificate compiled input decodeFuel
  inputBytes : Bytes
  inputEncoded : Ix.Ixby.Codec.encodeInput profile compiled.program reference.encodedInput = .ok inputBytes
  execution : Ix.Ixby.Codec.Execution profile exported.programBytes inputBytes
  executed : Ix.Ixby.Codec.execute profile exported.programBytes inputBytes reference.targetFuel = .ok execution
  decoded : decodeData source decodeFuel execution.output = some reference.result

def Exported.certify {source config compiled profile}
    (exported : @Exported source config compiled profile) (input : Array Data := #[])
    (sourceFuel : Nat := 100000) (targetFuel : Nat := 1000000) (decodeFuel : Nat := 10000) :
    Except String (ByteCertificate exported input decodeFuel) := do
  let reference ← compiled.certify input sourceFuel targetFuel decodeFuel
  match inputEncoded : Ix.Ixby.Codec.encodeInput profile compiled.program reference.encodedInput with
  | .error error => throw s!"Ixby input encoding: {reprStr error}"
  | .ok inputBytes =>
    match executed : Ix.Ixby.Codec.execute profile exported.programBytes inputBytes reference.targetFuel with
    | .error error => throw s!"Ixby canonical execution: {reprStr error}"
    | .ok execution =>
      match decoded : decodeData source decodeFuel execution.output with
      | none => throw "Ixby canonical output is outside the data ABI"
      | some data =>
        if equal : Data.equal data reference.result then
          have same := Data.eq_of_equal data reference.result equal
          return { reference, inputBytes, inputEncoded, execution, executed, decoded := same ▸ decoded }
        else throw "Ixby canonical execution disagrees with the source certificate"

end Compilatrix.Ixby
