module
import Tests.Ixby.Common
import Ix.Ixby.Flock.Contract

namespace Tests.Ixby.Flock.Contract

open Ix.Ixby Ix.Ixby.FlockBackend

private def digest (byte : UInt8) : Commitment.Digest :=
  ⟨Array.replicate 32 byte, by simp⟩

private def request : ExecSetupInput := {
  profile := { programBytes := 64, valueBytes := 64, maxSteps := 8 }
  capacity := {
    steps := 8, programBytes := 64, inputBytes := 64, outputBytes := 64
    memoryCells := 256, frameCells := 32 }
  primitives := { identity := digest 1, enabled := #[.word32Add, .word32Eq] }
  flockProtocol := digest 2
  backendImplementation := digest 3
}

private def rejects (request : ExecSetupInput) : Bool := !request.validate.isOk

private def checks : IO (List Check) := do
  return [
    ("exact physical admission boundary", request.validate.isOk),
    ("zero step capacity rejected", rejects { request with capacity.steps := 0 }),
    ("oversized cell capacity rejected", rejects { request with capacity.memoryCells := 2 ^ 32 }),
    ("insufficient step capacity rejected", rejects { request with capacity.steps := 7 }),
    ("insufficient program capacity rejected", rejects { request with capacity.programBytes := 63 }),
    ("insufficient input capacity rejected", rejects { request with capacity.inputBytes := 63 }),
    ("insufficient output capacity rejected", rejects { request with capacity.outputBytes := 63 }),
    ("invalid semantic profile rejected", rejects { request with profile.limits.natBits := 1 }),
    ("unregistered semantic primitive rejected", rejects
      { request with primitives.enabled := #[.natAdd] }),
    ("duplicate registry opcode rejected", rejects
      { request with primitives.enabled := #[.word32Add, .word32Add] }),
    ("fixed template with both Exec limbs", (validatePublicTemplate
      #[.fixed 1 2, .execDigestLow, .fixed 3 4, .execDigestHigh]).isOk),
    ("missing low digest limb rejected", !(validatePublicTemplate #[.execDigestHigh]).isOk),
    ("missing high digest limb rejected", !(validatePublicTemplate #[.execDigestLow]).isOk),
    ("duplicate digest limb rejected", !(validatePublicTemplate
      #[.execDigestLow, .execDigestLow, .execDigestHigh]).isOk)
  ]

public def suite : IO UInt32 := runChecks "ixby-flock-contract" checks

end Tests.Ixby.Flock.Contract
