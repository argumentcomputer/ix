module
public import Ix.Ixby.Commitment

/-! Experimental execution claims, separate from production `Ix.Claim`.
The public projection hides only the input commitment. It still commits to
the approved profile, exact guest image, and caller's expected result. -/

public section
@[expose] section

namespace Ix.Ixby.Claim

open Commitment (Digest Statement)
open Codec (Bytes)

structure PublicStatement where
  profile : Digest
  program : Digest
  output : Digest
  deriving BEq, DecidableEq, Repr

def publicStatement (statement : Statement) : PublicStatement :=
  ⟨statement.profile, statement.program, statement.output⟩

/-- Domain 5 is distinct from the complete four-component statement (4). -/
def PublicStatement.digest (statement : PublicStatement) : Digest :=
  Commitment.hash .publicResult (statement.profile.bytes ++
    statement.program.bytes ++ statement.output.bytes)

/-- The payload-level constructor is not an admission or execution check. -/
def bindPublic (profileBytes programBytes outputBytes : Bytes) : PublicStatement :=
  let profile := Commitment.hash .profile profileBytes
  let program := Commitment.hash .program (profile.bytes ++ programBytes)
  ⟨profile, program, Commitment.hash .output (program.bytes ++ outputBytes)⟩

theorem public_bind (profileBytes programBytes inputBytes outputBytes : Bytes) :
    publicStatement (Commitment.Internal.bind profileBytes programBytes inputBytes outputBytes) =
      bindPublic profileBytes programBytes outputBytes := rfl

/-- Public policy supplies the exact guest and expected canonical output;
neither private input bytes nor their commitment are needed here. -/
def ofPublicArtifacts (profile : Profile) (programBytes outputBytes : Bytes) :
    Except Codec.Error PublicStatement := do
  let profileBytes ← Codec.encodeProfile profile
  let program ← Codec.decodeProgram profile programBytes
  let _ ← Codec.decodeOutput profile program.value outputBytes
  return bindPublic profileBytes programBytes outputBytes

/-- Initial result ABI: success is the bytes of the canonical public claim;
failure is `Value.erased`. They have different canonical value tags. This is
an explicitly chosen wrapper ABI, not Lean's constructor layout for Option. -/
def claimResult (canonicalClaim : Bytes) : Value := .scalar (.bytes canonicalClaim)

def ofPublicClaim (profile : Profile) (programBytes canonicalClaim : Bytes) :
    Except Codec.Error PublicStatement := do
  let program ← Codec.decodeProgram profile programBytes
  let outputBytes ← Codec.encodeOutput profile program.value (claimResult canonicalClaim)
  ofPublicArtifacts profile programBytes outputBytes

/-- A semantic opening contains a real finite, canonically admitted byte run.
The host/prover may construct one, but a backend soundness proof must recover
this evidence from constraints; a witness generator is not that proof. -/
structure Opening (profile : Profile) (statement : Statement) where
  profileBytes : Bytes
  programBytes : Bytes
  inputBytes : Bytes
  outputBytes : Bytes
  profileEncoded : Codec.encodeProfile profile = .ok profileBytes
  evaluated : Codec.Evaluates profile programBytes inputBytes outputBytes
  bound : Commitment.Internal.bind profileBytes programBytes inputBytes outputBytes = statement

def Exec (profile : Profile) (statement : Statement) : Prop :=
  Nonempty (Opening profile statement)

/-- The input digest remains in the constrained Stage 3 statement, even when
it is existential in the terminal relation. No discarded or host-only link. -/
def PublicExec (profile : Profile) (expected : PublicStatement) : Prop :=
  ∃ statement, publicStatement statement = expected ∧ Exec profile statement

theorem exec_public {profile : Profile} {statement : Statement}
    (executed : Exec profile statement) :
    PublicExec profile (publicStatement statement) := ⟨statement, rfl, executed⟩

end Ix.Ixby.Claim
