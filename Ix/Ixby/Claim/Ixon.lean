module
public import Ix.Ixby.Claim
public import Ix.Claim

/-! Public Ixon boundary for the experimental Exec wrapper. This host adapter
is deliberately outside the pure `Ix.Ixby` import: `Ix.Claim` transitively
imports the native address-hashing implementation. No native parser/hash is
therefore smuggled into the execution-reflection theorem.

Initial application policy covers only a closed `checkEnv` claim. Supporting
other kinds or assumptions needs an explicit source-verifier adapter; never
drop their tags or assumptions to coerce them into this policy. -/

public section
@[expose] section

namespace Ix.Ixby.Claim.IxonAdapter

inductive Error where
  | claimLength
  | claimKind
  | claimDecode (message : String)
  | claimCanonical
  | codec (error : Codec.Error)
  deriving BEq, Repr, Inhabited

/-- Carries the exact public serialization equation, not just a digest picked
by the prover. `Address` itself does not enforce its byte width. -/
structure ClosedPublicClaim (bytes : ByteArray) where
  root : Address
  rootSize : root.hash.size = 32
  canonical : Ix.Claim.ser (.checkEnv root none) = bytes

def ClosedPublicClaim.claim {bytes : ByteArray} (checked : ClosedPublicClaim bytes) : Ix.Claim :=
  .checkEnv checked.root none

/-- Check the small allowed envelope before invoking the general Ixon parser.
The exact size/tag also rules out hostile variable-length claim structures. -/
def decodePublicClaim (bytes : ByteArray) : Except Error (ClosedPublicClaim bytes) := do
  unless bytes.size == 34 do throw .claimLength
  unless bytes[0]! == 0xe5 && bytes[33]! == 0 do throw .claimKind
  let claim ← _root_.Ixon.runGetExact Ix.Claim.get bytes |>.mapError .claimDecode
  match claim with
  | .checkEnv root none =>
    if rootSize : root.hash.size = 32 then
      if canonical : Ix.Claim.ser (.checkEnv root none) = bytes then
        return ⟨root, rootSize, canonical⟩
      else throw .claimCanonical
    else throw .claimLength
  | _ => throw .claimKind

/-- Reconstruct the public circuit statement from a caller-supplied claim and
the *approved* guest/profile. This performs no execution or cryptographic
verification and does not itself approve a compiler certificate. -/
def expected (approvedProfile : Profile) (approvedProgram : Codec.Bytes)
    (publicClaim : Ix.Claim) : Except Error PublicStatement := do
  -- Address is not intrinsically width-checked. Validate the original typed
  -- claim before serialization: malformed conditional addresses must not
  -- shift an assumptions tag into a different closed root's byte envelope.
  match publicClaim with
  | .checkEnv root none => unless root.hash.size == 32 do throw .claimLength
  | _ => throw .claimKind
  let bytes := Ix.Claim.ser publicClaim
  let _ ← decodePublicClaim bytes
  ofPublicClaim approvedProfile approvedProgram bytes.data |>.mapError .codec

/-- The final API shape: the application supplies public C, while input/proof
material remains behind the terminal verifier. Passing an arbitrary callback
or guest here does not establish the composition contract. -/
def verifyWith {Proof : Type} (approvedProfile : Profile) (approvedProgram : Codec.Bytes)
    (verifyTerminal : PublicStatement → Proof → Bool) (publicClaim : Ix.Claim)
    (proof : Proof) : Except Error Bool := do
  let statement ← expected approvedProfile approvedProgram publicClaim
  return verifyTerminal statement proof

end Ix.Ixby.Claim.IxonAdapter
