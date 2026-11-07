import IxCC.Ixon.V3.Resource.Addressed

/-! Versioned source admission for the ix frontend. These objects retain the
exact bytes and contracts consumed by resource admission. They do not assert
erased Lean typing, backend simulation, or an IxVM resource proof. -/

namespace IxCC.Ixon.V3

structure ResourceClaim where
  subject : Address
  profile : Address
  deriving BEq, DecidableEq, Repr

/-- The resource claim: TagN(4) flag `0xE` value 9 (bytes `E8 01`), the object
format, validator 2 (resource-v1), subject and profile. -/
def ResourceClaim.bytes (claim : ResourceClaim) : ByteArray := _root_.Ixon.runPut do
  _root_.Ixon.putTagN 4 0xE 9
  _root_.Ixon.putU8 objectFormat
  _root_.Ixon.putU8 2
  _root_.Ixon.putBytes claim.subject.hash
  _root_.Ixon.putBytes claim.profile.hash

/-- Parse only the native resource claim variant. This checks framing and
identity tags, not the truth of the claim. -/
def ResourceClaim.decode (bytes : ByteArray) : Except String ResourceClaim :=
  _root_.Ixon.runGetExact (do
    let tag ← _root_.Ixon.getTagN 4
    unless tag.flag == 0xE && tag.value == 9 do
      throw "ixon-v4: expected a resource claim"
    unless (← _root_.Ixon.getU8) == objectFormat do throw "ixon-v4: claim object format mismatch"
    unless (← _root_.Ixon.getU8) == 2 do throw "ixon-v4: claim validator mismatch"
    return ⟨← getAddress, ← getAddress⟩) bytes

structure ResourceInput (bytes profileBytes : ByteArray) where
  env : Env
  profile : Resource.Profile
  resolved : Resource.AddressedProgram
  decoded : decodeAnonymousEnv bytes = .ok env
  profileDecoded : Resource.Profile.ofBytes profileBytes = .ok profile
  admitted : Resource.Addressed.checkResources env profile = .ok resolved

/-- The source entry point for future v3 lowering. Keep this evidence and
the source root through later passes; no conversion to v2 is implicit. -/
def admitResources (bytes profileBytes : ByteArray) :
    Except String (ResourceInput bytes profileBytes) := do
  match decoded : decodeAnonymousEnv bytes with
  | .error error => throw error
  | .ok env =>
    match profileDecoded : Resource.Profile.ofBytes profileBytes with
    | .error error => throw error
    | .ok profile =>
      if profile.limits.depth > 256 || profile.limits.steps > 500000 then
        throw "ixon-v3: profile exceeds consumer checker budget"
      match admitted : Resource.Addressed.checkResources env profile with
      | .error error => throw error
      | .ok resolved => return { env, profile, resolved, decoded, profileDecoded, admitted }

/-- A claim's subject/profile must match this exact admitted source. This
binding check intentionally does not certify its separate typing statement. -/
def ResourceInput.checkClaimBinding {bytes profileBytes : ByteArray}
    (input : ResourceInput bytes profileBytes) (claimBytes : ByteArray) : Except String Unit := do
  let claim ← ResourceClaim.decode claimBytes
  unless claim.subject == input.env.root do throw "ixon-v3: claim subject mismatch"
  unless claim.profile == input.resolved.profileAddress do throw "ixon-v3: claim profile mismatch"

theorem ResourceInput.resources_checked {bytes profileBytes : ByteArray}
    (input : ResourceInput bytes profileBytes) :
    Resource.Addressed.checkResources input.env input.profile = .ok input.resolved :=
  input.admitted

theorem ResourceInput.source_decoded {bytes profileBytes : ByteArray}
    (input : ResourceInput bytes profileBytes) : decodeAnonymousEnv bytes = .ok input.env :=
  input.decoded

end IxCC.Ixon.V3
