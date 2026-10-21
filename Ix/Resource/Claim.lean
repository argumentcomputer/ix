module

public import Ix.Claim
public import Ix.Resource.Validate

/-! A resource claim binds the complete constant set, format v4,
resource-v1 validator, and the canonical policy bytes.

`resource-v1`'s typing half is IxC's tiered Ixon entry over the whole
environment (`Ix.Resource.typeCheck`); the claim stays uncertified as a
resource claim. An environment holding an unsafe inductive does not validate
(the tiered entry declines its records, divergence Q2 from `Ix.Tc`) until step
10d types such records beside the batch tier. -/

@[expose] public section

namespace Ix.Resource

def checkClaim (env : Ixon.Env) (profile : Profile) (claim : Ix.Claim) :
    Except String AddressedProgram := do
  let .resource root expectedProfile := claim
    | throw "resource validator: claim uses a different validator"
  unless env.merkleRoot == some root do
    throw "resource validator: claim subject differs from the complete constant set"
  unless (← profile.address) == expectedProfile do
    throw "resource validator: claim profile differs from the supplied policy"
  validate env profile

def makeClaim (env : Ixon.Env) (profile : Profile) : Except String Ix.Claim := do
  let some root := env.merkleRoot | throw "resource validator: empty claim subject"
  let claim := Ix.Claim.resource root (← profile.address)
  let _ ← checkClaim env profile claim
  return claim

end Ix.Resource

end
