module

public import Ix.Claim
public import Ix.Resource.Validate

/-! A resource claim bound the complete constant set, format v4,
resource-v1 validator, and the canonical policy bytes. The claim is retired:
every reader refuses its tag, and `makeClaim` refuses to make one.

`resource-v1`'s typing half is `Ix.Resource.typeCheck`: IxC's tiered Ixon
entry, with its theorem (`checkBytesTieredUsing_ok`) and the prepared binding
and prelude, over everything it admits,
and uncertified IxC typing for unsafe inductives, assumption axioms and the
records that depend on them (`Ix.Resource.Typing` says which part rests on
which). The claim stays uncertified as a resource claim. -/

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

def makeClaim (_env : Ixon.Env) (_profile : Profile) : Except String Ix.Claim :=
  throw "resource validator: the resource claim is retired"

end Ix.Resource

end
