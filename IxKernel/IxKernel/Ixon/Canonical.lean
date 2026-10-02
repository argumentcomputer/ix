module
public import IxKernel.Ixon.Bounded.Constant
public import IxKernel.Ixon.WireCheck

public section

namespace Ixon.Canonical

/-- Decode one canonical Ixon v4 constant, under explicit input-byte and aggregate
universe-expansion limits. Successful values satisfy the production wire
invariant and re-encode to exactly the supplied bytes. Mutual-block member
ordering is a separate semantic contract. -/
def deConstant (maxBytes maxUnivNodes : Nat) (bytes : ByteArray) : Except String Constant := do
  let constant ← Bounded.deConstant maxBytes maxUnivNodes bytes
  if WireCheck.validConstant constant then
    if serConstant constant = bytes then
      return constant
    else
      throw "getConstantCanonical: noncanonical wire encoding"
  else
    throw "getConstantCanonical: value outside the wire domain"

end Ixon.Canonical
