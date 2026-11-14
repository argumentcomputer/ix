module
public import IxC.Ixon.Bounded.Constant
public import IxC.Ixon.WireCheck

public section

namespace Ixon.Canonical

/-- Decode one canonical Ixon v5 constant, under explicit input-byte and aggregate
universe-expansion limits. Successful values satisfy the production wire
invariant, re-encode to exactly the supplied bytes, and carry their level count
(below `Ixon.maxLevelCount`) and binder data in canonical form
(`Constant.bindersCanonical`), and no theorem with assertions
(`Constant.modesCanonical`). Mutual-block member ordering is a separate
semantic contract. -/
def deConstant (maxBytes maxUnivNodes : Nat) (bytes : ByteArray) : Except String Constant := do
  let constant ← Bounded.deConstant maxBytes maxUnivNodes bytes
  if WireCheck.validConstant constant then
    if serConstant constant = bytes then
      if constant.bindersCanonical then
        if constant.modesCanonical then
          return constant
        else
          throw "getConstantCanonical: a theorem with assertions"
      else
        throw "getConstantCanonical: level count or binder data not in canonical form"
    else
      throw "getConstantCanonical: noncanonical wire encoding"
  else
    throw "getConstantCanonical: value outside the wire domain"

end Ixon.Canonical
