module
public import Ix.Ixon.Bounded.Universe

public section

namespace Ixon.Bounded

/-- Expanded universe constructors across an entire side table. -/
def univNodes (values : Array Univ) : Nat :=
  (values.toList.map Univ.nodeCount).sum

/-- Read the universe table with one shared expansion budget. The tail loop
appends each successfully checked universe without reserving the claimed
array size or restarting the budget between entries. -/
def getUnivArrayLoop : Nat → Nat → Array Univ → GetM (Array Univ × Nat)
  | 0, budget, values => pure (values, budget)
  | count + 1, budget, values => do
    let (value, remaining) ← getUniv budget
    getUnivArrayLoop count remaining (values.push value)

def getUnivArray (count budget : Nat) : GetM (Array Univ × Nat) :=
  getUnivArrayLoop count budget #[]

/-- The production record grammar with a shared budget for its final universe
table. Other fields use the same readers as the production decoder. -/
def getConstant (maxUnivNodes : Nat) : GetM Constant :=
  getConstantWithUnivs fun count => Prod.fst <$> getUnivArray count maxUnivNodes

/-- Decode one complete constant under input-byte and aggregate universe
expansion limits. These limits do not claim a bound on runtime heap bytes. -/
def deConstant (maxBytes maxUnivNodes : Nat) (bytes : ByteArray) : Except String Constant :=
  if bytes.size ≤ maxBytes then
    runGetExact (getConstant maxUnivNodes) bytes
  else
    .error "getConstantBounded: byte budget exhausted"

end Ixon.Bounded
