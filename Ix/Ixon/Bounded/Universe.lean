module
public import Ix.Ixon.Codec

public section

namespace Ixon

/-- Number of constructors after expanding compressed successor chains. -/
def Univ.nodeCount : Univ → Nat
  | .zero | .var _ => 1
  | .succ inner => inner.nodeCount + 1
  | .max left right | .imax left right => left.nodeCount + right.nodeCount + 1

namespace Bounded

/-- Constructors contributed by this tag, excluding recursive children. -/
def univTagCharge (tag : Tag2) : Nat :=
  if tag.flag == 0 && tag.size != 0 then tag.size.toNat else 1

/-- Universe payload decoding with a shared budget for expanded constructors.
The charge is reserved before reading children or constructing a successor
chain. Binary children consume the same budget sequentially. -/
def getUnivFromTag (recur : Nat → GetM (Univ × Nat))
    (budget : Nat) (tag : Tag2) : GetM (Univ × Nat) := do
  let charge := univTagCharge tag
  if charge ≤ budget then
    let remaining := budget - charge
    match tag.flag with
    | 0 =>
      if tag.size == 0 then
        return (.zero, remaining)
      else
        let (base, remaining) ← recur remaining
        return (base.addSucc tag.size.toNat, remaining)
    | 1 =>
      let (left, remaining) ← recur remaining
      let (right, remaining) ← recur remaining
      return (.max left right, remaining)
    | 2 =>
      let (left, remaining) ← recur remaining
      let (right, remaining) ← recur remaining
      return (.imax left right, remaining)
    | 3 => return (.var tag.size, remaining)
    | flag => throw s!"getUniv: invalid flag {flag}"
  else
    throw "getUnivBounded: expanded-node budget exhausted"

/-- Recursion fuel bounds encoded nesting; `budget` bounds expansion.
On success the second component is the unspent constructor budget. -/
def getUnivFuel : Nat → Nat → GetM (Univ × Nat)
  | 0, _ => throw "getUniv: recursion budget exhausted"
  | fuel + 1, budget => getTag2 >>= getUnivFromTag (getUnivFuel fuel) budget

def getUniv (budget : Nat) : GetM (Univ × Nat) := do
  let state ← get
  getUnivFuel (state.bytes.size - state.idx + 1) budget

/-- Decode exactly one universe under explicit byte and expanded-node limits.
The production unbounded decoder remains available for existing callers. -/
def deUniv (maxBytes maxNodes : Nat) (bytes : ByteArray) : Except String Univ :=
  if bytes.size ≤ maxBytes then
    runGetExact (Prod.fst <$> getUniv maxNodes) bytes
  else
    .error "getUnivBounded: byte budget exhausted"

end Bounded
end Ixon
