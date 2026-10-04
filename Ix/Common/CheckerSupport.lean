/-
  Optional source-environment support for certified checking of selected
  compilation closures. This is an input-selection policy, not a compiler
  rewrite edge or a change to the certified kernel's trust boundary.
-/
module
public import Lean.Environment

public section

namespace Lean

/-- Ground operations needed to install the pinned Nat recurrence certificate.
Some are absent from the operation's ordinary declaration dependency cone:
notably `Nat.land` needs `Nat.mul`. Keep this untrusted selection table aligned
with `Ix/Kernel/CoreDefs.lean`'s `natOpDeps`, without importing the certified
kernel into compiler code. The checker still validates every supplied record
and all its frozen pins; this table confers no acceptance authority.

Self edges are intentional. Transitive closure must use a visited set, and must
also traverse the ordinary declaration dependencies of each support name. -/
def checkerSupportNames (n : Name) : List Name :=
  if n == ``Nat.pred then [``Nat.pred]
  else if n == ``Nat.add then [``Nat.add]
  else if n == ``Nat.sub then [``Nat.pred, ``Nat.sub]
  else if n == ``Nat.mul then [``Nat.add, ``Nat.mul]
  else if n == ``Nat.pow then [``Nat.add, ``Nat.mul, ``Nat.pow]
  else if n == ``Nat.beq then [``Nat.beq]
  else if n == ``Nat.ble then [``Nat.ble]
  else if n == ``Nat.div then [``Nat.pred, ``Nat.sub, ``Nat.ble, ``Nat.div]
  else if n == ``Nat.mod then [``Nat.pred, ``Nat.sub, ``Nat.ble, ``Nat.mod]
  else if n == ``Nat.gcd then [``Nat.ble, ``Nat.mod, ``Nat.gcd]
  else if n == ``Nat.land then
    [``Nat.add, ``Nat.mul, ``Nat.ble, ``Nat.div, ``Nat.mod, ``Nat.land]
  else if n == ``Nat.lor then
    [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.ble, ``Nat.div, ``Nat.mod, ``Nat.lor]
  else if n == ``Nat.xor then
    [``Nat.add, ``Nat.mul, ``Nat.ble, ``Nat.div, ``Nat.mod, ``Nat.xor]
  else if n == ``Nat.shiftLeft then
    [``Nat.sub, ``Nat.mul, ``Nat.ble, ``Nat.shiftLeft]
  else if n == ``Nat.shiftRight then
    [``Nat.sub, ``Nat.ble, ``Nat.div, ``Nat.shiftRight]
  else []

/-- Existing source records only. A missing or modified support record remains
a checker decline/rejection; selection never synthesizes trusted constants. -/
def checkerSupportOf (consts : ConstMap) (n : Name) : List Name :=
  (checkerSupportNames n).filter consts.contains

end Lean

end
