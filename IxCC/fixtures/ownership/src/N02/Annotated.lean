import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
N02 `move-while-borrowed` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `N02MoveWhileBorrowed`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def lenL (@borrowed v : List Nat) : Nat := v.length

def moveDuringLoan (@unique owner : List Nat) : @unique List Nat :=
  let @borrow v : List Nat := owner
  let _n := lenL v
  owner
