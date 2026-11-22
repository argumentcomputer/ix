import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
N01 `consume-borrowed` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `N01ConsumeBorrowed`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def take (@unique xs : List Nat) : @unique List Nat := xs

def consumeView (@unique owner : List Nat) : @unique List Nat :=
  let @borrow v : List Nat := owner
  take v
