import Ix.Compile.SourceContract.Elab

/-!
N01 `consume-borrowed` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `N01ConsumeBorrowed`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def take (! xs : List Nat) : ! List Nat := xs

def consumeView (! owner : List Nat) : ! List Nat :=
  let borrow (~ v : List Nat) := owner
  take v
