import Ix.Compile.SourceContract.Elab

/-!
OS28 `borrow-accumulate` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `OS28BorrowAccumulate`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def lenL (~ v : List Nat) : Nat := v.length

def countAll (xs : List Nat) (! acc : Nat) : Nat :=
  let borrow (~ v : List Nat) := xs
  acc + lenL v
