import Ix.Compile.SourceContract.Elab

/-!
OS27 `borrow-return` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P29SharedLoan`. Written for Compilatr.ix (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def sharedLoan (!1 owner : Nat) : Nat :=
  let borrow (~ view : Nat) := owner
  view

def entry (n : Nat) : Nat := sharedLoan n
