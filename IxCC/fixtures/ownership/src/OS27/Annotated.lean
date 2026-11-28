import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
OS27 `borrow-return` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P29SharedLoan`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def sharedLoan (@unique owner : Nat) : Nat :=
  let @borrow view : Nat := owner
  view

def entry (n : Nat) : Nat := sharedLoan n
