import Ix.Compile.SourceContract.Elab

/-!
N04 `freeze-then-unique` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `N04FreezeThenUnique`. Written for Compilatr.ix (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def take (! xs : List Nat) : ! List Nat := xs

def freezeThenTake (! xs : List Nat) : ! List Nat :=
  let n := xs.length
  if n == 0 then take xs else take xs
