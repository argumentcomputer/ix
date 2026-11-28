import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
N04 `freeze-then-unique` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `N04FreezeThenUnique`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def take (@unique xs : List Nat) : @unique List Nat := xs

def freezeThenTake (@unique xs : List Nat) : @unique List Nat :=
  let n := xs.length
  if n == 0 then take xs else take xs
