import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
N03 `unique-twice` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `N03UniqueTwice`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def take (@unique xs : List Nat) : @unique List Nat := xs

def twice (@unique xs : List Nat) : List Nat × List Nat := (take xs, take xs)
