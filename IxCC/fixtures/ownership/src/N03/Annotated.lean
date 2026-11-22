import Ix.Compile.SourceContract.Elab

/-!
N03 `unique-twice` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `N03UniqueTwice`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def take (! xs : List Nat) : ! List Nat := xs

def twice (! xs : List Nat) : List Nat × List Nat := (take xs, take xs)
