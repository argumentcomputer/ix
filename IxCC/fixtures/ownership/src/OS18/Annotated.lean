import Ix.Compile.SourceContract.Elab

/-!
OS18 `unique-dup` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P37UniqueDup`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def dupU (! xs : List Nat) : List Nat × List Nat := (xs, xs)
