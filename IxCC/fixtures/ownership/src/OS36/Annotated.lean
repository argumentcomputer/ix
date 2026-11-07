import Ix.Compile.SourceContract.Elab

/-!
OS36 `array-bump-in-place` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `OS36ArrayBump`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def bump (! a : Array Nat) (i : Nat) : ! Array Nat := a.modify i (· + 1)
