import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
OS36 `array-bump-in-place` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `OS36ArrayBump`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def bump (@unique a : Array Nat) (i : Nat) : @unique Array Nat := a.modify i (· + 1)
