import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
OS09 `linear-add` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P14Linear`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def lin (@once x : Nat) (@once y : Nat) : Nat := x + y
