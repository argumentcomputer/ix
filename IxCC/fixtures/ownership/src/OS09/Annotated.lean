import Ix.Compile.SourceContract.Elab

/-!
OS09 `linear-add` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P14Linear`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def lin (1 x : Nat) (1 y : Nat) : Nat := x + y
