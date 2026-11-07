import Ix.Compile.SourceContract.Elab

/-!
OS11 `linear-unused` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P14cLinearUnused`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def unused (1 x : Nat) : Nat := 0
