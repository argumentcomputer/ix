import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
N06 `local-into-ctor` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `N06LocalIntoCtor`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def wrap (@borrowed xs : List Nat) : List (List Nat) := [xs]
