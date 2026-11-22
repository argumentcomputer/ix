import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
N05 `local-escape-list` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `N05LocalEscapeList`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def escList (@borrowed xs : List Nat) : List Nat := xs
