import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
OS23 `local-escape` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P17LocalEscape`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def esc (@borrowed x : Nat) : Nat := x
