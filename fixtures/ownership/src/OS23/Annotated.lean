import Ix.Compile.SourceContract.Elab

/-!
OS23 `local-escape` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P17LocalEscape`. Written for Compilatr.ix (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def esc (~ x : Nat) : Nat := x
