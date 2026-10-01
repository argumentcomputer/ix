import Ix.Compile.SourceContract.Elab

/-!
OS08 `bounds-proof-array` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `OS08BoundsArray`. Written for Compilatr.ix (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def getE (xs : Array Nat) (i : Nat) (0 h : i < xs.size) : Nat := xs[i]'h
