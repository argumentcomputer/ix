import Ix.Compile.SourceContract.Elab

/-!
N06 `local-into-ctor` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `N06LocalIntoCtor`. Written for Compilatr.ix (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def wrap (~ xs : List Nat) : List (List Nat) := [xs]
