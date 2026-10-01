import Ix.Compile.SourceContract.Elab

/-!
OS24 `local-to-library` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P09LocalLib`. Written for Compilatr.ix (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def len (~ xs : List Nat) : Nat := xs.length
