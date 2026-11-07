import Ix.Compile.SourceContract.Elab

/-!
N07 `linear-into-two-branches` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `N07LinearIntoTwoBranches`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def pickOne (b : Bool) (1 x : Nat) : Nat := if b then x else 0
