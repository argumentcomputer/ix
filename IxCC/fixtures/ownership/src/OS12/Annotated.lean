import Ix.Compile.SourceContract.Elab

/-!
OS12 `affine-dup` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P36AffineDup`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def twiceA (& x : Nat) : Nat := x + x
