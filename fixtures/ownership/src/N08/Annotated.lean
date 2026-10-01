import Ix.Compile.SourceContract.Elab

/-!
N08 `erased-used` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `N08ErasedUsed`. Written for Compilatr.ix (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def useErased (0 n : Nat) : Nat := n + 1
