import Ix.Compile.SourceContract.Elab

/-!
OS10 `linear-dup` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P14bLinearDup`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def twice (1 x : Nat) : Nat := x + x
