import Ix.Compile.SourceContract.Elab

/-!
OS21 `fresh-unique-result` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P35FreshResult`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def single (x : Nat) : ! List Nat := [x]

def idT {0 α : Type} (x : α) : α := x

def entry (n : Nat) : Nat := idT n + (single n).length
