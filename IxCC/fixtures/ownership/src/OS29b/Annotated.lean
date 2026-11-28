import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
OS29b `unique-closure` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `OS29bUniqueClosure`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def applyOnce (@unique k : Nat → Nat) (x : Nat) : Nat := k x

def useIt (n : Nat) : Nat := applyOnce (fun y => y + n) 3
