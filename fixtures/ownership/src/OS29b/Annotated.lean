import Ix.Compile.SourceContract.Elab

/-!
OS29b `unique-closure` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `OS29bUniqueClosure`. Written for Compilatr.ix (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def applyOnce (!1 k : Nat → Nat) (x : Nat) : Nat := k x

def useIt (n : Nat) : Nat := applyOnce (fun y => y + n) 3
