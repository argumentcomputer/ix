import Ix.Compile.SourceContract.Elab

/-!
OS15b `unique-reverse-both` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P03RevUniqueBoth`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def revAcc (! xs : List Nat) (! acc : List Nat) : ! List Nat :=
  match xs with
  | [] => acc
  | x :: rest => revAcc rest (x :: acc)
