import Ix.Compile.SourceContract.Elab

/-!
OS06b `erased-proof-discriminant` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P25HeadProof`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def headOr (xs : List Nat) (0 h : xs ≠ []) : Nat :=
  match xs, h with
  | x :: _, _ => x

def entry (n : Nat) : Nat := headOr [n, n+1] (by simp)
