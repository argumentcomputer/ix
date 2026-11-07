import Ix.Compile.SourceContract.Elab

/-!
OS07 `erased-proof-recursive` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P23Countdown`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def countdown (n : Nat) (0 h : 0 ≤ n) : Nat :=
  match n with
  | 0 => 0
  | k+1 => countdown k (Nat.zero_le k) + 1

def entry (n : Nat) : Nat := countdown n (Nat.zero_le n)
