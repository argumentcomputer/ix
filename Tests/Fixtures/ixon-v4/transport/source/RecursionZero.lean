import Ix.Compile.SourceContract.Elab

def count (n : Nat) (0 unused : Nat) : Nat :=
  match n with
  | 0 => 0
  | Nat.succ k => count k 0

def entry (n : Nat) : Nat := count n 0
