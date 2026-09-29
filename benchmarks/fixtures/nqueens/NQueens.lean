/-
Lean port of Koka `test/bench/koka/nqueens.kk`
(koka-lang/koka 8b803da69d3941ce1e03173578093aefc41ee548).
Copyright 2012-2023, Microsoft Research, Daan Leijen. Apache-2.0; see
`benchmarks/fixtures/LICENSES/koka-LICENSE`.
Modified for Compilatr.ix: translated from Koka to Lean, with `int32` queens
as `Nat` and solutions as `List`; see `VARIANT.md`.
-/

namespace NQueens

abbrev Solution := List Nat
abbrev Solutions := List (List Nat)

def safe (queen diag : Nat) : Solution → Bool
  | q :: qs => queen != q && queen != q + diag && queen != q - diag && safe queen (diag + 1) qs
  | [] => true

def appendSafe : Nat → Solution → Solutions → Solutions
  | 0, _, xss => xss
  | queen + 1, xs, xss =>
    if safe (queen + 1) 1 xs then appendSafe queen xs (((queen + 1) :: xs) :: xss)
    else appendSafe queen xs xss

def extend (queen : Nat) (acc : Solutions) : Solutions → Solutions
  | xs :: rest => extend queen (appendSafe queen xs acc) rest
  | [] => acc

def findSolutions (n : Nat) : Nat → Solutions
  | 0 => [[]]
  | queen + 1 => extend n [] (findSolutions n queen)

def queens (n : Nat) : Nat :=
  (findSolutions n n).length

end NQueens

/-- The pure benchmark entry: the value `main` prints. -/
def entry (n : Nat) : Nat := NQueens.queens n

def main : List String → IO UInt32
  | [n] => do IO.println (toString (entry n.toNat!)); pure 0
  | _ => do IO.eprintln "usage: nqueens N"; pure 1
