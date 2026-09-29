/-
Lean port of CakeML `compiler/benchmarks/cakeml_benchmarks/cakeml/reverse.cml`
(CakeML/cakeml 530c7deec135ad421cce7ca768eed2f5801261b2). BSD-3-Clause; see
`benchmarks/fixtures/LICENSES/cakeml-LICENSE`.
Modified for Compilatr.ix: translated from CakeML to Lean, with a printed
length and checksum in place of the unused `val test`; see `VARIANT.md`.
-/

namespace Reverse

/-- Naive reverse; `append` and `rev` are local functions, as in CakeML. -/
def reverse (xs : List α) : List α :=
  rev xs
where
  append : List α → List α → List α
    | [], ys => ys
    | x :: xs, ys => x :: append xs ys
  rev : List α → List α
    | [] => []
    | x :: xs => append (rev xs) [x]

def mkList : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: mkList n

/-- Order-sensitive checksum of the result (not part of the CakeML program). -/
def checksum : Nat → List Nat → Nat
  | h, [] => h
  | h, x :: xs => checksum ((h * 31 + x) % 1000000007) xs

end Reverse

/-- The pure benchmark entry: the length and checksum `main` prints. -/
def entry (n : Nat) : Nat × Nat :=
  let r := Reverse.reverse (Reverse.mkList n)
  (r.length, Reverse.checksum 0 r)

def main : List String → IO UInt32
  | [n] => do
    let (len, sum) := entry n.toNat!
    IO.println s!"{len} {sum}"
    pure 0
  | _ => do IO.eprintln "usage: reverse N"; pure 1
