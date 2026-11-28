/-
Lean port of CakeML `compiler/benchmarks/cakeml_benchmarks/cakeml/foldl.cml`
(CakeML/cakeml 530c7deec135ad421cce7ca768eed2f5801261b2). BSD-3-Clause; see
`benchmarks/fixtures/LICENSES/cakeml-LICENSE`.
Modified for IxCC: translated from CakeML to Lean, with the size as
an argument (upstream: 40000) and a printed result in place of the unused
`val test`; see `VARIANT.md`.
-/

namespace Foldl

def foldl (f : β → α → β) : β → List α → β
  | e, [] => e
  | e, x :: xs => foldl f (f e x) xs

def «repeat» (x : α) : Nat → List α
  | 0 => []
  | n + 1 => x :: «repeat» x n

def test (n : Nat) : Nat :=
  foldl (fun x y => x + foldl (fun x y => x + y) 0 y) 0 («repeat» («repeat» 1 n) n)

end Foldl

/-- The pure benchmark entry: the value `main` prints. -/
def entry (n : Nat) : Nat := Foldl.test n

def main : List String → IO UInt32
  | [n] => do IO.println (toString (entry n.toNat!)); pure 0
  | _ => do IO.eprintln "usage: foldl N"; pure 1
