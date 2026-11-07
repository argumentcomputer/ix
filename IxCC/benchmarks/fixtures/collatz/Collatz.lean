/-! MT.2 `collatz` benchmark: the Collatz step count, verbatim from
`fixtures/corpus/phase1-scalar/src/Scalar.lean` (IxCC); `entry` sums
it over `[1, limit)` and `main` is the benchmark wrapper. -/

namespace Scalar

/-- Collatz steps to reach 1 (fuel bounds the loop; OEIS A006577 below
`10⁶` needs at most 524). -/
def collatzGo : Nat → Nat → Nat → Nat
  | 0, _, s => s
  | fuel + 1, n, s =>
    if n ≤ 1 then s else collatzGo fuel (if n % 2 == 0 then n / 2 else 3 * n + 1) (s + 1)

def collatz (n : Nat) : Nat := collatzGo 1000 n 0

end Scalar

/-- The pure benchmark entry: the total Collatz steps of `1 … limit - 1`. -/
def entry (limit : Nat) : Nat := Id.run do
  let mut s := 0
  for n in [1:limit] do
    s := s + Scalar.collatz n
  return s

def main : List String → IO UInt32
  | [n] => do IO.println (toString (entry n.toNat!)); pure 0
  | _ => do IO.eprintln "usage: collatz LIMIT"; pure 1
