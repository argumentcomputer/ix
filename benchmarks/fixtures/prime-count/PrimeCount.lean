/-! MT.2 `prime-count` benchmark: `π(n)` by trial division, verbatim from
`fixtures/corpus/phase1-scalar/src/Scalar.lean` (Compilatr.ix); `entry` and
`main` are the benchmark wrapper. -/

namespace Scalar

/-- Trial division by `d` while `d² ≤ n` (fuel `n`). -/
def primeGo (n : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, d => if d * d > n then true else if n % d == 0 then false else primeGo n fuel (d + 1)

def isPrime (n : Nat) : Bool := n ≥ 2 && primeGo n n 2

/-- `π(n)`, the primes up to `n`, by trial division. -/
def primeCount (n : Nat) : Nat := Id.run do
  let mut c := 0
  for i in [2:n + 1] do
    if isPrime i then c := c + 1
  return c

end Scalar

/-- The pure benchmark entry: the value `main` prints. -/
def entry (n : Nat) : Nat := Scalar.primeCount n

def main : List String → IO UInt32
  | [n] => do IO.println (toString (entry n.toNat!)); pure 0
  | _ => do IO.eprintln "usage: prime-count N"; pure 1
