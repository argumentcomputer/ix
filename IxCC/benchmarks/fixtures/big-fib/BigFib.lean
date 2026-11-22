/-! K5 `big-fib`: fast-doubling arbitrary-precision Fibonacci `F(n)` over Lean's
exact `Nat`, returning a compact non-modular fingerprint (exact bit length, top
32 bits, and remainder mod `10^9 + 7`). -/

namespace BigFibBench

def bitLen (v : Nat) : Nat :=
  if v == 0 then 0
  else
    let rec findHi : Nat → Nat → Nat
      | 0, hi => hi
      | fuel + 1, hi => if (v >>> hi) == 0 then hi else findHi fuel (hi * 2)
    let hi := findHi 32 1
    let rec bsearch : Nat → Nat → Nat → Nat
      | 0, lo, _ => lo + 1
      | fuel + 1, lo, hi =>
        if lo + 1 ≥ hi then lo + 1
        else
          let mid := (lo + hi) / 2
          if (v >>> mid) == 0 then bsearch fuel lo mid
          else bsearch fuel mid hi
    bsearch 32 (hi / 2) hi

def bignumDigest (v : Nat) : Nat :=
  let bl := bitLen v
  let top := if bl > 32 then v >>> (bl - 32) else v
  let rem := v % 1000000007
  bl * 1000000007 + ((rem * 31 + top) % 1000000007)

/-- Fast-doubling Fibonacci returning `(F(n), F(n+1))`. Exact for all `n < 2^64`. -/
def fibPairAux : Nat → Nat → Nat × Nat
  | 0, _ => (0, 1)
  | fuel + 1, n =>
    if n == 0 then (0, 1)
    else
      let (a, b) := fibPairAux fuel (n / 2)
      let c := a * (2 * b - a)
      let d := a * a + b * b
      if n % 2 == 0 then (c, d) else (d, c + d)

def fastFib (n : Nat) : Nat := (fibPairAux 64 n).1

end BigFibBench

/-- The pure benchmark entry: compact fingerprint of `F(n)`. -/
def entry (n : Nat) : Nat := BigFibBench.bignumDigest (BigFibBench.fastFib n)

def main : List String → IO UInt32
  | [n] => do IO.println (toString (entry n.toNat!)); pure 0
  | _ => do IO.eprintln "usage: big-fib N"; pure 1
