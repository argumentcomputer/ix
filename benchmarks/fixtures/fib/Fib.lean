/-! K1 `fib`. The definition is verbatim from `IxCCTests/Fixtures/K1.lean`
(IxCC `2e4740d`); `entry` and `main` are the benchmark wrapper. -/

namespace K1

/-- Structural recursion with a `match` on 0 / 1 / n+2. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

end K1

/-- The pure benchmark entry: the value `main` prints. -/
def entry (n : Nat) : Nat := K1.fib n

def main : List String → IO UInt32
  | [n] => do IO.println (toString (entry n.toNat!)); pure 0
  | _ => do IO.eprintln "usage: fib N"; pure 1
