/-! MEAS-4 `lean-clang` row: the K1 definitions of `fib`, `sum-loop` and
`gcd`, verbatim from `benchmarks/fixtures/{fib,sum-loop,gcd}` (and so from
`fixtures/ixon-v4/k1/K1.lean`), exported to the C timing driver in place of
the fixtures' `entry` and `main`. -/

namespace K1

/-- Structural recursion with a `match` on 0 / 1 / n+2. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- An idiomatic `for` loop over a range (`Std.Legacy.Range`). -/
def sumLoop (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + i
  return s

/-- Well-founded recursion with a `Nat` measure. -/
def gcd (a b : Nat) : Nat :=
  if h : b = 0 then a else gcd b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

end K1

@[export meas4_fib] def meas4Fib (n : Nat) : Nat := K1.fib n

@[export meas4_sum_loop] def meas4SumLoop (n : Nat) : Nat := K1.sumLoop n

@[export meas4_gcd] def meas4Gcd (a b : Nat) : Nat := K1.gcd a b
