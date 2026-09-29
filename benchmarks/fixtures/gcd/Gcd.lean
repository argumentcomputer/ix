/-! K1 `gcd`. The definition is verbatim from `fixtures/ixon-v3/k1/K1.lean`
(Compilatr.ix `2e4740d`); `entry` and `main` are the benchmark wrapper. -/

namespace K1

/-- Well-founded recursion with a `Nat` measure. -/
def gcd (a b : Nat) : Nat :=
  if h : b = 0 then a else gcd b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

end K1

/-- The pure benchmark entry: the value `main` prints. -/
def entry (a b : Nat) : Nat := K1.gcd a b

def main : List String → IO UInt32
  | [a, b] => do IO.println (toString (entry a.toNat! b.toNat!)); pure 0
  | _ => do IO.eprintln "usage: gcd A B"; pure 1
