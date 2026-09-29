/-! K1 `sum-loop`. The definition is verbatim from `fixtures/ixon-v3/k1/K1.lean`
(Compilatr.ix `2e4740d`); `entry` and `main` are the benchmark wrapper. -/

namespace K1

/-- An idiomatic `for` loop over a range (`Std.Legacy.Range`). -/
def sumLoop (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + i
  return s

end K1

/-- The pure benchmark entry: the value `main` prints. -/
def entry (n : Nat) : Nat := K1.sumLoop n

def main : List String → IO UInt32
  | [n] => do IO.println (toString (entry n.toNat!)); pure 0
  | _ => do IO.eprintln "usage: sum-loop N"; pure 1
