/-! K1 `ackermann`. The definition is verbatim from `IxCCTests/Fixtures/K1.lean`
(in this repository); `entry` and `main` are the benchmark wrapper. -/

namespace K1

/-- Well-founded recursion with a lexicographic measure. -/
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

end K1

/-- The pure benchmark entry: the value `main` prints. -/
def entry (m n : Nat) : Nat := K1.ack m n

def main : List String → IO UInt32
  | [m, n] => do IO.println (toString (entry m.toNat! n.toNat!)); pure 0
  | _ => do IO.eprintln "usage: ackermann M N"; pure 1
