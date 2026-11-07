/-! MT.2 `sfib` benchmark: Koka's `sfib-int.kk` loop, verbatim from
`fixtures/corpus/phase1-scalar/src/Scalar.lean` (IxCC); `entry` and
`main` are the benchmark wrapper. -/

namespace Scalar

/-- Koka `sfib-int.kk`: a tail loop on `x² + x + 2`, restarted above `10⁹`,
so every value stays below `2⁶³`. -/
def sfibGo : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => if x > 1000000000 then sfibGo n 1 else sfibGo n (x * x + x + 2)

def sfib (n : Nat) : Nat := sfibGo n 1

end Scalar

/-- The pure benchmark entry: the value `main` prints. -/
def entry (n : Nat) : Nat := Scalar.sfib n

def main : List String → IO UInt32
  | [n] => do IO.println (toString (entry n.toNat!)); pure 0
  | _ => do IO.eprintln "usage: sfib N"; pure 1
