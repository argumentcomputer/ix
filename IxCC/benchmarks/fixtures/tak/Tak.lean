/-! K1 `tak`. The definition is verbatim from `IxCCTests/Fixtures/K1.lean`
(in this repository); `entry` and `main` are the benchmark wrapper. The
fuel is an explicit argument. For `tak x y z` with these arguments, fuel
`x - 1` is the least that gives Takeuchi's unbounded result, so the test and
bench arguments pass fuel `x`. -/

namespace K1

/-- Takeuchi's function, total through an explicit fuel argument. -/
def tak : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, z => z
  | f + 1, x, y, z =>
    if y < x then tak f (tak f (x - 1) y z) (tak f (y - 1) z x) (tak f (z - 1) x y) else z

end K1

/-- The pure benchmark entry: the value `main` prints. -/
def entry (fuel x y z : Nat) : Nat := K1.tak fuel x y z

def main : List String → IO UInt32
  | [f, x, y, z] => do IO.println (toString (entry f.toNat! x.toNat! y.toNat! z.toNat!)); pure 0
  | _ => do IO.eprintln "usage: tak FUEL X Y Z"; pure 1
