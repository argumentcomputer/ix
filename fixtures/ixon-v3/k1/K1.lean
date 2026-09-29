/-! First-rung (K1) scalar programs for Compilatr.ix, written as ordinary Lean. -/

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

/-- Well-founded recursion with a lexicographic measure. -/
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

/-- Takeuchi's function, total through an explicit fuel argument. -/
def tak : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, z => z
  | f + 1, x, y, z =>
    if y < x then tak f (tak f (x - 1) y z) (tak f (y - 1) z x) (tak f (z - 1) x y) else z

/-- Well-founded recursion with a `Nat` measure. -/
def gcd (a b : Nat) : Nat :=
  if h : b = 0 then a else gcd b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

end K1
