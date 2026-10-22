import Aiur.Generic
import Mathlib.Algebra.Field.Rat

open Aiur

def alternatives : Generic.Program Nat := aiur% "
enum Pair { Forward(Field, Field), Reversed(Field, Field) }

fn sum(value: Pair) -> Field {
  let Pair::Forward(x, y) | Pair::Reversed(y, x) = value;
  let 0 | 1 = x;
  x + y
}

fn main() -> Field { sum(Pair::Reversed(7, 1)) }
"

#eval do
  let source ← Generic.prepare (alternatives.toField Rat)
  source.run "main" []
