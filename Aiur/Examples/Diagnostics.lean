import Aiur.Generic
import Mathlib.Algebra.Field.Rat

open Aiur

def diagnostics : Generic.Program Nat := aiur% "
fn double(x: Field) -> Field {
  debug!(\"doubling\", x);
  x * 2
}
fn main() -> Field {
  let values: [Field; 2] = [3, 4];
  debug!(\"inputs\", values);
  assert_eq!(values, [3, 4], \"unexpected inputs\");
  (double(values[0]): Field)
}
"

#eval do
  let s ← Generic.prepare (diagnostics.toField Rat)
  return s.runTraced "main" []
