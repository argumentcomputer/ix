import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur

def pointerProgram : Program Nat := aiur% "
fn read(p: &(Field, &Field)) -> Field {
  let (x, q) = *p;
  x + *q
}
fn main(x: Field) -> Field {
  let p = &(x, &(x + 1));
  read(p)
}
"

#eval eval (pointerProgram.toField Rat) "main" [7]
-- .ok (.field 15)

#eval run (pointerProgram.toField Rat) "main" [7]
-- Also returns the two allocated cells. Source locations are 0 and 1.

example : EvalCall (pointerProgram.toField Rat) "main" [7] 15 :=
  eval_spec (hints := HintProvider.unavailable) (fuel := 20) (by decide +kernel)

#eval (Circuit.compile (pointerProgram.toField Rat)).isOk
-- true: both stores and loads produce guarded ROM requirements.
