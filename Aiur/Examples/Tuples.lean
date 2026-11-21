import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur

def tupleProgram : Program Nat := aiur% "
fn swap(p: (Field, Field)) -> (Field, Field) {
  match p { (x, y) => (y, x) }
}

fn step(p: (Field, (Field, Field))) -> (Field, (Field, Field), ()) {
  let (tag, (x, y)) = p;
  match (tag, x) {
    (0, _) => (tag, swap((x, y)), ()),
    (_, 0) => (tag, (y, y), ()),
    _ => (tag, (x + y, x * y), ()),
  }
}
"

#eval eval (tupleProgram.toField Rat) "step" [.tuple [0, .tuple [2, 3]]]
-- .ok (.tuple [0, .tuple [3, 2], .tuple []])

example : EvalCall (tupleProgram.toField Rat) "step" [.tuple [0, .tuple [2, 3]]]
    (.tuple [0, .tuple [3, 2], .tuple []]) :=
  eval_spec (hints := HintProvider.unavailable) (fuel := 20) (by decide +kernel)

#eval (Circuit.compile (tupleProgram.toField Rat)).isOk
-- true
