import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def enums : Program Nat := aiur% r#"
enum List { Nil, Cons(Field, &List) }
enum Item { Empty, Scalar(Field), Pair(Field, Field) }

fn sum(xs: List) -> Field {
  match xs {
    List::Nil => 0,
    List::Cons(x, tail) => x + sum(*tail),
  }
}

fn inspect(item: Item) -> Field {
  let value = match item {
    Item::Empty => 0,
    Item::Scalar(0) => 1,
    Item::Scalar(x) => x,
    Item::Pair(x, y) => x + y,
  };
  value + 1
}

fn main(x: Field, y: Field) -> Field {
  let rest = List::Cons(y, &List::Nil);
  inspect(Item::Scalar(sum(List::Cons(x, &rest))))
}
"#

#eval eval (enums.toField Rat) "main" [7, 8]
#eval run (enums.toField Rat) "main" [7, 8]

example : eval (enums.toField Rat) "main" [7, 8] 64 = .ok 16 := by decide +kernel

example : EvalCall (enums.toField Rat) "main" [7, 8] 16 :=
  eval_spec (hints := HintProvider.unavailable) (fuel := 64) (by decide +kernel)

#eval (Circuit.compile (enums.toField Rat)).isOk
-- true

#eval (Value.construct "List" "Nil" [] : Value Rat).encode enums.enums
-- some { type := .enum "List", words := [0, 0, 0] }
