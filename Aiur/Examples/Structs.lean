import Aiur.Generic
import Mathlib.Algebra.Field.Rat

open Aiur

def structs : Generic.Program Nat := aiur% "
struct Point { x: Field, y: Field }
struct Box<T> { value: T }
const origin = Point { x: 0, y: 0 };

fn swap(Point { x, y }: Point) -> Point { Point { y: x, x: y } }
fn unwrap<T>(b: Box<T>) -> T { b.value }
fn main(x: Field, y: Field) -> Field {
  let p = unwrap(Box { value: swap(Point { x, y }) });
  let Point { x: first, .. } = p;
  first + origin.y
}
"

#eval do
  let s ← Generic.prepare (structs.toField Rat)
  s.run "main" [3, 7]
-- .ok (7, [])

#eval do
  let s ← Generic.prepare (structs.toField Rat)
  let specialized ← Generic.specialize s ["main"]
  let _ ← specialized.compile
  specialized.coreRun "main" [3, 7]
-- .ok (7, [])
