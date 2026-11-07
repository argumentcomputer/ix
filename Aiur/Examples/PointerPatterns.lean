import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur

def pointerPatterns : Generic.Program Nat := aiur% "
enum List<T> { Nil, Cons(T, &List<T>) }

fn read<T>(&value: &T) -> T { value }

fn sum(xs: &List<Field>) -> Field {
  match xs {
    &List::Nil => 0,
    &List::Cons(head, tail) => head + sum(tail),
  }
}

fn main(x: Field) -> Field {
  let &a = &x;
  let (&b, c) = (&(a + 1), 2);
  sum(&List::Cons(read(&b), &List::Cons(c, &List::Nil)))
}
"

#eval do
  let source ← Generic.prepare (pointerPatterns.toField Rat)
  return (← source.run "main" [.field 10]).1
-- .ok (.field 13)

#eval do
  let source ← Generic.prepare (pointerPatterns.toField Rat)
  let specialized ← Generic.specialize source ["main"]
  return (← specialized.run "main" [.field 10]).1
-- .ok (.field 13)

#eval do
  let source ← Generic.prepare (pointerPatterns.toField Rat)
  let specialized ← Generic.specialize source ["main"]
  let circuit ← specialized.compile
  return circuit.system.chips.length
-- .ok 3: main, read<Field>, and sum
