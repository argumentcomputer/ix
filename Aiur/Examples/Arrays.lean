import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur

def arrays : Generic.Program Nat := aiur% "
type Block = [Field; 4];
const zeros = [0; 4];
const cell = &[0];

fn duplicate<T>(x: T) -> [T; 2] { [x; 2] }
fn middle(a: Block) -> [Field; 2] { a[1..3] }
fn main(x: Field) -> [Field; 2] {
  let [a, b] = middle([0, x, 7, 0]);
  let ::zeros = [0, 0, 0, 0];
  let ::cell = cell;
  let copied = duplicate(a);
  [copied[0] + b, copied[1]]
}
"

#eval do
  let source ← Generic.prepare (arrays.toField Rat)
  source.run "main" [5]

#eval do
  let source ← Generic.prepare (arrays.toField Rat)
  let program ← Generic.specialize source ["main"]
  program.run "main" [5]

#eval do
  let source ← Generic.prepare (arrays.toField Rat)
  let program ← Generic.specialize source ["main"]
  return (← program.compile).system.chips.length
