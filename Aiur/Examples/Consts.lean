import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur

def constSource : Generic.Program Nat := aiur% "
const zero = 0;
const cell = &(zero,);
const again = cell;

fn classify(p: &(Field,)) -> Field {
  match p {
    ::cell => 1,
    _ => 0,
  }
}

fn main(zero: Field) -> Field {
  // A local wins over a global in value position.
  let saved = zero;
  // `again` allocates here; `::cell` below loads and checks its contents.
  let p = again;
  let ::cell = p;
  saved + ::zero + classify(p)
}
"

-- Const declarations and references remain through source evaluation.
#guard constSource.consts.length == 3

#eval do
  let source ← Generic.prepare (constSource.toField Rat)
  source.run "main" [.field 10]
-- .ok (.field 11, [.tuple [.field 0]])

#eval do
  let source ← Generic.prepare (constSource.toField Rat)
  let specialized ← Generic.specialize source ["main"]
  specialized.run "main" [.field 10]

#eval do
  let source ← Generic.prepare (constSource.toField Rat)
  let specialized ← Generic.specialize source ["main"]
  return (← specialized.compile).system.chips.length
-- .ok 2: main and classify
