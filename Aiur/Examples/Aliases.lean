import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur

def aliasedSource : Generic.Program Nat := aiur% "
type Scalar = Field;
type Pair<T> = (T, T);
type Maybe<T> = Option<T>;
enum Option<T> { None, Some(T) }

fn duplicate<T>(x: T) -> Pair<T> { (x, x) }
fn main(x: Scalar) -> Scalar {
  match Maybe::Some(duplicate(x)) {
    Maybe::Some(pair) => pair.0,
    Maybe::None => 0,
  }
}
"

-- Alias declarations remain in the source; literals still use Nat.
#guard aliasedSource.aliases.length == 3

#eval do
  let source ← Generic.prepare (aliasedSource.toField Rat)
  source.run "main" [.field 42]

#eval do
  let source ← Generic.prepare (aliasedSource.toField Rat)
  let specialized ← Generic.specialize source ["main"]
  specialized.run "main" [.field 42]

#eval do
  let source ← Generic.prepare (aliasedSource.toField Rat)
  let specialized ← Generic.specialize source ["main"]
  let circuit ← specialized.compile
  return circuit.system.chips.length
