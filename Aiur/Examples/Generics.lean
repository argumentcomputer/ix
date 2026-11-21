import Aiur
import Mathlib.Algebra.Field.Rat

open Aiur

def genericSource : Generic.Program Nat := aiur% "
enum Option<T> { None, Some(T) }

fn identity<T>(x: T) -> T { x }

fn unwrap_or<T>(value: Option<T>, fallback: T) -> T {
  match value { Option::Some(x) => x, Option::None => fallback }
}

fn main(x: Field) -> Field {
  let pair = identity((x, 2));
  unwrap_or(Option::Some(pair.0), 0)
}
"

-- The interpreter calls generic bodies directly, with concrete type arguments.
#eval do
  let source ← Generic.prepare (genericSource.toField Rat)
  source.run "main" [.field 42]
-- Except.ok (Aiur.Value.field 42, [])

-- Entrypoints belong to this invocation, rather than the source syntax.
#eval do
  let source ← Generic.prepare (genericSource.toField Rat)
  let specialized ← Generic.specialize source ["main"]
  specialized.run "main" [.field 42]
-- Except.ok (Aiur.Value.field 42, [])

#eval do
  let source ← Generic.prepare (genericSource.toField Rat)
  let specialized ← Generic.specialize source ["main"]
  let circuit ← specialized.compile
  return circuit.system.chips.length
-- Except.ok 3

-- The theorem works for arbitrary inputs, outputs, recursion and hint values.
example [Field F] [DecidableEq F] (source : Generic.Source F)
    (specialized : Generic.Specialized source ["main"]) :
    source.EvalCall "main" args output ↔ specialized.EvalCall "main" args output :=
  specialized.evalCall_iff (by simp)
