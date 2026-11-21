import Aiur.Modules
import Mathlib.Algebra.Field.Rat

open Aiur

def modular : Modules.Program Nat := aiur_modules% "
signature Accumulator {
    type State;
    const EMPTY: State;
    fn push(state: State, coefficient: Field) -> State;
    fn finish(state: State) -> Field;
}

module PairAccumulator: Accumulator {
    struct State { total: Field, count: Field }
    const EMPTY = State { total: 0, count: 0 };
    fn push(state: State, coefficient: Field) -> State {
        state with { .total = state.total + coefficient, .count = state.count + 1 }
    }
    fn finish(state: State) -> Field { state.total }
}

module Algorithm<A: Accumulator> {
    fn sum(a: Field, b: Field) -> Field {
        A::finish(A::push(A::push(A::EMPTY, a), b))
    }
}

module App = Algorithm::<PairAccumulator>;
"

#eval do
  let p ← Modules.prepare (modular.toField Rat) ["App::sum"]
  p.run "App::sum" [.field 7, .field 9]

-- Entrypoints belong to the host configuration. Both names select one instance.
#eval do
  let p ← Modules.prepare (modular.toField Rat)
    ["App::sum", "Algorithm::<PairAccumulator>::sum"]
  let c ← p.compile
  return c.specialized.program.functions.map (fun (f : Function Rat) => f.name)
