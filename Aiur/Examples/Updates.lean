import Aiur.Generic
import Mathlib.Algebra.Field.Rat

open Aiur

def updates : Generic.Program Nat := aiur% "
struct Point { x: Field, y: Field }
struct State { position: Point, samples: [Field; 3] }

fn advance(state: State, sample: Field) -> State {
  state with {
    .position.x = state.position.x + 1,
    .samples[2] = sample,
  }
}

fn main() -> (Field, [Field; 3]) {
  let initial = State { position: Point { x: 3, y: 4 }, samples: [0; 3] };
  let next = advance(initial, 9);
  (next.position.x, next.samples)
}
"

#eval do
  let s ← Generic.prepare (updates.toField Rat)
  s.run "main" []
-- .ok (.tuple [4, .tuple [0, 0, 9]], [])

#eval do
  let s ← Generic.prepare (updates.toField Rat)
  let specialized ← Generic.specialize s ["main"]
  let _ ← specialized.compile
  specialized.coreRun "main" []
-- .ok (.tuple [4, .tuple [0, 0, 9]], [])
