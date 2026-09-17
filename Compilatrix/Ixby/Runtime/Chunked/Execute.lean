import Compilatrix.Ixby.Runtime.Chunked.Representation

/-! Resumable execution using immutable chunks for internal byte builders.
Program and input admission still run through the pinned reference validator. -/

namespace Compilatrix.Ixby.Runtime.Chunked

open Ix.Ixby (Limits Program Error)

def initialState (limits : Limits) (program : Program) (input : Array Ix.Ixby.Value) :
    Except Error State :=
  (Ix.Ixby.initialState limits program input).map State.ofReference

def run (limits : Limits) (program : Program) : Nat → State → Except Error Value
  | 0, _ => .error .outOfFuel
  | fuel + 1, state =>
    match step limits program state with
    | .error error => .error error
    | .ok (.halted value) => .ok value
    | .ok (.next next) => run limits program fuel next

def execute (limits : Limits) (program : Program) (input : Array Ix.Ixby.Value)
    (fuel : Nat) : Except Error Ix.Ixby.Value := do
  let state ← initialState limits program input
  (run limits program fuel state).map Value.toReference

def runChunk (limits : Limits) (program : Program) :
    Nat → State → Nat → Except Error (Sum Value State × Nat)
  | 0, state, count => .ok (.inr state, count)
  | fuel + 1, state, count => do
    match ← step limits program state with
    | .halted value => return (.inl value, count + 1)
    | .next state => runChunk limits program fuel state (count + 1)

def chunkToReference : Sum Value State × Nat → Sum Ix.Ixby.Value Ix.Ixby.State × Nat
  | (.inl value, count) => (.inl value.toReference, count)
  | (.inr state, count) => (.inr state.toReference, count)

end Compilatrix.Ixby.Runtime.Chunked
