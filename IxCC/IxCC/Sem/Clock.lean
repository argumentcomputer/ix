import IxCC.Sem.Result

/-!
# A clocked small-step runner

The run loop that clocked small-step semantics share (Xv and Xl): a
step either continues, possibly spending one unit of clock, or ends. A
charge with an empty clock is `timeout`. The runner also takes a step bound
(`fuel`) so that it is structural; each semantics chooses a bound that the
clock always exhausts first (see `Lir.Semantics`).

Lir keeps its own copy of this loop (`Lir.run`), with the same charging
discipline; levels that share labels and calls therefore charge the same
events, and their clocks agree step for step.
-/

namespace IxCC.Sem

/-- One step of a clocked semantics with states `σ` and final values `α`. -/
inductive Step (σ α : Type) where
  /-- `charge`: this step spends one unit of clock. -/
  | next (s : σ) (charge : Bool)
  | done (value : α)
  | fail (r : Resource)
  | trap
  | stuck

/-- Iterate `step` with at most `fuel` steps and clock `k`. -/
def runClocked {σ α : Type} (step : σ → Step σ α) : (fuel k : Nat) → σ → Result α
  | 0, _, _ => .timeout
  | fuel + 1, k, s =>
      match step s with
      | .next s' false => runClocked step fuel k s'
      | .next s' true =>
          match k with
          | 0 => .timeout
          | k + 1 => runClocked step fuel k s'
      | .done value => .ok value
      | .fail r => .resource r
      | .trap => .trap
      | .stuck => .stuck

end IxCC.Sem
