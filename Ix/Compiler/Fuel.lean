namespace Ix.Compiler

/-!
# Fuel-order proof utilities

Evaluator-specific proofs establish stability across one successor step.  This
module contains the single order traversal that lifts such a step theorem
across an arbitrary fuel increase.
-/

/-- A result preserved by every successor step is preserved by any increase in
fuel. -/
theorem fuel_mono_of_succ {α : Sort u} {run : Nat → α} {result : α}
    {fuel larger : Nat}
    (hsucc : ∀ current, run current = result → run (current + 1) = result)
    (hle : fuel ≤ larger) (hrun : run fuel = result) :
    run larger = result := by
  induction hle with
  | refl => exact hrun
  | step _ ih => exact hsucc _ ih

end Ix.Compiler
