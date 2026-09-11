import Ix.Compiler.IxIR2.CallEval
import Ix.Compiler.IxIR2.Resources
import Ix.Compiler.IxIR2.CostSteps
import Ix.Compiler.IxIR2.EvalFuel

/-!
# Resources of executions with suspended credits

Reservations held by every continuation already participate in the physical
allocation balance. A direct call transfers that ownership to one saved frame
without changing the heap or the total number of credits. Existing return,
allocation, discard, and edge rules discharge the same balance. Cost and peak
invariants therefore hold for every actual step of either versioned policy.
-/

namespace Ix.Compiler.IxIR2.Eval.Policy

theorem suspendCall_resources {context : Context} {before after : Machine}
    {frame : Frame} {stack : List Continuation} {call : DirectCall}
    (running : before.control = .running frame stack)
    (called : suspendCall context before frame stack call = .ok after) :
    after.store = before.store ∧ after.heapFuel = before.heapFuel ∧
      after.presentCredits = before.presentCredits := by
  obtain ⟨values, definition, _, _, _, _, rfl⟩ := suspendCall_iff.mp called
  refine ⟨rfl, rfl, ?_⟩
  cases before with
  | mk store heapFuel control =>
      simp only at running
      subst control
      simp [Machine.presentCredits_running, Frame.presentCredits,
        Continuation.presentCredits]

theorem Step.allocationAccounting {policy : CreditPolicy} {context : Context}
    {before after : Machine} (stepped : Step policy context .physical before after)
    (accounted : before.AllocationAccounting) : after.AllocationAccounting := by
  rcases stepped.classify with original | ⟨frame, stack, call, _, running, _, called⟩
  · exact original.allocationAccounting accounted
  · obtain ⟨storeEq, _, creditsEq⟩ := suspendCall_resources running called
    simpa only [Machine.AllocationAccounting, storeEq, creditsEq] using accounted

theorem Steps.allocationAccounting {policy : CreditPolicy} {context : Context}
    {count : Nat} {before after : Machine}
    (steps : Steps policy context .physical count before after)
    (accounted : before.AllocationAccounting) : after.AllocationAccounting := by
  induction steps with
  | refl => exact accounted
  | cons running head tail ih => exact ih (head.allocationAccounting accounted)

theorem runMachine_allocationAccounting {policy : CreditPolicy} {context : Context}
    {controlFuel : Nat} {machine : Machine} {result : Result}
    (run : runMachine policy context .physical controlFuel machine = .ok result)
    (accounted : machine.AllocationAccounting) :
    result.store.live + result.store.heap.frees = result.store.heap.allocs := by
  obtain ⟨count, _, steps⟩ := runMachine_steps run
  simpa [Machine.AllocationAccounting, Machine.presentCredits] using
    steps.allocationAccounting accounted

theorem runMain_allocationAccounting {policy : CreditPolicy} {context : Context}
    {program : Program} {controlFuel heapFuel : Nat} {result : Result}
    (arity : program.main.signature.params.size = 0)
    (nonempty : program.main.blocks.isEmpty = false)
    (run : runMain policy context .physical program controlFuel heapFuel = .ok result) :
    result.store.live + result.store.heap.frees = result.store.heap.allocs := by
  rw [runMain_eq_runMachine arity nonempty] at run
  exact runMachine_allocationAccounting run (initialMachine_allocationAccounting ..)

theorem Step.costs {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {before after : Machine}
    (stepped : Step policy context interpretation before after) :
    before.store.heap.rcops ≤ after.store.heap.rcops ∧
      before.store.peakLiveNodes ≤ after.store.peakLiveNodes ∧
      (before.store.live ≤ before.store.peakLiveNodes →
        after.store.live ≤ after.store.peakLiveNodes) := by
  rcases stepped.classify with original | ⟨frame, stack, call, _, running, _, called⟩
  · exact ⟨original.rcops_mono, original.peakLive_mono, original.preservesPeakBound⟩
  · have stores := (suspendCall_resources running called).1
    simp only [stores]
    exact ⟨Nat.le_refl _, Nat.le_refl _, id⟩

theorem Steps.costs {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {count : Nat} {before after : Machine}
    (steps : Steps policy context interpretation count before after) :
    before.store.heap.rcops ≤ after.store.heap.rcops ∧
      before.store.peakLiveNodes ≤ after.store.peakLiveNodes ∧
      (before.store.live ≤ before.store.peakLiveNodes →
        after.store.live ≤ after.store.peakLiveNodes) := by
  induction steps with
  | refl => exact ⟨Nat.le_refl _, Nat.le_refl _, id⟩
  | cons running head tail ih =>
      exact ⟨Nat.le_trans head.costs.1 ih.1,
        Nat.le_trans head.costs.2.1 ih.2.1, ih.2.2 ∘ head.costs.2.2⟩

theorem runMachine_prefix_costs {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {controlFuel prefixCount : Nat}
    {initial middle : Machine} {result : Result}
    (run : runMachine policy context interpretation controlFuel initial = .ok result)
    (prefixSteps : Steps policy context interpretation prefixCount initial middle)
    (initialPeak : initial.store.live ≤ initial.store.peakLiveNodes) :
    middle.store.heap.rcops ≤ result.store.heap.rcops ∧
      middle.store.peakLiveNodes ≤ result.store.peakLiveNodes ∧
      middle.store.live ≤ result.store.peakLiveNodes := by
  obtain ⟨count, _, execution⟩ := runMachine_steps run
  obtain ⟨suffixCount, _, suffix⟩ := prefixSteps.cancelPrefixToHalted execution rfl
  exact ⟨suffix.costs.1, suffix.costs.2.1,
    Nat.le_trans (prefixSteps.costs.2.2 initialPeak) suffix.costs.2.1⟩

end Ix.Compiler.IxIR2.Eval.Policy
