import Ix.Compiler.UniqueReuse.TargetMain
import Ix.Compiler.IxIR2.ReservationSteps
import Ix.Compiler.IxIR2.Resources
import Ix.Compiler.IxIR2.CostSteps

namespace Ix.Compiler.UniqueReuse.Target

open Ix.Compiler.IxIR0.UniqueReverse (Plan)
open Ix.Compiler.IxIR2
open Ix.Compiler.IxIR2.Eval

private theorem stepsV0 {ctx : Context} {mode : Interpretation} {count : Nat} {before after : Machine}
    (steps : Steps ctx mode count before after) : Policy.Steps .callLocalV0 ctx mode count before after := by
  induction steps with
  | refl => exact .refl _
  | cons running head tail ih => exact .cons running head ih

/-- Every actual physical prefix has exactly owned, non-live reservations,
balanced allocation accounting, no RC work, and the final peak bound. -/
theorem prefixResources (plan : Plan) (reuse : Bool) {heapFuel count : Nat} {middle : Machine}
    (prefixSteps : Steps (context plan reuse) .physical count
      (initialMachine (UniqueLower.program plan reuse).main #[] heapFuel) middle) :
    middle.ReservationOwnership ∧ middle.AllocationAccounting ∧
      middle.store.heap.rcops = 0 ∧ middle.store.live ≤ middle.store.peakLiveNodes ∧
      middle.store.peakLiveNodes ≤ plan.values.length + 2 ∧ count ≤ controlCost plan reuse := by
  obtain ⟨store, value, execution, result⟩ := mainSteps plan reuse .physical heapFuel
  obtain ⟨suffixCount, countEq, suffix⟩ := prefixSteps.cancelPrefixToHalted execution rfl
  have costs := suffix.costs_mono
  have initialPeak : (initialMachine (UniqueLower.program plan reuse).main #[] heapFuel).store.live ≤
      (initialMachine (UniqueLower.program plan reuse).main #[] heapFuel).store.peakLiveNodes := by
    rw [initialMachine_store_empty]; exact Nat.le_refl _
  exact ⟨Policy.runMain_prefix_reservationOwnership (stepsV0 prefixSteps),
    prefixSteps.allocationAccounting (initialMachine_allocationAccounting ..),
    Nat.eq_zero_of_le_zero (by simpa only [result.rcops] using costs.1),
    prefixSteps.preservesPeakBound initialPeak, by simpa only [result.peak] using costs.2, by omega⟩

structure CostLaws (plan : Plan) (baseline selected : Store) (reuse : Bool) : Prop where
  allocations : selected.heap.allocs + (if reuse then plan.values.length else 0) = baseline.heap.allocs
  frees : selected.heap.frees + (if reuse then plan.values.length else 0) = baseline.heap.frees
  reuses : selected.heap.reuses = if reuse then plan.values.length else 0
  payload : selected.reusedPayloadUnits = if reuse then 2 * plan.values.length else 0
  noRC : baseline.heap.rcops = 0 ∧ selected.heap.rcops = 0
  peak : selected.peakLiveNodes = baseline.peakLiveNodes
  live : selected.live = baseline.live

theorem costLaws {plan : Plan} {reuse : Bool} {baseline selected : Store} {baselineValue selectedValue : RVal}
    (base : MainResult plan false .physical baseline baselineValue)
    (result : MainResult plan reuse .physical selected selectedValue) : CostLaws plan baseline selected reuse := by
  refine ⟨?_, ?_, ?_, ?_, ⟨base.rcops, result.rcops⟩, result.peak.trans base.peak.symm,
    result.live.trans base.live.symm⟩
  · rw [base.allocs, result.allocs]
    cases reuse <;> simp [freshPerCons, inPlace] <;> omega
  · rw [base.frees, result.frees]
    cases reuse <;> simp [freshPerCons, inPlace] <;> omega
  · rw [result.reuses]
    cases reuse <;> simp [reusesPerCons, inPlace]
  · rw [result.payload]
    cases reuse <;> simp [reusesPerCons, inPlace]

end Ix.Compiler.UniqueReuse.Target
