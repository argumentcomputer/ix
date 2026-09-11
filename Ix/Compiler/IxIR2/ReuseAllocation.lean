import Ix.Compiler.IxIR2.ReuseCost
import Ix.Compiler.IxIR2.AllocationEvents
import Ix.Compiler.IxIR2.ReuseResources

/-!
# Comparative allocation and free observations

Semantic heap correspondence preserves live-node counts. Combining this fact
with actual execution accounting and the separate allocation-event equation
yields both counter laws at halt.
-/



namespace Ix.Compiler.IxIR2.Eval

/-- Comparative counters at successful physical halt. Each executed reuse
saves one fresh allocation and one terminal free relative to the baseline. -/
structure Result.AllocationLaws (baseline selected : Result) : Prop where
  allocations : baseline.store.heap.allocs =
    selected.store.heap.allocs + selected.store.heap.reuses
  frees : baseline.store.heap.frees =
    selected.store.heap.frees + selected.store.heap.reuses

theorem Result.AllocationLaws.of_accounting {baseline selected : Result}
    {locRel : Nat → Nat → Prop}
    (heaps : ReuseSim.StableHeapRel baseline.store selected.store locRel)
    (events : baseline.store.allocationEvents = selected.store.allocationEvents)
    (noReuse : baseline.store.heap.reuses = 0)
    (baselineAccounted : baseline.store.live + baseline.store.heap.frees = baseline.store.heap.allocs)
    (selectedAccounted : selected.store.live + selected.store.heap.frees = selected.store.heap.allocs) :
    baseline.AllocationLaws selected := by
  have live := heaps.live_eq
  unfold Store.allocationEvents at events
  constructor <;> omega

/-- Both actual shared-result releases, with the same sufficient traversal
budget, retain the comparative free law after the heaps are empty. -/
def Result.ReclaimedAllocationLaws (baseline selected : Result) : Prop :=
  ∃ releaseFuel baselineReleased selectedReleased remaining,
    releaseShared releaseFuel baseline.store baseline.value = .ok (baselineReleased, remaining) ∧
    releaseShared releaseFuel selected.store selected.value = .ok (selectedReleased, remaining) ∧
    baselineReleased.live = 0 ∧ selectedReleased.live = 0 ∧
    baselineReleased.heap.allocs = baselineReleased.heap.frees ∧
    selectedReleased.heap.allocs = selectedReleased.heap.frees ∧
    baselineReleased.heap.frees = selectedReleased.heap.frees + selectedReleased.heap.reuses

theorem Result.AllocationLaws.reclaimed {baseline selected : Result}
    {locRel : Nat → Nat → Prop}
    (laws : baseline.AllocationLaws selected)
    (heaps : ReuseSim.StableHeapRel baseline.store selected.store locRel)
    (values : IxIR1.Sim.RValIso locRel baseline.value selected.value)
    (baselineResources : baseline.SharedResources)
    (selectedResources : selected.SharedResources) :
    baseline.ReclaimedAllocationLaws selected := by
  obtain ⟨releaseFuel, baselineReleased, remaining, baselineRelease, baselineEmpty,
      baselineBalance⟩ := baselineResources.2
  obtain ⟨selectedReleased, selectedRelease, selectedEmpty⟩ :=
    heaps.sharedReclamation values baselineRelease baselineEmpty
  have selectedHeapBalance := releaseShared_heapBalance selectedRelease
  have selectedBalance : selectedReleased.heap.allocs = selectedReleased.heap.frees := by
    have accounted := selectedResources.1
    unfold HeapBalance at selectedHeapBalance
    omega
  have baselineCounters := releaseShared_allocationCounters baselineRelease
  have selectedCounters := releaseShared_allocationCounters selectedRelease
  refine ⟨releaseFuel, baselineReleased, selectedReleased, remaining,
    baselineRelease, selectedRelease, baselineEmpty, selectedEmpty,
    baselineBalance, selectedBalance, ?_⟩
  have allocations := laws.allocations
  omega

end Ix.Compiler.IxIR2.Eval
