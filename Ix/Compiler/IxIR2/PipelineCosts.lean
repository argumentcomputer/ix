import Ix.Compiler.IxIR2.PipelineAllocation

/-!
# Comparative costs for the actual selected shared-main compiler

RC and peak bounds cover both selection branches and independent sufficient
execution budgets. All intermediate selected states are bounded by the actual
baseline's final counters. Shared reclamation retains the same cost bounds and
R3's allocation/free laws.
-/

namespace Ix.Compiler.IxIR2.Eval

theorem Result.ReclaimedCostLaws.allocations {baseline selected : Result}
    (laws : baseline.ReclaimedCostLaws selected) : baseline.ReclaimedAllocationLaws selected := by
  obtain ⟨fuel, baselineReleased, selectedReleased, remaining, baselineRun, selectedRun,
    baselineEmpty, selectedEmpty, baselineBalance, selectedBalance, frees, _costs⟩ := laws
  exact ⟨fuel, baselineReleased, selectedReleased, remaining, baselineRun, selectedRun,
    baselineEmpty, selectedEmpty, baselineBalance, selectedBalance, frees⟩

/-- Extend the exact R3 reclamation witnesses with RC and peak bounds. -/
theorem Result.CostBounds.reclaimed {baseline selected : Result} {locRel : Nat → Nat → Prop}
    (costs : baseline.CostBounds selected)
    (heaps : ReuseSim.StableHeapRel baseline.store selected.store locRel)
    (allocations : baseline.ReclaimedAllocationLaws selected) :
    baseline.ReclaimedCostLaws selected := by
  obtain ⟨fuel, baselineReleased, selectedReleased, remaining, baselineRun, selectedRun,
    baselineEmpty, selectedEmpty, baselineBalance, selectedBalance, frees⟩ := allocations
  exact ⟨fuel, baselineReleased, selectedReleased, remaining, baselineRun, selectedRun,
    baselineEmpty, selectedEmpty, baselineBalance, selectedBalance, frees,
    costs.releaseShared heaps baselineRun selectedRun baselineEmpty selectedEmpty⟩

end Ix.Compiler.IxIR2.Eval

namespace Ix.Compiler.IxIR2.Pipeline

/-- The RC and peak bounds concern any two actual successful physical runs,
with independent choices of sufficient control and heap fuel. -/
theorem CompiledAttachment.successfulPhysicalCostBounds
    {world : Ixon.Owned} {fuel : Nat} (attached : CompiledAttachment world fuel)
    (selection : Reuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program)
    {baselineControl baselineHeap selectedControl selectedHeap : Nat}
    {baseline selected : Eval.Result}
    (baselineRun : Eval.runMain attached.simulationTargetContext .physical
      attached.target.artifact.program baselineControl baselineHeap = .ok baseline)
    (selectedRun : Eval.runMain
      (Eval.Context.ofProgram selection.target attached.target.artifact.validationContext.schemas)
      .physical selection.target selectedControl selectedHeap = .ok selected) :
    baseline.CostBounds selected := by
  obtain ⟨control, result, locRel, run, _heaps, _values, _fuel, _events, costs⟩ :=
    ReuseLiveSim.selectedPhysicalMainSimulationWithCosts selection baselineRun
  obtain ⟨stores, _values⟩ := Eval.runMain_success_unique
    (attached.selectedMainEntry selection).1 (attached.selectedMainEntry selection).2 run selectedRun
  simpa only [Eval.Result.CostBounds, stores] using costs

/-- Every actual selected prefix, including all internal macro states, fits
within the physical baseline's terminal RC count and peak-live count. -/
def CompiledAttachment.PrefixCostBounds
    {world : Ixon.Owned} {fuel : Nat} (attached : CompiledAttachment world fuel)
    (selection : Reuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program)
    (heapFuel : Nat) (baseline : Eval.Result) : Prop :=
  ∀ {count : Nat} {middle : Eval.Machine},
    Eval.Steps (Eval.Context.ofProgram selection.target attached.target.artifact.validationContext.schemas)
      .physical count (Eval.initialMachine selection.target.main #[] heapFuel) middle →
    middle.store.heap.rcops ≤ baseline.store.heap.rcops ∧
    middle.store.peakLiveNodes ≤ baseline.store.peakLiveNodes ∧
    middle.store.live ≤ baseline.store.peakLiveNodes

theorem CompiledAttachment.selectedPrefixCostBounds
    {world : Ixon.Owned} {fuel : Nat} (attached : CompiledAttachment world fuel)
    (selection : Reuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program)
    {controlFuel heapFuel : Nat} {baseline selected : Eval.Result}
    (selectedRun : Eval.runMain
      (Eval.Context.ofProgram selection.target attached.target.artifact.validationContext.schemas)
      .physical selection.target controlFuel heapFuel = .ok selected)
    (costs : baseline.CostBounds selected) : attached.PrefixCostBounds selection heapFuel baseline := by
  rw [Eval.runMain_eq_runMachine (attached.selectedMainEntry selection).1
    (attached.selectedMainEntry selection).2] at selectedRun
  intro count middle prefixSteps
  have observed := Eval.runMachine_prefix_costs selectedRun prefixSteps (Nat.le_refl 0)
  exact ⟨Nat.le_trans observed.1 costs.rcops,
    Nat.le_trans observed.2.1 costs.peakLive, Nat.le_trans observed.2.2 costs.peakLive⟩

/-- Owned execution derives the same semantic and resource endpoints as R3,
and the compiler trace supplies RC and peak bounds without new caller premises. -/
theorem CompiledAttachment.selectedPhysicalMainCostLaws
    {fuel : Nat} (attached : CompiledAttachment .shared fuel)
    (selection : Reuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program)
    {sourceFuel : Nat} {sourceOut : IxIR1.Store × IxIR1.RVal}
    (ownedRun : IxIR1.runOwnedMain attached.simulationSourceContext
      attached.target.artifact.source.mainResult attached.target.artifact.source.main
      sourceFuel = .ok sourceOut) :
    ∃ baselineControl selectedControl heapFuel baseline selected locRel,
      Eval.runMain attached.simulationTargetContext .physical
        attached.target.artifact.program baselineControl heapFuel = .ok baseline ∧
      Eval.runMain
        (Eval.Context.ofProgram selection.target attached.target.artifact.validationContext.schemas)
        .physical selection.target selectedControl heapFuel = .ok selected ∧
      Lower.Sim.OutcomeRel sourceOut baseline ∧
      ReuseSim.StableHeapRel baseline.store selected.store locRel ∧
      IxIR1.Sim.RValIso locRel baseline.value selected.value ∧
      baseline.SharedResources ∧ selected.SharedResources ∧
      baseline.AllocationLaws selected ∧ baseline.CostBounds selected ∧
      baseline.ReclaimedCostLaws selected ∧ attached.PrefixCostBounds selection heapFuel baseline := by
  obtain ⟨baselineControl, selectedControl, heapFuel, baseline, selected, locRel,
    baselineRun, selectedRun, baselineRelation, heaps, values, baselineResources,
    selectedResources, allocations, reclaimed⟩ := attached.selectedPhysicalMainAllocationLaws selection ownedRun
  have costs := attached.successfulPhysicalCostBounds selection baselineRun selectedRun
  exact ⟨baselineControl, selectedControl, heapFuel, baseline, selected, locRel,
    baselineRun, selectedRun, baselineRelation, heaps, values, baselineResources,
    selectedResources, allocations, costs, costs.reclaimed heaps reclaimed,
    attached.selectedPrefixCostBounds selection selectedRun costs⟩

/-- Full counter and reclamation laws for arbitrary actual successful runs;
the prefix bound uses the selected run's own traversal budget. -/
theorem CompiledAttachment.successfulPhysicalCostLaws
    {fuel : Nat} (attached : CompiledAttachment .shared fuel)
    (selection : Reuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program)
    {sourceFuel : Nat} {sourceOut : IxIR1.Store × IxIR1.RVal}
    (ownedRun : IxIR1.runOwnedMain attached.simulationSourceContext
      attached.target.artifact.source.mainResult attached.target.artifact.source.main
      sourceFuel = .ok sourceOut)
    {baselineControl baselineHeap selectedControl selectedHeap : Nat}
    {baseline selected : Eval.Result}
    (baselineRun : Eval.runMain attached.simulationTargetContext .physical
      attached.target.artifact.program baselineControl baselineHeap = .ok baseline)
    (selectedRun : Eval.runMain
      (Eval.Context.ofProgram selection.target attached.target.artifact.validationContext.schemas)
      .physical selection.target selectedControl selectedHeap = .ok selected) :
    baseline.AllocationLaws selected ∧ baseline.CostBounds selected ∧
    baseline.ReclaimedCostLaws selected ∧ attached.PrefixCostBounds selection selectedHeap baseline := by
  obtain ⟨witnessBaselineControl, witnessSelectedControl, witnessHeap, witnessBaseline,
    witnessSelected, locRel, witnessBaselineRun, witnessSelectedRun,
    _baselineRelation, _heaps, _values, _baselineResources, _selectedResources,
    allocations, costs, reclaimed, _prefixes⟩ := attached.selectedPhysicalMainCostLaws selection ownedRun
  obtain ⟨baselineStores, baselineValues⟩ := Eval.runMain_success_unique
    attached.target.artifact.mainArity attached.target.artifact.mainNonempty witnessBaselineRun baselineRun
  obtain ⟨selectedStores, selectedValues⟩ := Eval.runMain_success_unique
    (attached.selectedMainEntry selection).1 (attached.selectedMainEntry selection).2
    witnessSelectedRun selectedRun
  have actualCosts : baseline.CostBounds selected := by
    simpa only [Eval.Result.CostBounds, baselineStores, selectedStores] using costs
  refine ⟨⟨?_, ?_⟩, actualCosts, ?_, attached.selectedPrefixCostBounds selection selectedRun actualCosts⟩
  · simpa only [baselineStores, selectedStores] using allocations.allocations
  · simpa only [baselineStores, selectedStores] using allocations.frees
  · simpa only [Eval.Result.ReclaimedCostLaws, baselineStores, baselineValues,
      selectedStores, selectedValues] using reclaimed

/-- Compare the selected result and every prefix of its execution with one
actual checked baseline, preserving both R2 resources and R3's counter laws. -/
def CompiledAttachment.CostComparison
    {fuel : Nat} (attached : CompiledAttachment .shared fuel)
    (selection : Reuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program)
    (selectedHeap : Nat) (selected : Eval.Result) : Prop :=
  ∃ baselineControl baselineHeap baseline,
    Eval.runMain attached.simulationTargetContext .physical attached.target.artifact.program
      baselineControl baselineHeap = .ok baseline ∧
    baseline.SharedResources ∧ baseline.AllocationLaws selected ∧ baseline.CostBounds selected ∧
    baseline.ReclaimedCostLaws selected ∧ attached.PrefixCostBounds selection selectedHeap baseline

theorem CompiledAttachment.CostComparison.allocations
    {fuel : Nat} {attached : CompiledAttachment .shared fuel}
    {selection : Reuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program}
    {heapFuel : Nat} {selected : Eval.Result}
    (comparison : attached.CostComparison selection heapFuel selected) :
    attached.AllocationComparison selected := by
  obtain ⟨control, heap, baseline, run, resources, allocations, _costs, reclaimed, _prefixes⟩ := comparison
  exact ⟨control, heap, baseline, run, resources, allocations, reclaimed.allocations⟩

end Ix.Compiler.IxIR2.Pipeline
