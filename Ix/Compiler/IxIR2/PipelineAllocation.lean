import Ix.Compiler.IxIR2.PipelineResources
import Ix.Compiler.IxIR2.ReuseAllocation

/-!
# Allocation and free laws for the selected shared-main compiler

The owned source execution and checked attachment derive the baseline's zero
reuse count. The actual rewrite execution supplies allocation-event equality;
R2 supplies terminal accounting and shared-result reclamation. No comparative
counter or compiler-state invariant is a caller premise.
-/

namespace Ix.Compiler.IxIR2.Pipeline

/-- The actual owned execution of a compiled shared main performs no baseline
reuse. This is derived from the lowering trace and transported by exact
baseline heap correspondence. -/
theorem CompiledAttachment.baselineNoReuses
    {fuel : Nat} (attached : CompiledAttachment .shared fuel)
    {sourceFuel : Nat} {store : IxIR1.Store} {value : IxIR1.RVal}
    (ownedRun : IxIR1.runOwnedMain attached.simulationSourceContext
      attached.target.artifact.source.mainResult attached.target.artifact.source.main
      sourceFuel = .ok (store, value))
    {baseline : Eval.Result} (related : Lower.Sim.OutcomeRel (store, value) baseline) :
    baseline.store.heap.reuses = 0 := by
  have mainWorld : attached.target.artifact.source.mainResult = .shared := by
    rw [attached.targetSourceProduced, attached.inputProduced]
  have bodyRun := (IxIR1.Sim.runOwnedMain_ok ownedRun).1
  rw [mainWorld] at bodyRun
  have noReuse := attached.functionTraceNoReuse attached.target.artifact.mainTraceMember
  rw [attached.target.artifact.mainSource] at noReuse
  rw [related.heap]
  exact IxIR1.NoReuse.runMain_reuses_eq_zero
    (attached.sourceContextNoReuse rfl) noReuse bodyRun

/-- Both physical executions and their exact allocation/free laws, including
complete reclamation of both shared results. Optimized and checked baseline
selection use the same public theorem. -/
theorem CompiledAttachment.selectedPhysicalMainAllocationLaws
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
      baseline.AllocationLaws selected ∧ baseline.ReclaimedAllocationLaws selected := by
  obtain ⟨baselineControl, heapFuel, baseline, baselineRun, baselineRelation⟩ :=
    attached.successfulPhysicalMainSimulation ownedRun
  obtain ⟨selectedControl, selected, locRel, selectedRun, heaps, values, _budget, events⟩ :=
    ReuseLiveSim.selectedPhysicalMainSimulationWithAllocationEvents selection baselineRun
  have baselineAccounted := Eval.runMain_allocationAccounting
    attached.target.artifact.mainArity attached.target.artifact.mainNonempty baselineRun
  have selectedAccounted := attached.selectedAllocationAccounting selection selectedRun
  obtain ⟨releaseFuel, baselineReleased, baselineRelease, baselineEmpty⟩ :=
    attached.baselineSharedReclamation ownedRun baselineRelation
  obtain ⟨selectedReleased, selectedRelease, selectedEmpty⟩ :=
    heaps.sharedReclamation values baselineRelease baselineEmpty
  have baselineResources := Eval.Result.sharedResources_of_release
    baselineAccounted baselineRelease baselineEmpty
  have selectedResources := Eval.Result.sharedResources_of_release
    selectedAccounted selectedRelease selectedEmpty
  have laws := Eval.Result.AllocationLaws.of_accounting heaps events
    (attached.baselineNoReuses ownedRun baselineRelation) baselineAccounted selectedAccounted
  exact ⟨baselineControl, selectedControl, heapFuel, baseline, selected, locRel,
    baselineRun, selectedRun, baselineRelation, heaps, values,
    baselineResources, selectedResources, laws,
    laws.reclaimed heaps values baselineResources selectedResources⟩

/-- The laws concern any actual successful runs of the baseline and selected
programs, including independent sufficient choices of control and heap fuel. -/
theorem CompiledAttachment.successfulPhysicalAllocationLaws
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
    baseline.AllocationLaws selected ∧ baseline.ReclaimedAllocationLaws selected := by
  obtain ⟨witnessBaselineControl, witnessSelectedControl, witnessHeap, witnessBaseline,
      witnessSelected, locRel, witnessBaselineRun, witnessSelectedRun,
      _baselineRelation, _heaps, _values, _baselineResources, _selectedResources,
      laws, reclaimed⟩ := attached.selectedPhysicalMainAllocationLaws selection ownedRun
  obtain ⟨baselineStores, baselineValues⟩ := Eval.runMain_success_unique
    attached.target.artifact.mainArity attached.target.artifact.mainNonempty
    witnessBaselineRun baselineRun
  obtain ⟨selectedStores, selectedValues⟩ := Eval.runMain_success_unique
    (attached.selectedMainEntry selection).1 (attached.selectedMainEntry selection).2
    witnessSelectedRun selectedRun
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa only [baselineStores, selectedStores] using laws.allocations
  · simpa only [baselineStores, selectedStores] using laws.frees
  · simpa only [Eval.Result.ReclaimedAllocationLaws, baselineStores, baselineValues,
      selectedStores, selectedValues] using reclaimed

/-- A selected result is compared with an actual physical run of the checked
baseline, retaining its resources and both pre- and post-release laws. -/
def CompiledAttachment.AllocationComparison
    {fuel : Nat} (attached : CompiledAttachment .shared fuel) (selected : Eval.Result) : Prop :=
  ∃ baselineControl baselineHeap baseline,
    Eval.runMain attached.simulationTargetContext .physical attached.target.artifact.program
      baselineControl baselineHeap = .ok baseline ∧
    baseline.SharedResources ∧ baseline.AllocationLaws selected ∧
    baseline.ReclaimedAllocationLaws selected

end Ix.Compiler.IxIR2.Pipeline
