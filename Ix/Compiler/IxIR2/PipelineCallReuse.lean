import Ix.Compiler.IxIR2.PipelineCosts
import Ix.Compiler.IxIR2.CallReuseMain
import Ix.Compiler.IxIR2.CallResources

/-!
# Compiler costs and reclamation with suspended call credits

The common checked lowering trace derives endpoint closure and a live result.
The actual selected execution supplies the unchanged semantic heap relation,
allocation events, RC and peak bounds. Physical accounting and shared release
then give R4's complete resource laws for both policy selection branches.
-/

namespace Ix.Compiler.IxIR2.Pipeline

theorem CompiledAttachment.baselineClosed
    {fuel : Nat} (attached : CompiledAttachment .shared fuel)
    {sourceFuel : Nat} {store : IxIR1.Store} {value : IxIR1.RVal}
    (ownedRun : IxIR1.runOwnedMain attached.simulationSourceContext
      attached.target.artifact.source.mainResult attached.target.artifact.source.main
      sourceFuel = .ok (store, value))
    {baseline : Eval.Result} (related : Lower.Sim.OutcomeRel (store, value) baseline) :
    IxIR1.Sim.StoreClosed baseline.store.heap ∧
      IxIR1.Sim.LiveRVal baseline.store.heap baseline.value := by
  have mainWorld : attached.target.artifact.source.mainResult = .shared := by
    rw [attached.targetSourceProduced, attached.inputProduced]
  have bodyRun := (IxIR1.Sim.runOwnedMain_ok ownedRun).1
  rw [mainWorld] at bodyRun
  have run : IxIR1.runMain attached.simulationSourceContext
      attached.target.artifact.source.main sourceFuel = .ok (store, value) := bodyRun
  rw [attached.simulationSourceContext_eq_addressedCtx,
    attached.targetSourceProduced, attached.inputProduced] at run
  have ownership := attached.source.owned (fun _ _ => none) run
  rw [related.heap, related.value]
  refine ⟨ownership.storeClosed, ?_⟩
  have world := ownership.roots_world ⟨.shared, value⟩ (by simp)
  cases value with
  | loc location => exact ⟨world.choose, world.choose_spec.1⟩
  | lit literal => trivial
  | erased => trivial

def CompiledAttachment.CallPrefixCostBounds
    {fuel : Nat} (attached : CompiledAttachment .shared fuel)
    (selection : CallReuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program)
    (heapFuel : Nat) (baseline : Eval.Result) : Prop :=
  ∀ {count : Nat} {middle : Eval.Machine},
    Eval.Policy.Steps selection.policy
      (Eval.Context.ofProgram selection.target attached.target.artifact.validationContext.schemas)
      .physical count (Eval.initialMachine selection.target.main #[] heapFuel) middle →
    middle.store.heap.rcops ≤ baseline.store.heap.rcops ∧
    middle.store.peakLiveNodes ≤ baseline.store.peakLiveNodes ∧
    middle.store.live ≤ baseline.store.peakLiveNodes

theorem CompiledAttachment.selectedCallPrefixCostBounds
    {fuel : Nat} (attached : CompiledAttachment .shared fuel)
    (selection : CallReuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program)
    {controlFuel heapFuel : Nat} {baseline selected : Eval.Result}
    (selectedRun : Eval.Policy.runMain selection.policy
      (Eval.Context.ofProgram selection.target attached.target.artifact.validationContext.schemas)
      .physical selection.target controlFuel heapFuel = .ok selected)
    (costs : baseline.CostBounds selected) : attached.CallPrefixCostBounds selection heapFuel baseline := by
  have entry := selection.mainEntry attached.target.artifact.mainArity attached.target.artifact.mainNonempty
  rw [Eval.Policy.runMain_eq_runMachine entry.1 entry.2] at selectedRun
  intro count middle prefixSteps
  have observed := Eval.Policy.runMachine_prefix_costs selectedRun prefixSteps (Nat.le_refl 0)
  exact ⟨Nat.le_trans observed.1 costs.rcops,
    Nat.le_trans observed.2.1 costs.peakLive, Nat.le_trans observed.2.2 costs.peakLive⟩

/-- All compiler-state, heap, and cost invariants are reconstructed internally
from successful owned execution and the exact checked selection. -/
theorem CompiledAttachment.selectedCallPhysicalMainCostLaws
    {fuel : Nat} (attached : CompiledAttachment .shared fuel)
    (selection : CallReuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program)
    {sourceFuel : Nat} {sourceOut : IxIR1.Store × IxIR1.RVal}
    (ownedRun : IxIR1.runOwnedMain attached.simulationSourceContext
      attached.target.artifact.source.mainResult attached.target.artifact.source.main
      sourceFuel = .ok sourceOut) :
    ∃ baselineControl selectedControl heapFuel baseline selected locRel,
      Eval.runMain attached.simulationTargetContext .physical
        attached.target.artifact.program baselineControl heapFuel = .ok baseline ∧
      Eval.Policy.runMain selection.policy
        (Eval.Context.ofProgram selection.target attached.target.artifact.validationContext.schemas)
        .physical selection.target selectedControl heapFuel = .ok selected ∧
      Lower.Sim.OutcomeRel sourceOut baseline ∧
      ReuseSim.StableHeapRel baseline.store selected.store locRel ∧
      IxIR1.Sim.RValIso locRel baseline.value selected.value ∧
      baseline.SharedResources ∧ selected.SharedResources ∧
      baseline.AllocationLaws selected ∧ baseline.CostBounds selected ∧
      baseline.ReclaimedCostLaws selected ∧ attached.CallPrefixCostBounds selection heapFuel baseline := by
  obtain ⟨baselineControl, heapFuel, baseline, baselineRun, baselineRelation⟩ :=
    attached.successfulPhysicalMainSimulation ownedRun
  have closure := attached.baselineClosed ownedRun baselineRelation
  obtain ⟨selectedControl, selected, locRel, selectedRun, heaps, values, _budget, events, costs⟩ :=
    selection.mainSimulation attached.target.artifact.mainArity attached.target.artifact.mainNonempty
      baselineRun closure.1 closure.2
  have baselineAccounted := Eval.runMain_allocationAccounting
    attached.target.artifact.mainArity attached.target.artifact.mainNonempty baselineRun
  have entry := selection.mainEntry attached.target.artifact.mainArity attached.target.artifact.mainNonempty
  have selectedAccounted := Eval.Policy.runMain_allocationAccounting entry.1 entry.2 selectedRun
  obtain ⟨releaseFuel, baselineReleased, baselineRelease, baselineEmpty⟩ :=
    attached.baselineSharedReclamation ownedRun baselineRelation
  obtain ⟨selectedReleased, selectedRelease, selectedEmpty⟩ :=
    heaps.sharedReclamation values baselineRelease baselineEmpty
  have baselineResources := Eval.Result.sharedResources_of_release
    baselineAccounted baselineRelease baselineEmpty
  have selectedResources := Eval.Result.sharedResources_of_release
    selectedAccounted selectedRelease selectedEmpty
  have allocations := Eval.Result.AllocationLaws.of_accounting heaps events
    (attached.baselineNoReuses ownedRun baselineRelation) baselineAccounted selectedAccounted
  have reclaimed := allocations.reclaimed heaps values baselineResources selectedResources
  exact ⟨baselineControl, selectedControl, heapFuel, baseline, selected, locRel,
    baselineRun, selectedRun, baselineRelation, heaps, values, baselineResources,
    selectedResources, allocations, costs, costs.reclaimed heaps reclaimed,
    attached.selectedCallPrefixCostBounds selection selectedRun costs⟩

/-- The laws apply to actual successful runs with independent sufficient
control and heap budgets, including every prefix of the selected run. -/
theorem CompiledAttachment.successfulCallPhysicalCostLaws
    {fuel : Nat} (attached : CompiledAttachment .shared fuel)
    (selection : CallReuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program)
    {sourceFuel : Nat} {sourceOut : IxIR1.Store × IxIR1.RVal}
    (ownedRun : IxIR1.runOwnedMain attached.simulationSourceContext
      attached.target.artifact.source.mainResult attached.target.artifact.source.main
      sourceFuel = .ok sourceOut)
    {baselineControl baselineHeap selectedControl selectedHeap : Nat}
    {baseline selected : Eval.Result}
    (baselineRun : Eval.runMain attached.simulationTargetContext .physical
      attached.target.artifact.program baselineControl baselineHeap = .ok baseline)
    (selectedRun : Eval.Policy.runMain selection.policy
      (Eval.Context.ofProgram selection.target attached.target.artifact.validationContext.schemas)
      .physical selection.target selectedControl selectedHeap = .ok selected) :
    selected.SharedResources ∧ baseline.AllocationLaws selected ∧ baseline.CostBounds selected ∧
    baseline.ReclaimedCostLaws selected ∧ attached.CallPrefixCostBounds selection selectedHeap baseline := by
  obtain ⟨witnessBaselineControl, witnessSelectedControl, witnessHeap, witnessBaseline,
    witnessSelected, locRel, witnessBaselineRun, witnessSelectedRun,
    _baselineRelation, _heaps, _values, _baselineResources, resources,
    allocations, costs, reclaimed, _prefixes⟩ := attached.selectedCallPhysicalMainCostLaws selection ownedRun
  obtain ⟨baselineStores, baselineValues⟩ := Eval.runMain_success_unique
    attached.target.artifact.mainArity attached.target.artifact.mainNonempty witnessBaselineRun baselineRun
  have entry := selection.mainEntry attached.target.artifact.mainArity attached.target.artifact.mainNonempty
  obtain ⟨selectedStores, selectedValues⟩ := Eval.Policy.runMain_success_unique
    entry.1 entry.2 witnessSelectedRun selectedRun
  have actualCosts : baseline.CostBounds selected := by
    simpa only [Eval.Result.CostBounds, baselineStores, selectedStores] using costs
  refine ⟨?_, ⟨?_, ?_⟩, actualCosts, ?_,
    attached.selectedCallPrefixCostBounds selection selectedRun actualCosts⟩
  · simpa only [Eval.Result.SharedResources, selectedStores, selectedValues] using resources
  · simpa only [baselineStores, selectedStores] using allocations.allocations
  · simpa only [baselineStores, selectedStores] using allocations.frees
  · simpa only [Eval.Result.ReclaimedCostLaws, baselineStores, baselineValues,
      selectedStores, selectedValues] using reclaimed

def CompiledAttachment.CallCostComparison
    {fuel : Nat} (attached : CompiledAttachment .shared fuel)
    (selection : CallReuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program)
    (selectedHeap : Nat) (selected : Eval.Result) : Prop :=
  ∃ baselineControl baselineHeap baseline,
    Eval.runMain attached.simulationTargetContext .physical attached.target.artifact.program
      baselineControl baselineHeap = .ok baseline ∧
    baseline.SharedResources ∧ baseline.AllocationLaws selected ∧ baseline.CostBounds selected ∧
    baseline.ReclaimedCostLaws selected ∧ attached.CallPrefixCostBounds selection selectedHeap baseline

end Ix.Compiler.IxIR2.Pipeline
