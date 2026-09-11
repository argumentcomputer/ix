import Ix.Compiler.IxIR2.PipelinePhysical
import Ix.Compiler.IxIR2.ReuseLiveSim
import Ix.Compiler.IxIR2.ReuseResources
import Ix.Compiler.IxIR2.EvalFuel

/-!
# Terminal resources for the selected compiler output

The common checked shared-main attachment supplies reclamation for its owned
IxIR₁ execution. Exact baseline lowering and the existing selected semantic
relation transport the release; actual physical execution supplies allocation
accounting independently of that relation.
-/

namespace Ix.Compiler.IxIR2.Pipeline

open Ix.Compiler.Ixon (Owned)

theorem CompiledAttachment.selectedMainEntry
    {world : Owned} {fuel : Nat} (attached : CompiledAttachment world fuel)
    (selection : Reuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program) :
    selection.target.main.signature.params.size = 0 ∧
      selection.target.main.blocks.isEmpty = false := by
  cases selection with
  | optimized output produced =>
      change output.target.main.signature.params.size = 0 ∧
        output.target.main.blocks.isEmpty = false
      rw [← output.trace_target]
      exact ⟨by rw [output.trace.target_main_signature]; exact attached.target.artifact.mainArity,
        output.trace.main.definition_blocks_nonempty attached.target.artifact.mainNonempty⟩
  | baseline error rejected =>
      exact ⟨attached.target.artifact.mainArity, attached.target.artifact.mainNonempty⟩

/-- Successful owned execution of the exact shared compiler input supplies a
release for any exactly related baseline result. No heap premise is supplied. -/
theorem CompiledAttachment.baselineSharedReclamation
    {fuel : Nat} (attached : CompiledAttachment .shared fuel)
    {sourceFuel : Nat} {store : IxIR1.Store} {value : IxIR1.RVal}
    (ownedRun : IxIR1.runOwnedMain attached.simulationSourceContext
      attached.target.artifact.source.mainResult attached.target.artifact.source.main
      sourceFuel = .ok (store, value))
    {baseline : Eval.Result} (related : Lower.Sim.OutcomeRel (store, value) baseline) :
    ∃ releaseFuel released,
      Eval.releaseShared releaseFuel baseline.store baseline.value = .ok (released, 0) ∧
      released.live = 0 := by
  have mainWorld : attached.target.artifact.source.mainResult = .shared := by
    rw [attached.targetSourceProduced, attached.inputProduced]
  have bodyRun := (IxIR1.Sim.runOwnedMain_ok ownedRun).1
  rw [mainWorld] at bodyRun
  have run : IxIR1.runMain attached.simulationSourceContext
      attached.target.artifact.source.main sourceFuel = .ok (store, value) := bodyRun
  have noReuse := attached.functionTraceNoReuse attached.target.artifact.mainTraceMember
  rw [attached.target.artifact.mainSource] at noReuse
  have reuses := IxIR1.NoReuse.runMain_reuses_eq_zero
    (attached.sourceContextNoReuse rfl) noReuse run
  have order := (IxIR1.Reclamation.runMain_order_of_reuses_eq_zero run reuses).1
  have positive : Lower.Sim.PositiveSharedRC store := by
    intro location box found shared
    exact order.rc_pos found
  have addressedRun : IxIR1.runMain
      (attached.source.lowering.result.addressedCtx (fun _ _ => none))
      attached.source.lowering.result.main sourceFuel = .ok (store, value) := by
    rw [attached.simulationSourceContext_eq_addressedCtx, attached.targetSourceProduced,
      attached.inputProduced] at run
    exact run
  obtain ⟨sourceReleaseFuel, sourceReleased, sourceRelease, sourceEmpty⟩ :=
    attached.source.reclamation (fun _ _ => none) addressedRun
  obtain ⟨releaseFuel, released, release, stores, positiveOut⟩ :=
    Lower.Sim.dropVal_simulates_releaseSharedWork positive related.toStoreRel sourceRelease
  refine ⟨releaseFuel, released, ?_, ?_⟩
  · rw [related.value]
    exact release
  · change released.heap.live = 0
    rw [stores.heap]
    exact sourceEmpty

/-- Every actual successful physical main of the selected program accounts
for all allocations, including checked fallback to the baseline. -/
theorem CompiledAttachment.selectedAllocationAccounting
    {world : Owned} {fuel : Nat} (attached : CompiledAttachment world fuel)
    (selection : Reuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program)
    {context : Eval.Context} {controlFuel heapFuel : Nat} {result : Eval.Result}
    (run : Eval.runMain context .physical selection.target controlFuel heapFuel = .ok result) :
    result.store.live + result.store.heap.frees = result.store.heap.allocs :=
  Eval.runMain_allocationAccounting (attached.selectedMainEntry selection).1
    (attached.selectedMainEntry selection).2 run

/-- The existing baseline simulation plus selected reuse preserves semantics
and derives terminal resources for the same actual selected execution. -/
theorem CompiledAttachment.selectedPhysicalMainResources
    {fuel : Nat} (attached : CompiledAttachment .shared fuel)
    (selection : Reuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program)
    {sourceFuel : Nat} {sourceOut : IxIR1.Store × IxIR1.RVal}
    (ownedRun : IxIR1.runOwnedMain attached.simulationSourceContext
      attached.target.artifact.source.mainResult attached.target.artifact.source.main
      sourceFuel = .ok sourceOut) :
    ∃ controlFuel heapFuel result baseline locRel,
      Eval.runMain
        (Eval.Context.ofProgram selection.target attached.target.artifact.validationContext.schemas)
        .physical selection.target controlFuel heapFuel = .ok result ∧
      Lower.Sim.OutcomeRel sourceOut baseline ∧
      ReuseSim.StableHeapRel baseline.store result.store locRel ∧
      IxIR1.Sim.RValIso locRel baseline.value result.value ∧
      result.SharedResources := by
  obtain ⟨baselineControl, heapFuel, baseline, baselineRun, baselineRelation⟩ :=
    attached.successfulPhysicalMainSimulation ownedRun
  obtain ⟨releaseFuel, released, release, empty⟩ :=
    attached.baselineSharedReclamation ownedRun baselineRelation
  obtain ⟨controlFuel, result, locRel, run, heaps, values, budget⟩ :=
    ReuseLiveSim.selectedPhysicalMainSimulation selection baselineRun
  obtain ⟨output, outputRelease, outputEmpty⟩ := heaps.sharedReclamation values release empty
  exact ⟨controlFuel, heapFuel, result, baseline, locRel, run, baselineRelation, heaps, values,
    Eval.Result.sharedResources_of_release
      (attached.selectedAllocationAccounting selection run) outputRelease outputEmpty⟩

/-- The resource guarantee applies to any successful execution of the actual
selection, including a different sufficient choice of control and heap fuel. -/
theorem CompiledAttachment.selectedSuccessfulSharedResources
    {fuel : Nat} (attached : CompiledAttachment .shared fuel)
    (selection : Reuse.Selection Validate.defaultLimits
      attached.target.artifact.validationContext attached.target.artifact.program)
    {sourceFuel : Nat} {sourceOut : IxIR1.Store × IxIR1.RVal}
    (ownedRun : IxIR1.runOwnedMain attached.simulationSourceContext
      attached.target.artifact.source.mainResult attached.target.artifact.source.main
      sourceFuel = .ok sourceOut)
    {controlFuel heapFuel : Nat} {result : Eval.Result}
    (run : Eval.runMain
      (Eval.Context.ofProgram selection.target attached.target.artifact.validationContext.schemas)
      .physical selection.target controlFuel heapFuel = .ok result) : result.SharedResources := by
  obtain ⟨witnessControl, witnessHeap, witness, baseline, locRel, witnessRun,
      baselineRelation, heaps, values, resources⟩ :=
    attached.selectedPhysicalMainResources selection ownedRun
  obtain ⟨stores, values⟩ := Eval.runMain_success_unique
    (attached.selectedMainEntry selection).1 (attached.selectedMainEntry selection).2 witnessRun run
  simpa only [Eval.Result.SharedResources, stores, values] using resources

end Ix.Compiler.IxIR2.Pipeline
